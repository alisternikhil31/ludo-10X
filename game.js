'use strict';

/**
 * game.js: Decagon Ludo client (Phaser 3).
 * Board renderer + tile coordinate lookup + UI state machine + networking.
 *
 * Per-player tile index map (matches server position semantics):
 *   -1        : home yard (use slotIndex 0..3 for the 4 tokens)
 *    0..1     : entry runway (leads from the yard onto the ring)
 *    2..51    : outer border path (50 shared ring tiles, full clockwise lap)
 *   52..57    : private Home Stretch lane (6 tiles, radial, into the hub)
 *   58        : finish hub  (server MAX_POSITION = 58)
 */
(function (root) {
  // -------------------------------------------------------------------------
  // Constants
  // -------------------------------------------------------------------------
  const CANVAS_SIZE = 800;
  const CX = 400;
  const CY = 400;

  const PLAYERS = 10;
  const SECTOR_RAD = (2 * Math.PI) / PLAYERS; // 36 degrees
  const START_ANGLE = -Math.PI / 2; // player 0's sector is centered at the top

  const R_OUT = 385; // outer decagon vertex radius
  const R_RING = 352; // ring decagon vertex radius (outer border path)
  const R_HUB = 92; // finish hub decagon radius

  const RING_PER_SECTOR = 5; // odd, so the middle cell sits on the sector axis
  const RING_TOTAL = PLAYERS * RING_PER_SECTOR; // 50
  const GATE_K = 2; // middle ring cell: last ring tile before the Home Stretch
  const START_K = 3; // cell right after the gate: where tokens enter the lap

  const RUNWAY_LEN = 2;
  const RUNWAY_STEP = 26;
  const HOME_STRETCH_LEN = 6;
  const HS_OUTER_R = 296;
  const HS_INNER_R = 130;
  const HS_STEP = (HS_OUTER_R - HS_INNER_R) / (HOME_STRETCH_LEN - 1);
  const FINISH_R = 50; // each player's finish spot sits on their own ray

  const YARD_R = 232;
  const YARD_ANGLE_OFFSET = 0.19; // rad; yard sits on the start-tile side
  const YARD_SLOT_SPACING = 22;
  const TOKEN_RADIUS = 10;

  const TILE = Object.freeze({
    YARD: -1,
    RUNWAY_START: 0,
    RING_START: RUNWAY_LEN,
    HOME_STRETCH_START: RUNWAY_LEN + RING_TOTAL,
    FINISH: RUNWAY_LEN + RING_TOTAL + HOME_STRETCH_LEN,
  });

  const PLAYER_COLORS = [
    0xe74c3c, 0xe67e22, 0xf1c40f, 0xa3d900, 0x27ae60,
    0x1abc9c, 0x3498db, 0x5b5fe0, 0x9b59b6, 0xff6fb5,
  ];

  const DEBUG_LABELS = false; // true: print tile indices for player 0

  // -------------------------------------------------------------------------
  // Polar helpers: x = cx + r*cos(a), y = cy + r*sin(a)
  // -------------------------------------------------------------------------
  const polar = (r, a) => ({ x: CX + r * Math.cos(a), y: CY + r * Math.sin(a) });
  const sectorAngle = (p) => START_ANGLE + p * SECTOR_RAD;

  // -------------------------------------------------------------------------
  // Precomputed coordinate tables
  // -------------------------------------------------------------------------
  const ringCells = []; // global ring index g = sector * RING_PER_SECTOR + k (clockwise)
  for (let s = 0; s < PLAYERS; s++) {
    const a0 = sectorAngle(s) - SECTOR_RAD / 2;
    const a1 = sectorAngle(s) + SECTOR_RAD / 2;
    const v0 = polar(R_RING, a0);
    const v1 = polar(R_RING, a1);
    for (let k = 0; k < RING_PER_SECTOR; k++) {
      const t = (k + 0.5) / RING_PER_SECTOR;
      const x = v0.x + (v1.x - v0.x) * t;
      const y = v0.y + (v1.y - v0.y) * t;
      ringCells.push({
        x, y, sector: s, k,
        r: Math.hypot(x - CX, y - CY),
        angle: Math.atan2(y - CY, x - CX),
      });
    }
  }

  const tileTable = []; // tileTable[player][tileIndex 0..FINISH]
  const yardSlots = []; // yardSlots[player][slot 0..3]
  const yardCenters = [];

  for (let p = 0; p < PLAYERS; p++) {
    const theta = sectorAngle(p);
    const table = [];

    // Entry runway: radial, along the start tile's ray, innermost cell first
    const startCell = ringCells[(p * RING_PER_SECTOR + START_K) % RING_TOTAL];
    for (let j = 0; j < RUNWAY_LEN; j++) {
      table.push(polar(startCell.r - (RUNWAY_LEN - j) * RUNWAY_STEP, startCell.angle));
    }

    // Outer border path: full clockwise lap, start tile -> gate tile
    for (let s = 0; s < RING_TOTAL; s++) {
      const c = ringCells[(p * RING_PER_SECTOR + START_K + s) % RING_TOTAL];
      table.push({ x: c.x, y: c.y });
    }

    // Private Home Stretch lane along the sector axis, feeding the hub
    for (let j = 0; j < HOME_STRETCH_LEN; j++) {
      table.push(polar(HS_OUTER_R - j * HS_STEP, theta));
    }

    // Finish spot inside the shared hub
    table.push(polar(FINISH_R, theta));
    tileTable.push(table);

    // Home yard: 2x2 grid in the wedge's start-side half
    const yc = polar(YARD_R, theta + YARD_ANGLE_OFFSET);
    yardCenters.push(yc);
    const u = { x: Math.cos(theta), y: Math.sin(theta) }; // radial
    const v = { x: -Math.sin(theta), y: Math.cos(theta) }; // tangential
    const h = YARD_SLOT_SPACING / 2;
    yardSlots.push(
      [[-h, -h], [-h, h], [h, -h], [h, h]].map(([dr, dt]) => ({
        x: yc.x + u.x * dr + v.x * dt,
        y: yc.y + u.y * dr + v.y * dt,
      }))
    );
  }

  // -------------------------------------------------------------------------
  // Public lookup API
  // -------------------------------------------------------------------------
  /**
   * Absolute canvas pixels for a player's tile.
   * tileIndex -1 = yard (slotIndex picks 0..3), 0..TILE.FINISH = path tiles.
   */
  function getTileCoordinates(playerIndex, tileIndex, slotIndex = 0) {
    if (!Number.isInteger(playerIndex) || playerIndex < 0 || playerIndex >= PLAYERS) {
      throw new RangeError(`playerIndex out of range: ${playerIndex}`);
    }
    if (tileIndex === TILE.YARD) {
      if (!Number.isInteger(slotIndex) || slotIndex < 0 || slotIndex > 3) {
        throw new RangeError(`slotIndex out of range: ${slotIndex}`);
      }
      const s = yardSlots[playerIndex][slotIndex];
      return { x: s.x, y: s.y };
    }
    if (!Number.isInteger(tileIndex) || tileIndex < 0 || tileIndex > TILE.FINISH) {
      throw new RangeError(`tileIndex out of range: ${tileIndex}`);
    }
    const t = tileTable[playerIndex][tileIndex];
    return { x: t.x, y: t.y };
  }

  /** Shared ring cell id (0..49) for a player's tile, or null if not on the ring. */
  function getGlobalRingIndex(playerIndex, tileIndex) {
    if (tileIndex < TILE.RING_START || tileIndex >= TILE.HOME_STRETCH_START) return null;
    return (playerIndex * RING_PER_SECTOR + START_K + (tileIndex - TILE.RING_START)) % RING_TOTAL;
  }

  /** 'yard' | 'runway' | 'ring' | 'homeStretch' | 'finish' */
  function getTileKind(tileIndex) {
    if (tileIndex === TILE.YARD) return 'yard';
    if (tileIndex < TILE.RING_START) return 'runway';
    if (tileIndex < TILE.HOME_STRETCH_START) return 'ring';
    if (tileIndex < TILE.FINISH) return 'homeStretch';
    return 'finish';
  }

  // -------------------------------------------------------------------------
  // Drawing
  // -------------------------------------------------------------------------
  function rectPoints(cx, cy, halfR, halfT, angle) {
    const ux = Math.cos(angle), uy = Math.sin(angle);
    const vx = -uy, vy = ux;
    return [[-1, -1], [1, -1], [1, 1], [-1, 1]].map(([a, b]) => ({
      x: cx + ux * halfR * a + vx * halfT * b,
      y: cy + uy * halfR * a + vy * halfT * b,
    }));
  }

  function decagon(radius) {
    const pts = [];
    for (let i = 0; i < PLAYERS; i++) {
      pts.push(polar(radius, sectorAngle(i) - SECTOR_RAD / 2));
    }
    return pts;
  }

  function drawBoard(scene) {
    const g = scene.add.graphics();
    const label = (x, y, text, size = 13, color = '#ffffff') =>
      scene.add
        .text(x, y, text, { fontFamily: 'Arial, sans-serif', fontSize: `${size}px`, color })
        .setOrigin(0.5);

    // Sector wedges (36 degrees each) from the hub out to the outer decagon
    for (let p = 0; p < PLAYERS; p++) {
      const a0 = sectorAngle(p) - SECTOR_RAD / 2;
      const a1 = sectorAngle(p) + SECTOR_RAD / 2;
      g.fillStyle(PLAYER_COLORS[p], p % 2 ? 0.1 : 0.16);
      g.fillPoints([{ x: CX, y: CY }, polar(R_OUT, a0), polar(R_OUT, a1)], true);
      g.lineStyle(1, 0xffffff, 0.12);
      g.lineBetween(CX, CY, polar(R_OUT, a0).x, polar(R_OUT, a0).y);
    }

    // Outer decagon border
    g.lineStyle(4, 0xdfe6ee, 0.9);
    g.strokePoints(decagon(R_OUT), true);

    // Ring decagon guide line
    g.lineStyle(2, 0xffffff, 0.12);
    g.strokePoints(decagon(R_RING), true);

    // Outer border path tiles (shared ring)
    ringCells.forEach((c, gIdx) => {
      const sector = c.sector;
      const pts = rectPoints(c.x, c.y, 13, 18, sectorAngle(sector));
      const isStart = c.k === START_K;
      const isGate = c.k === GATE_K;
      g.fillStyle(isStart ? PLAYER_COLORS[sector] : 0xf4f6f8, isStart ? 0.95 : 0.92);
      g.fillPoints(pts, true);
      g.lineStyle(isGate ? 3 : 1, isGate ? PLAYER_COLORS[sector] : 0x1b1f27, 1);
      g.strokePoints(pts, true);
      if (DEBUG_LABELS) label(c.x, c.y, String(gIdx), 10, '#000000');
    });

    for (let p = 0; p < PLAYERS; p++) {
      const color = PLAYER_COLORS[p];
      const theta = sectorAngle(p);
      const startCell = ringCells[(p * RING_PER_SECTOR + START_K) % RING_TOTAL];

      // Entry runway
      for (let j = 0; j < RUNWAY_LEN; j++) {
        const t = tileTable[p][j];
        const pts = rectPoints(t.x, t.y, 11, 11, startCell.angle);
        g.fillStyle(color, 0.45);
        g.fillPoints(pts, true);
        g.lineStyle(1.5, color, 1);
        g.strokePoints(pts, true);
        if (DEBUG_LABELS && p === 0) label(t.x, t.y, String(j), 10);
      }

      // Home Stretch lane
      for (let j = 0; j < HOME_STRETCH_LEN; j++) {
        const t = tileTable[p][TILE.HOME_STRETCH_START + j];
        const pts = rectPoints(t.x, t.y, 13, 13, theta);
        g.fillStyle(color, 0.85);
        g.fillPoints(pts, true);
        g.lineStyle(1.5, 0x1b1f27, 1);
        g.strokePoints(pts, true);
        if (DEBUG_LABELS && p === 0) label(t.x, t.y, String(TILE.HOME_STRETCH_START + j), 10);
      }

      // Home yard: backing plate + 4 token slots
      const yc = yardCenters[p];
      const plate = rectPoints(yc.x, yc.y, 20, 20, theta);
      g.fillStyle(color, 0.28);
      g.fillPoints(plate, true);
      g.lineStyle(2, color, 0.9);
      g.strokePoints(plate, true);
      yardSlots[p].forEach((s) => {
        g.fillStyle(0x10131a, 0.9);
        g.fillCircle(s.x, s.y, TOKEN_RADIUS + 1);
        g.lineStyle(2, color, 1);
        g.strokeCircle(s.x, s.y, TOKEN_RADIUS + 1);
      });

      // Seat label on the empty half of the wedge (A = even seats, B = odd seats)
      const lp = polar(185, theta - 0.17);
      label(lp.x, lp.y, `P${p + 1}`, 14);
      label(lp.x, lp.y + 14, p % 2 === 0 ? 'A' : 'B', 10, '#aab4c3');
    }

    // Shared center finish hub: 10 colored slices
    for (let p = 0; p < PLAYERS; p++) {
      const a0 = sectorAngle(p) - SECTOR_RAD / 2;
      const a1 = sectorAngle(p) + SECTOR_RAD / 2;
      g.fillStyle(PLAYER_COLORS[p], 0.9);
      g.fillPoints([{ x: CX, y: CY }, polar(R_HUB, a0), polar(R_HUB, a1)], true);
    }
    g.lineStyle(3, 0xffffff, 0.9);
    g.strokePoints(decagon(R_HUB), true);
    g.fillStyle(0x10131a, 0.85);
    g.fillCircle(CX, CY, 22);
    label(CX, CY, 'HOME', 10);

    // Finish spots
    for (let p = 0; p < PLAYERS; p++) {
      const f = tileTable[p][TILE.FINISH];
      g.lineStyle(1.5, 0xffffff, 0.8);
      g.strokeCircle(f.x, f.y, TOKEN_RADIUS);
    }

    return g;
  }

  // -------------------------------------------------------------------------
  // Client state
  // -------------------------------------------------------------------------
  const TOKENS_PER_PLAYER = 4;
  const TURN_SECONDS = 15;
  const ACK_TIMEOUT_MS = 4000;
  const STEP_MS = 90;
  const STACK_OFFSET = 6;
  const TOKEN_HIT_SIZE = 40;
  const AUTO_PLAY_DELAY_MS = 700;
  const NO_MOVE_DELAY_MS = 1000;

  const S = Object.freeze({
    CONNECTING: 'CONNECTING',
    SPECTATOR: 'SPECTATOR',
    WAITING_PEER: 'WAITING_PEER',
    OPPONENT_TURN: 'OPPONENT_TURN',
    AWAIT_ROLL: 'AWAIT_ROLL',
    AWAIT_PICK: 'AWAIT_PICK',
    AWAIT_ACK: 'AWAIT_ACK',
  });

  const client = {
    socket: null,
    scene: null,
    device: null, // 'A' | 'B'
    myPlayers: [],
    currentPlayerIndex: 0,
    peerConnected: false,
    state: S.CONNECTING,
    turnToken: 0, // bumps on every state change; cancels stale timeouts
    roll: null,
    legal: [],
    pending: null, // optimistic action awaiting server ack
    seq: 0,
    countdown: null,
    sprites: [],
    tokens: Array.from({ length: PLAYERS * TOKENS_PER_PLAYER }, (_, i) => ({
      playerIndex: Math.floor(i / TOKENS_PER_PLAYER),
      tokenIndex: i % TOKENS_PER_PLAYER,
      position: TILE.YARD,
    })),
  };

  const tokenAt = (p, t) => client.tokens[p * TOKENS_PER_PLAYER + t];
  const spriteOf = (t) => client.sprites[t.playerIndex * TOKENS_PER_PLAYER + t.tokenIndex];
  const deviceForTurn = (idx) => (idx % 2 === 0 ? 'A' : 'B'); // even = A, odd = B
  const isMyTurn = () => client.device !== null && deviceForTurn(client.currentPlayerIndex) === client.device;
  const buzz = (ms) => { if (typeof navigator !== 'undefined' && navigator.vibrate) navigator.vibrate(ms); };

  // -------------------------------------------------------------------------
  // Local move rules (used for highlighting and the auto-play fallback)
  // -------------------------------------------------------------------------
  function legalMoves(playerIndex, roll) {
    const moves = [];
    for (let i = 0; i < TOKENS_PER_PLAYER; i++) {
      const t = tokenAt(playerIndex, i);
      if (t.position === TILE.YARD) {
        if (roll === 6) moves.push({ tokenIndex: i, from: TILE.YARD, to: TILE.RUNWAY_START });
      } else if (t.position < TILE.FINISH && t.position + roll <= TILE.FINISH) {
        moves.push({ tokenIndex: i, from: t.position, to: t.position + roll });
      }
    }
    return moves;
  }

  function chooseAutoMove(moves) {
    const score = (m) => (m.to === TILE.FINISH ? 1000 : 0) + (m.from === TILE.YARD ? 500 : 0) + m.to;
    return moves.slice().sort((a, b) => score(b) - score(a))[0];
  }

  // -------------------------------------------------------------------------
  // HUD (DOM overlay built at runtime, so no index.html changes are needed)
  // -------------------------------------------------------------------------
  const ui = {};

  function buildUI() {
    const css = `
      #ludo-status{position:fixed;top:0;left:0;right:0;display:flex;align-items:center;justify-content:space-between;
        gap:10px;padding:calc(env(safe-area-inset-top,0px) + 8px) 12px 8px;background:rgba(16,19,26,.88);
        color:#fff;font:600 14px/1.25 system-ui,sans-serif;z-index:20;pointer-events:none}
      #ludo-status .ls-dice{display:none;padding:4px 10px;border-radius:999px;background:#ffd23f;color:#10131a;font-weight:800;white-space:nowrap}
      #ludo-status .ls-dice.pop{animation:ludoPop .25s ease-out}
      @keyframes ludoPop{0%{transform:scale(.6)}70%{transform:scale(1.15)}100%{transform:scale(1)}}
      #ludo-roll{position:fixed;left:0;right:0;bottom:0;display:none;flex-direction:column;align-items:center;gap:8px;
        padding:12px 16px calc(env(safe-area-inset-bottom,0px) + 12px);background:rgba(16,19,26,.92);z-index:20}
      #ludo-roll.show{display:flex}
      #ludo-roll button{width:100%;max-width:420px;min-height:56px;border:0;border-radius:14px;background:#ffd23f;color:#10131a;
        font:800 20px system-ui,sans-serif;letter-spacing:.06em;touch-action:manipulation}
      #ludo-roll button:disabled{opacity:.4}
      #ludo-roll .lr-hint{color:#dfe6ee;font:600 14px system-ui,sans-serif;min-height:18px}
      #ludo-roll .lr-row{display:flex;align-items:center;gap:10px;width:100%;max-width:420px}
      #ludo-roll .lr-bar{flex:1;height:8px;border-radius:4px;background:rgba(255,255,255,.15);overflow:hidden}
      #ludo-roll .lr-bar i{display:block;height:100%;background:#4cd964;transform-origin:left center}
      #ludo-roll.urgent .lr-bar i{background:#ff453a}
      #ludo-roll .lr-secs{color:#fff;font:800 18px system-ui,sans-serif;min-width:28px;text-align:right}
    `;
    const style = document.createElement('style');
    style.textContent = css;
    document.head.appendChild(style);

    const mk = (tag, cls, parent, text) => {
      const e = document.createElement(tag);
      if (cls) e.className = cls;
      if (text) e.textContent = text;
      if (parent) parent.appendChild(e);
      return e;
    };

    const status = mk('div', null, document.body);
    status.id = 'ludo-status';
    ui.statusText = mk('span', 'ls-text', status, 'Connecting…');
    ui.dice = mk('span', 'ls-dice', status);

    const overlay = mk('div', null, document.body);
    overlay.id = 'ludo-roll';
    ui.overlay = overlay;
    ui.rollBtn = mk('button', null, overlay, 'ROLL DICE');
    ui.hint = mk('div', 'lr-hint', overlay);
    const row = mk('div', 'lr-row', overlay);
    ui.barFill = mk('i', null, mk('div', 'lr-bar', row));
    ui.secs = mk('span', 'lr-secs', row, String(TURN_SECONDS));

    ui.setStatus = (t) => { ui.statusText.textContent = t; };
    ui.setHint = (t) => { ui.hint.textContent = t; };
    ui.showOverlay = (v) => ui.overlay.classList.toggle('show', v);
    ui.setRollEnabled = (v) => { ui.rollBtn.disabled = !v; };
    ui.showDice = (value, who) => {
      ui.dice.textContent = `${who} rolled ${value}`;
      ui.dice.style.display = 'inline-block';
      ui.dice.classList.remove('pop');
      void ui.dice.offsetWidth; // restart animation
      ui.dice.classList.add('pop');
    };
    ui.setCountdown = (secs, frac) => {
      ui.secs.textContent = String(secs);
      ui.barFill.style.transform = `scaleX(${frac})`;
      ui.overlay.classList.toggle('urgent', secs <= 5);
    };

    ui.rollBtn.addEventListener('click', () => performRoll(false));
  }

  function renderStatus() {
    const cur = client.currentPlayerIndex;
    const who = `P${cur + 1} (Device ${deviceForTurn(cur)})`;
    switch (client.state) {
      case S.CONNECTING: return ui.setStatus('Connecting…');
      case S.SPECTATOR: return ui.setStatus('Game is full: both devices are already connected');
      case S.WAITING_PEER: return ui.setStatus('Waiting for the other device…');
      case S.AWAIT_ROLL: return ui.setStatus(`Your turn: ${who}`);
      case S.AWAIT_PICK: return ui.setStatus(`Your turn: P${cur + 1}`);
      default: return ui.setStatus(`Waiting for ${who}`); // OPPONENT_TURN / AWAIT_ACK
    }
  }

  function flash(text, ms = 2500) {
    ui.setStatus(text);
    setTimeout(renderStatus, ms);
  }

  // -------------------------------------------------------------------------
  // Countdown
  // -------------------------------------------------------------------------
  function stopCountdown() {
    if (client.countdown) clearInterval(client.countdown);
    client.countdown = null;
  }

  function startCountdown(seconds, onExpire) {
    stopCountdown();
    const total = seconds * 1000;
    const endAt = performance.now() + total;
    ui.setCountdown(seconds, 1);
    client.countdown = setInterval(() => {
      const left = Math.max(0, endAt - performance.now());
      ui.setCountdown(Math.ceil(left / 1000), left / total);
      if (left <= 0) {
        stopCountdown();
        onExpire();
      }
    }, 100);
  }

  // -------------------------------------------------------------------------
  // Token sprites, highlighting, animation
  // -------------------------------------------------------------------------
  function createTokenSprites(scene) {
    client.tokens.forEach((t) => {
      const body = scene.add.circle(0, 0, TOKEN_RADIUS, PLAYER_COLORS[t.playerIndex]).setStrokeStyle(2, 0xffffff);
      const ring = scene.add.circle(0, 0, TOKEN_RADIUS + 6).setStrokeStyle(3, 0xffffff).setVisible(false);
      const c = scene.add.container(0, 0, [ring, body]).setDepth(5);
      c.setSize(TOKEN_HIT_SIZE, TOKEN_HIT_SIZE).setInteractive();
      c.on('pointerdown', () => onTokenTap(t));
      c.ring = ring;
      c.moving = false;
      c.pulse = null;
      const p = getTileCoordinates(t.playerIndex, t.position, t.tokenIndex);
      c.setPosition(p.x, p.y);
      client.sprites.push(c);
    });
  }

  function stackKey(t) {
    if (t.position === TILE.YARD) return `y:${t.playerIndex}:${t.tokenIndex}`;
    const g = getGlobalRingIndex(t.playerIndex, t.position);
    return g !== null ? `r:${g}` : `${t.playerIndex}:${t.position}`;
  }

  function moveSprite(sprite, x, y, immediate) {
    if (Math.abs(sprite.x - x) < 0.5 && Math.abs(sprite.y - y) < 0.5) return;
    if (immediate) sprite.setPosition(x, y);
    else client.scene.tweens.add({ targets: sprite, x, y, duration: 100, ease: 'Sine.easeOut' });
  }

  // Spread tokens that share a tile so every token stays visible and tappable
  function layoutStacks(immediate) {
    const groups = new Map();
    client.tokens.forEach((t) => {
      if (spriteOf(t).moving) return;
      const key = stackKey(t);
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(t);
    });
    groups.forEach((group) => {
      group.forEach((t, i) => {
        const base = getTileCoordinates(t.playerIndex, t.position, t.tokenIndex);
        let { x, y } = base;
        if (group.length > 1) {
          const a = (2 * Math.PI * i) / group.length;
          x += Math.cos(a) * STACK_OFFSET;
          y += Math.sin(a) * STACK_OFFSET;
        }
        moveSprite(spriteOf(t), x, y, immediate);
      });
    });
  }

  function animateToken(token, fromPos, toPos, done) {
    const sprite = spriteOf(token);
    const scene = client.scene;
    scene.tweens.killTweensOf(sprite);
    sprite.moving = true;
    sprite.setDepth(10);

    const path = [];
    if (fromPos < 0 || toPos < fromPos) {
      path.push(getTileCoordinates(token.playerIndex, toPos, token.tokenIndex));
    } else {
      for (let pos = fromPos + 1; pos <= toPos; pos++) {
        path.push(getTileCoordinates(token.playerIndex, pos, token.tokenIndex));
      }
    }

    const step = (i) => {
      if (i >= path.length) {
        sprite.moving = false;
        sprite.setDepth(5);
        layoutStacks(false);
        if (done) done();
        return;
      }
      scene.tweens.add({
        targets: sprite,
        x: path[i].x,
        y: path[i].y,
        duration: fromPos < 0 ? 220 : STEP_MS,
        ease: 'Sine.easeInOut',
        onComplete: () => step(i + 1),
      });
    };
    step(0);
  }

  function clearHighlights() {
    client.sprites.forEach((s) => {
      if (s.pulse) { s.pulse.stop(); s.pulse = null; }
      s.ring.setVisible(false).setAlpha(1);
    });
  }

  function highlightMoves(moves) {
    moves.forEach((m) => {
      const s = spriteOf(tokenAt(client.currentPlayerIndex, m.tokenIndex));
      s.ring.setVisible(true).setAlpha(1);
      s.pulse = client.scene.tweens.add({
        targets: s.ring, alpha: { from: 1, to: 0.25 }, duration: 450, yoyo: true, repeat: -1,
      });
    });
  }

  function snapSprites() {
    client.sprites.forEach((s) => {
      client.scene.tweens.killTweensOf(s);
      s.moving = false;
      s.setDepth(5);
    });
    layoutStacks(true);
  }

  // -------------------------------------------------------------------------
  // UI state machine
  // -------------------------------------------------------------------------
  function setState(next) {
    client.state = next;
    client.turnToken++;
    renderStatus();
  }

  function resetTurnUI() {
    stopCountdown();
    clearHighlights();
    ui.showOverlay(false);
  }

  function enterAwaitRoll() {
    resetTurnUI();
    client.roll = null;
    client.legal = [];
    setState(S.AWAIT_ROLL);
    ui.showOverlay(true);
    ui.setRollEnabled(true);
    ui.setHint('Tap ROLL DICE');
    startCountdown(TURN_SECONDS, () => performRoll(true)); // timeout => auto roll + auto move
    buzz([30, 40, 30]);
  }

  function enterOpponentTurn() {
    resetTurnUI();
    setState(S.OPPONENT_TURN);
  }

  /**
   * Persistent turn check. Runs on every state change and on a heartbeat.
   * currentPlayerIndex % 2 === 0 -> Device A's turn, otherwise Device B's.
   */
  function evaluateTurn() {
    if (!client.socket || client.state === S.SPECTATOR) return;
    if (!client.socket.connected || client.device === null) return;
    if (client.pending) return; // optimistic action in flight

    if (!client.peerConnected) {
      if (client.state !== S.WAITING_PEER) {
        resetTurnUI();
        setState(S.WAITING_PEER);
      }
      return;
    }

    if (isMyTurn()) {
      if (client.state !== S.AWAIT_ROLL && client.state !== S.AWAIT_PICK) enterAwaitRoll();
    } else if (client.state !== S.OPPONENT_TURN) {
      enterOpponentTurn();
    }
    renderStatus();
  }

  function performRoll(auto) {
    if (client.state !== S.AWAIT_ROLL || !isMyTurn()) return;
    stopCountdown();

    const playerIndex = client.currentPlayerIndex;
    const value = 1 + Math.floor(Math.random() * 6);
    client.roll = value;
    client.legal = legalMoves(playerIndex, value);

    setState(S.AWAIT_PICK);
    const stamp = client.turnToken;
    const later = (fn, ms) =>
      setTimeout(() => {
        if (stamp === client.turnToken && client.state === S.AWAIT_PICK) fn();
      }, ms);

    // Optimistic: show the die instantly, then tell the server
    ui.showDice(value, `P${playerIndex + 1}`);
    ui.setRollEnabled(false);
    buzz(20);
    client.socket.emit('ROLL_DICE', { playerIndex, value });

    if (client.legal.length === 0) {
      ui.setHint('No valid move: passing');
      later(submitPass, NO_MOVE_DELAY_MS);
    } else if (auto) {
      ui.setHint('Time is up: playing automatically');
      later(autoPick, AUTO_PLAY_DELAY_MS);
    } else {
      ui.setHint('Tap a glowing token');
      highlightMoves(client.legal);
      startCountdown(TURN_SECONDS, autoPick);
    }
  }

  function autoPick() {
    if (client.state !== S.AWAIT_PICK) return;
    if (client.legal.length === 0) return submitPass();
    commitMove(chooseAutoMove(client.legal));
  }

  function onTokenTap(token) {
    if (client.state !== S.AWAIT_PICK || token.playerIndex !== client.currentPlayerIndex) return;
    const move = client.legal.find((m) => m.tokenIndex === token.tokenIndex);
    if (move) commitMove(move);
  }

  function sendWithAck(event, payload, clientMoveId) {
    client.socket.timeout(ACK_TIMEOUT_MS).emit(event, payload, (err, res) => {
      if (!client.pending || client.pending.clientMoveId !== clientMoveId) return; // already resolved
      if (err || !res || !res.ok) {
        client.socket.emit('REQUEST_SYNC'); // STATE_SYNC will roll the screen back
        return;
      }
      client.pending = null;
      client.currentPlayerIndex = res.nextPlayerIndex;
      client.roll = null;
      client.legal = [];
      evaluateTurn();
    });
  }

  function commitMove(move) {
    if (client.state !== S.AWAIT_PICK) return;
    const playerIndex = client.currentPlayerIndex;
    const token = tokenAt(playerIndex, move.tokenIndex);
    const clientMoveId = `${client.device}${++client.seq}`;

    resetTurnUI();
    client.pending = { clientMoveId, kind: 'move' };
    setState(S.AWAIT_ACK);

    // 1) Optimistic local render, instantly
    token.position = move.to;
    animateToken(token, move.from, move.to);
    client.currentPlayerIndex = (playerIndex + 1) % PLAYERS;
    renderStatus();

    // 2) Immediately send the packet
    sendWithAck('MOVE_TOKEN', { playerIndex, tokenIndex: move.tokenIndex, toPosition: move.to, clientMoveId }, clientMoveId);
  }

  function submitPass() {
    if (client.state !== S.AWAIT_PICK && client.state !== S.AWAIT_ROLL) return;
    const playerIndex = client.currentPlayerIndex;
    const clientMoveId = `${client.device}${++client.seq}`;

    resetTurnUI();
    client.pending = { clientMoveId, kind: 'pass' };
    setState(S.AWAIT_ACK);
    client.currentPlayerIndex = (playerIndex + 1) % PLAYERS;
    renderStatus();

    sendWithAck('PASS_TURN', { playerIndex, clientMoveId }, clientMoveId);
  }

  // -------------------------------------------------------------------------
  // Networking
  // -------------------------------------------------------------------------
  function applySnapshot(snap) {
    resetTurnUI();
    client.pending = null;
    client.roll = null;
    client.legal = [];
    client.currentPlayerIndex = snap.currentPlayerIndex;
    snap.tokens.forEach((t, i) => { client.tokens[i].position = t.position; });
    client.peerConnected = client.device === 'A' ? snap.deviceBConnected : snap.deviceAConnected;
    snapSprites();
    setState(S.CONNECTING); // forces evaluateTurn to choose the right state
    evaluateTurn();
  }

  function initNetwork() {
    if (typeof io === 'undefined') {
      ui.setStatus('socket.io client script is missing');
      return;
    }
    const socket = io(root.LUDO_SERVER_URL || undefined, { transports: ['websocket'] });
    client.socket = socket;

    socket.on('connect_error', (err) => {
      if (err && err.data && err.data.code === 'SERVER_FULL') {
        resetTurnUI();
        setState(S.SPECTATOR);
        socket.disconnect();
      } else {
        ui.setStatus('Connection problem, retrying…');
      }
    });

    socket.on('disconnect', () => {
      client.pending = null;
      client.peerConnected = false;
      resetTurnUI();
      setState(S.CONNECTING);
    });

    socket.on('ASSIGNED', ({ device, playerIndices }) => {
      client.device = device;
      client.myPlayers = playerIndices;
    });

    socket.on('STATE_SYNC', applySnapshot);

    socket.on('PEER_STATUS', ({ device, connected }) => {
      if (device === client.device) return;
      client.peerConnected = connected;
      evaluateTurn();
    });

    socket.on('MIRROR_ROLL', ({ playerIndex, value }) => ui.showDice(value, `P${playerIndex + 1}`));

    socket.on('MIRROR_MOVE', (m) => {
      const token = tokenAt(m.playerIndex, m.tokenIndex);
      if (!token) return;
      const from = token.position;
      token.position = m.toPosition;
      animateToken(token, from, m.toPosition);
      client.currentPlayerIndex = m.nextPlayerIndex;
      evaluateTurn();
    });

    socket.on('MIRROR_PASS', (m) => {
      client.currentPlayerIndex = m.nextPlayerIndex;
      evaluateTurn();
    });

    // Server refused an optimistic action: roll back to its authoritative snapshot
    socket.on('MOVE_REJECTED', ({ reason, state: snap }) => {
      if (snap) applySnapshot(snap);
      flash(`Move rejected (${reason}), resynced`);
    });
  }

  // -------------------------------------------------------------------------
  // Phaser bootstrap (skipped when loaded outside a browser, e.g. unit tests)
  // -------------------------------------------------------------------------
  const api = {
    CANVAS_SIZE, CX, CY, PLAYERS, TILE, TOKEN_RADIUS, PLAYER_COLORS,
    RING_TOTAL, RING_PER_SECTOR,
    getTileCoordinates, getGlobalRingIndex, getTileKind,
  };

  if (typeof Phaser !== 'undefined') {
    class BoardScene extends Phaser.Scene {
      constructor() {
        super('BoardScene');
      }
      create() {
        client.scene = this;
        this.board = drawBoard(this);
        createTokenSprites(this);
        layoutStacks(true);
        buildUI();
        initNetwork();
        setInterval(evaluateTurn, 500); // persistent turn check
        root.LudoScene = this;
      }
    }

    root.LudoGame = new Phaser.Game({
      type: Phaser.AUTO,
      width: CANVAS_SIZE,
      height: CANVAS_SIZE,
      parent: 'game-container', // falls back to <body> if the element is absent
      backgroundColor: '#12151c',
      scale: { mode: Phaser.Scale.FIT, autoCenter: Phaser.Scale.CENTER_BOTH },
      render: { antialias: true },
      scene: [BoardScene],
    });
  }

  root.LudoBoard = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
