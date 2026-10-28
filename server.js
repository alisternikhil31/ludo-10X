'use strict';

const http = require('http');
const path = require('path');
const express = require('express');
const { Server } = require('socket.io');

// ---------------------------------------------------------------------------
// Config
// ---------------------------------------------------------------------------
const PORT = Number(process.env.PORT) || 3000;
const CORS_ORIGIN = process.env.CORS_ORIGIN || '*';
const IDLE_RESET_MS = Number(process.env.IDLE_RESET_MS) || 5 * 60 * 1000;

const TOTAL_PLAYERS = 10;
const TOKENS_PER_PLAYER = 4;
const BASE_POSITION = -1; // token still in home yard
const MAX_POSITION = 58; // finish hub (matches TILE.FINISH in game.js)

// ---------------------------------------------------------------------------
// Master state
// ---------------------------------------------------------------------------
function createTokens() {
  const tokens = [];
  for (let p = 0; p < TOTAL_PLAYERS; p++) {
    for (let t = 0; t < TOKENS_PER_PLAYER; t++) {
      tokens.push({ playerIndex: p, tokenIndex: t, position: BASE_POSITION });
    }
  }
  return tokens;
}

const state = {
  deviceA_socketId: null,
  deviceB_socketId: null,
  currentPlayerIndex: 0, // 0..9
  tokens: createTokens(), // master global token array (40 tokens)
};

let idleResetTimer = null;

// Zig-zag seating: even indices -> Device A, odd indices -> Device B
const deviceForPlayer = (i) => (i % 2 === 0 ? 'A' : 'B');
const socketIdForDevice = (d) => (d === 'A' ? state.deviceA_socketId : state.deviceB_socketId);
const bothConnected = () => Boolean(state.deviceA_socketId && state.deviceB_socketId);

const playersForDevice = (d) =>
  Array.from({ length: TOTAL_PLAYERS }, (_, i) => i).filter((i) => deviceForPlayer(i) === d);

const snapshot = () => ({
  currentPlayerIndex: state.currentPlayerIndex,
  tokens: state.tokens,
  deviceAConnected: Boolean(state.deviceA_socketId),
  deviceBConnected: Boolean(state.deviceB_socketId),
});

function resetGame() {
  state.currentPlayerIndex = 0;
  state.tokens = createTokens();
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------
function validateMove(socket, payload) {
  if (!payload || typeof payload !== 'object') return 'INVALID_PAYLOAD';

  const { playerIndex, tokenIndex, toPosition } = payload;
  if (
    !Number.isInteger(playerIndex) || playerIndex < 0 || playerIndex >= TOTAL_PLAYERS ||
    !Number.isInteger(tokenIndex) || tokenIndex < 0 || tokenIndex >= TOKENS_PER_PLAYER ||
    !Number.isInteger(toPosition) || toPosition < BASE_POSITION || toPosition > MAX_POSITION
  ) {
    return 'INVALID_PAYLOAD';
  }

  if (!bothConnected()) return 'OPPONENT_DISCONNECTED';
  if (playerIndex !== state.currentPlayerIndex) return 'NOT_YOUR_TURN';

  // Sender must be the socket authorized for the active player
  const authorizedSocketId = socketIdForDevice(deviceForPlayer(state.currentPlayerIndex));
  if (socket.id !== authorizedSocketId) return 'UNAUTHORIZED_SOCKET';

  const token = state.tokens[playerIndex * TOKENS_PER_PLAYER + tokenIndex];
  if (!token) return 'TOKEN_NOT_FOUND';
  if (token.position === toPosition) return 'NO_OP_MOVE';

  return null;
}

// Shared check for events that only carry a playerIndex (ROLL_DICE, PASS_TURN)
function authorizeActiveTurn(socket, payload) {
  if (!payload || typeof payload !== 'object') return 'INVALID_PAYLOAD';
  if (!bothConnected()) return 'OPPONENT_DISCONNECTED';
  if (payload.playerIndex !== state.currentPlayerIndex) return 'NOT_YOUR_TURN';
  if (socket.id !== socketIdForDevice(deviceForPlayer(state.currentPlayerIndex))) {
    return 'UNAUTHORIZED_SOCKET';
  }
  return null;
}

// ---------------------------------------------------------------------------
// Server setup
// ---------------------------------------------------------------------------
const app = express();
app.disable('x-powered-by');
app.use(express.static(path.join(__dirname, 'public')));
app.get('/health', (_req, res) =>
  res.json({
    ok: true,
    deviceA: Boolean(state.deviceA_socketId),
    deviceB: Boolean(state.deviceB_socketId),
    currentPlayerIndex: state.currentPlayerIndex,
  })
);

const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: CORS_ORIGIN },
  pingInterval: 10000,
  pingTimeout: 8000,
  maxHttpBufferSize: 1e5,
});

// ---------------------------------------------------------------------------
// Middleware: device assignment (first free slot; A first, then B; others rejected)
// ---------------------------------------------------------------------------
io.use((socket, next) => {
  if (!state.deviceA_socketId) {
    state.deviceA_socketId = socket.id;
    socket.data.device = 'A';
    return next();
  }
  if (!state.deviceB_socketId) {
    state.deviceB_socketId = socket.id;
    socket.data.device = 'B';
    return next();
  }
  const err = new Error('SERVER_FULL');
  err.data = { code: 'SERVER_FULL', role: 'spectator' };
  return next(err);
});

// ---------------------------------------------------------------------------
// Connection handling
// ---------------------------------------------------------------------------
io.on('connection', (socket) => {
  const device = socket.data.device;

  if (idleResetTimer) {
    clearTimeout(idleResetTimer);
    idleResetTimer = null;
  }

  console.log(`[connect] Device ${device} (${socket.id})`);

  socket.emit('ASSIGNED', {
    device,
    playerIndices: playersForDevice(device),
    totalPlayers: TOTAL_PLAYERS,
  });
  socket.emit('STATE_SYNC', snapshot());
  socket.broadcast.emit('PEER_STATUS', { device, connected: true });

  socket.on('REQUEST_SYNC', () => socket.emit('STATE_SYNC', snapshot()));

  // Relay the roll so the other device can display it
  socket.on('ROLL_DICE', (payload) => {
    if (authorizeActiveTurn(socket, payload)) return;
    const { playerIndex, value } = payload;
    if (!Number.isInteger(value) || value < 1 || value > 6) return;
    socket.broadcast.emit('MIRROR_ROLL', { playerIndex, value });
  });

  socket.on('MOVE_TOKEN', (payload, ack) => {
    const reply = typeof ack === 'function' ? ack : () => {};
    const clientMoveId = payload && payload.clientMoveId;

    const error = validateMove(socket, payload);
    if (error) {
      // Lets the optimistic client roll back and resync
      socket.emit('MOVE_REJECTED', { reason: error, clientMoveId, state: snapshot() });
      return reply({ ok: false, reason: error });
    }

    const { playerIndex, tokenIndex, toPosition } = payload;
    const token = state.tokens[playerIndex * TOKENS_PER_PLAYER + tokenIndex];
    const fromPosition = token.position;
    token.position = toPosition;

    // Advance zig-zag turn (extra-turn / capture rules to be added with the rules engine)
    state.currentPlayerIndex = (state.currentPlayerIndex + 1) % TOTAL_PLAYERS;

    // Instant mirror to the other device
    socket.broadcast.emit('MIRROR_MOVE', {
      playerIndex,
      tokenIndex,
      fromPosition,
      toPosition,
      nextPlayerIndex: state.currentPlayerIndex,
    });

    // Confirm to the sender (reconciles optimistic state)
    reply({ ok: true, clientMoveId, nextPlayerIndex: state.currentPlayerIndex });
  });

  // No legal move (or timeout with nothing playable): advance the turn
  socket.on('PASS_TURN', (payload, ack) => {
    const reply = typeof ack === 'function' ? ack : () => {};
    const clientMoveId = payload && payload.clientMoveId;

    const error = authorizeActiveTurn(socket, payload);
    if (error) {
      socket.emit('MOVE_REJECTED', { reason: error, clientMoveId, state: snapshot() });
      return reply({ ok: false, reason: error });
    }

    const passedPlayer = state.currentPlayerIndex;
    state.currentPlayerIndex = (passedPlayer + 1) % TOTAL_PLAYERS;

    socket.broadcast.emit('MIRROR_PASS', {
      playerIndex: passedPlayer,
      nextPlayerIndex: state.currentPlayerIndex,
    });
    reply({ ok: true, clientMoveId, nextPlayerIndex: state.currentPlayerIndex });
  });

  socket.on('disconnect', (reason) => {
    console.log(`[disconnect] Device ${device} (${socket.id}) - ${reason}`);

    // Only free the slot if this socket still owns it
    if (state.deviceA_socketId === socket.id) state.deviceA_socketId = null;
    if (state.deviceB_socketId === socket.id) state.deviceB_socketId = null;

    socket.broadcast.emit('PEER_STATUS', { device, connected: false });

    // Both gone: keep state for a grace period so devices can resume, then reset
    if (!state.deviceA_socketId && !state.deviceB_socketId && !idleResetTimer) {
      idleResetTimer = setTimeout(() => {
        resetGame();
        idleResetTimer = null;
        console.log('[reset] Game state cleared after idle timeout');
      }, IDLE_RESET_MS);
    }
  });
});

// ---------------------------------------------------------------------------
// Startup / shutdown
// ---------------------------------------------------------------------------
server.listen(PORT, () => console.log(`Ludo server listening on :${PORT}`));

function shutdown(signal) {
  console.log(`[${signal}] shutting down`);
  if (idleResetTimer) clearTimeout(idleResetTimer);
  io.close(() => server.close(() => process.exit(0)));
  setTimeout(() => process.exit(1), 5000).unref();
}
process.on('SIGINT', () => shutdown('SIGINT'));
process.on('SIGTERM', () => shutdown('SIGTERM'));
