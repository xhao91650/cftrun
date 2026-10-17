/**
 * CF-Workers-TURN-EdgeTunnel
 * 基于 Cloudflare Workers 的 VLESS + TURN(TCP/UDP relay) + XUDP 代理
 * 内置 TURN 节点池 + 轮询订阅 + Vue3/Element Plus 管理面板
 *
 * 协议参考: RFC 5389(STUN) / RFC 5766(TURN) / RFC 6062(TURN TCP) / RFC 8656(TURN bis)
 * 依赖: cloudflare:sockets, KV namespace (KV)
 */
import { connect } from 'cloudflare:sockets';

// ============================================================
//  全局常量
// ============================================================
const VERSION = '2026-10-16';
const MAX_ED = 8192;
const CONNECT_TIMEOUT = 15000;
const DEFAULT_UUID = '2523c510-9ff0-415b-9582-93949bfae7e3';

// ============================================================
//  工具函数
// ============================================================
const dec = new TextDecoder();
const enc = s => new TextEncoder().encode(s);
const u16 = (b, o = 0) => (b[o] << 8) | b[o + 1];
const pad4 = n => -n & 3;
const cat = (...a) => {
  const r = new Uint8Array(a.reduce((s, x) => s + x.length, 0));
  a.reduce((o, x) => (r.set(x, o), o + x.length), 0);
  return r;
};
const safeClose = (...a) => a.forEach(x => { try { x?.close?.(); } catch {} });
const randomTID = () => crypto.getRandomValues(new Uint8Array(12));
const isIPv4 = h => /^\d{1,3}(\.\d{1,3}){3}$/.test(h);
const stripBrackets = h => h.replace(/^\[|\]$/g, '');

async function md5(s) {
  return new Uint8Array(await crypto.subtle.digest('MD5', enc(s)));
}
async function md5md5(s) {
  const h1 = await md5(s);
  return Array.from(new Uint8Array(await crypto.subtle.digest('MD5', h1)))
    .map(b => b.toString(16).padStart(2, '0')).join('');
}
async function resolveIP(host) {
  if (isIPv4(host)) return host;
  try {
    const r = await fetch(`https://cloudflare-dns.com/dns-query?name=${encodeURIComponent(host)}&type=A`,
      { headers: { Accept: 'application/dns-json' } }).then(r => r.json());
    return r.Answer?.find(a => a.type === 1)?.data ?? null;
  } catch { return null; }
}

// ============================================================
//  VLESS 协议解析
// ============================================================
let idBytes = null;
function setUUID(uuid) {
  idBytes = Uint8Array.fromHex(uuid.replaceAll('-', ''));
}
function checkUUID(c) {
  return !idBytes.some((v, i) => c[i + 1] !== v);
}
function addrStr(t, b) {
  if (t === 3) return dec.decode(b);
  if (t === 1) return b.join('.');
  if (t === 4) return `[${Array.from({ length: 8 }, (_, i) => u16(b, i * 2).toString(16)).join(':')}]`;
  return '';
}
function parseAddr(b, o, t) {
  const l = t === 3 ? b[o++] : t === 1 ? 4 : t === 4 ? 16 : 0;
  return l && o + l <= b.length ? { addrBytes: b.subarray(o, o + l), dataOffset: o + l } : null;
}
function parseVLESS(c) {
  if (!checkUUID(c)) return null;
  const o = 19 + c[17];
  const port = u16(c, o);
  const t = c[o + 2] === 1 ? 1 : c[o + 2] + 1;
  const a = parseAddr(c, o + 3, t);
  return a ? { addrType: t, ...a, port } : null;
}
function isVLESSUDP(c) {
  return checkUUID(c) && c[18 + c[17]] === 3 ? { cmd: 3, dataOffset: 19 + c[17] } : null;
}

// ============================================================
//  STUN / TURN 协议
// ============================================================
const MAGIC = new Uint8Array([0x21, 0x12, 0xA4, 0x42]);
const MT = {
  AQ: 0x003, AO: 0x103, AE: 0x113,
  PQ: 0x008, PO: 0x108,
  CQ: 0x00A, CO: 0x10A,
  BQ: 0x00B, BO: 0x10B,
  SI: 0x016, DI: 0x017,
};
const AT = {
  USER: 0x006, MI: 0x008, ERR: 0x009,
  PEER: 0x012, DATA: 0x013,
  REALM: 0x014, NONCE: 0x015,
  TRANSPORT: 0x019, CONNID: 0x02A,
};

function stunAttr(t, v) {
  const b = new Uint8Array(4 + v.length + pad4(v.length));
  const d = new DataView(b.buffer);
  d.setUint16(0, t); d.setUint16(2, v.length);
  b.set(v, 4);
  return b;
}
function stunMsg(t, id, attrs) {
  const body = cat(...attrs);
  const h = new Uint8Array(20);
  const d = new DataView(h.buffer);
  d.setUint16(0, t); d.setUint16(2, body.length);
  h.set(MAGIC, 4); h.set(id, 8);
  return cat(h, body);
}
function xorPeer(ip, port) {
  const b = new Uint8Array(8);
  b[1] = 1;
  new DataView(b.buffer).setUint16(2, port ^ 0x2112);
  ip.split('.').forEach((v, i) => b[4 + i] = +v ^ MAGIC[i]);
  return b;
}
function parseXorPeer(d) {
  if (!d?.length >= 8) return ['', 0];
  return [MAGIC.map((m, i) => d[4 + i] ^ m).join('.'), u16(d, 2) ^ 0x2112];
}
function parseStun(d) {
  if (d.length < 20 || MAGIC.some((v, i) => d[4 + i] !== v)) return null;
  const dv = new DataView(d.buffer, d.byteOffset, d.byteLength);
  const ml = dv.getUint16(2);
  const attrs = {};
  for (let o = 20; o + 4 <= 20 + ml;) {
    const t = dv.getUint16(o), l = dv.getUint16(o + 2);
    if (o + 4 + l > d.length) break;
    attrs[t] = d.slice(o + 4, o + 4 + l);
    o += 4 + l + pad4(l);
  }
  return { type: dv.getUint16(0), attrs };
}
function parseErr(d) {
  return d?.length >= 4 ? (d[2] & 7) * 100 + d[3] : 0;
}
async function addIntegrity(m, key) {
  const c = new Uint8Array(m);
  const d = new DataView(c.buffer);
  d.setUint16(2, d.getUint16(2) + 24);
  const k = await crypto.subtle.importKey('raw', key, { name: 'HMAC', hash: 'SHA-1' }, false, ['sign']);
  return cat(c, stunAttr(AT.MI, new Uint8Array(await crypto.subtle.sign('HMAC', k, c))));
}
async function readStun(rd, buf) {
  let b = buf ?? new Uint8Array(0);
  const pull = async () => {
    const { done, value } = await rd.read();
    if (done) throw 0;
    b = cat(b, new Uint8Array(value));
  };
  try {
    while (b.length < 20) await pull();
    const n = 20 + u16(b, 2);
    while (b.length < n) await pull();
    return [parseStun(b.subarray(0, n)), b.length > n ? b.subarray(n) : null];
  } catch { return [null, null]; }
}

// TURN 认证（支持无认证 / 长期凭据）
async function turnAuth(w, r, transport, { user, pass }, pipeline) {
  const tp = new Uint8Array([transport, 0, 0, 0]);
  await w.write(stunMsg(MT.AQ, randomTID(), [stunAttr(AT.TRANSPORT, tp)]));
  let [msg, ex] = await readStun(r);
  if (!msg) return null;
  let key = null, aa = [];
  const sign = m => key ? addIntegrity(m, key) : Promise.resolve(m);
  if (msg.type === MT.AE && user && pass && parseErr(msg.attrs[AT.ERR]) === 401) {
    const realm = dec.decode(msg.attrs[AT.REALM] ?? new Uint8Array(0));
    const nonce = msg.attrs[AT.NONCE] ?? new Uint8Array(0);
    key = await md5(`${user}:${realm}:${pass}`);
    aa = [stunAttr(AT.USER, enc(user)), stunAttr(AT.REALM, enc(realm)), stunAttr(AT.NONCE, nonce)];
    const aq = await addIntegrity(stunMsg(MT.AQ, randomTID(), [stunAttr(AT.TRANSPORT, tp), ...aa]), key);
    const extras = pipeline ? await Promise.all(pipeline(aa, sign)) : [];
    await w.write(extras.length ? cat(aq, ...extras) : aq);
    [msg, ex] = await readStun(r, ex);
    if (!msg) return null;
  } else if (msg.type === MT.AO && pipeline) {
    const extras = await Promise.all(pipeline(aa, sign));
    if (extras.length) await w.write(cat(...extras));
  }
  return msg.type === MT.AO ? { key, aa, ex, sign } : null;
}

// 从 URL 解析 turn:// 节点
function parseTurnURL(url) {
  const m = decodeURIComponent(url).match(/\/turn:\/\/([^?&#\s]*)/i);
  if (!m) return null;
  const t = m[1];
  const at = t.lastIndexOf('@');
  const cred = at >= 0 ? t.slice(0, at) : '';
  const hp = t.slice(at + 1);
  const [host, p] = hp.split(':');
  const ci = cred.indexOf(':');
  return p ? {
    host, port: +p,
    user: ci >= 0 ? cred.slice(0, ci) : '',
    pass: ci >= 0 ? cred.slice(ci + 1) : '',
  } : null;
}

// ============================================================
//  TURN TCP Relay (RFC 6062)
// ============================================================
async function turnTCPConn({ host, port, user, pass }, targetIp, targetPort) {
  let ctrl = null, data = null;
  const close = () => safeClose(ctrl, data);
  try {
    ctrl = connect({ hostname: host, port });
    await ctrl.opened;
    const cw = ctrl.writable.getWriter(), cr = ctrl.readable.getReader();
    const peer = stunAttr(AT.PEER, xorPeer(targetIp, targetPort));
    const auth = await turnAuth(cw, cr, 6, { user, pass }, (aa, sign) => [
      sign(stunMsg(MT.PQ, randomTID(), [peer, ...aa])),
      sign(stunMsg(MT.CQ, randomTID(), [peer, ...aa])),
    ]);
    if (!auth) { close(); return null; }
    const { aa, sign } = auth;
    let ex = auth.ex;
    data = connect({ hostname: host, port });
    let r;
    [r, ex] = await readStun(cr, ex);
    if (r?.type !== MT.PO) { close(); return null; }
    [r, ex] = await readStun(cr, ex);
    if (r?.type !== MT.CO || !r.attrs[AT.CONNID]) { close(); return null; }
    await data.opened;
    const dw = data.writable.getWriter(), dr = data.readable.getReader();
    await dw.write(await sign(stunMsg(MT.BQ, randomTID(), [stunAttr(AT.CONNID, r.attrs[AT.CONNID]), ...aa])));
    let extra;
    [r, extra] = await readStun(dr);
    if (r?.type !== MT.BO) { close(); return null; }
    cr.releaseLock(); cw.releaseLock(); dw.releaseLock();
    const readable = new ReadableStream({
      start: c => { if (extra?.length) c.enqueue(extra); },
      pull: c => dr.read().then(({ done, value }) => done ? c.close() : c.enqueue(new Uint8Array(value))),
      cancel: () => { try { dr.cancel(); } catch {} },
    });
    return { readable, writable: data.writable, close };
  } catch { close(); return null; }
}

// ============================================================
//  TURN UDP Relay + XUDP (RFC 5766 / XUDP)
// ============================================================
function encodeAddr(h) {
  const s = stripBrackets(h);
  const m = s.match(/^(\d+)\.(\d+)\.(\d+)\.(\d+)$/);
  if (m) return new Uint8Array([0x01, ...m.slice(1).map(Number)]);
  if (s.includes(':')) {
    const b = new Uint8Array(17); b[0] = 0x03;
    s.split(':').forEach((x, i) => {
      const v = parseInt(x, 16) || 0;
      b[1 + i * 2] = v >> 8; b[2 + i * 2] = v & 0xff;
    });
    return b;
  }
  const e = enc(s);
  return cat(new Uint8Array([0x02, e.length]), e);
}
function xudpAddr(d) {
  if (!d.length) return ['', 0];
  if (d[0] <= 1) return d.length >= 5 ? [d.subarray(1, 5).join('.'), 5] : ['', 0];
  if (d[0] === 2) return d.length >= 2 + d[1] ? [dec.decode(d.subarray(2, 2 + d[1])), 2 + d[1]] : ['', 0];
  return d[0] === 3 && d.length >= 17 ? [`[${Array.from({ length: 8 }, (_, i) => u16(d, 1 + i * 2).toString(16)).join(':')}]`, 17] : ['', 0];
}
function fakeIPType(h) {
  const m = h.match(/^(\d+)\.(\d+)\.(\d+)\.(\d+)$/);
  if (m && +m[1] === 198 && [18, 19].includes(+m[2])) return 4;
  return stripBrackets(h).startsWith('fc') && h.includes(':') ? 6 : 0;
}
function parseXUDP(d) {
  if (d.length < 6) return null;
  const metaLen = u16(d), metaEnd = 2 + metaLen;
  if (metaLen < 4 || metaEnd > d.length) return null;
  const f = {
    network: metaEnd > 6 ? d[6] : 0,
    port: metaEnd >= 9 ? u16(d, 7) : 0,
    host: metaEnd > 9 ? xudpAddr(d.subarray(9, metaEnd))[0] : '',
    payload: null, totalLen: metaEnd,
  };
  if ((d[5] & 1) && metaEnd + 2 <= d.length) {
    const pLen = u16(d, metaEnd);
    if (metaEnd + 2 + pLen <= d.length) {
      f.payload = d.subarray(metaEnd + 2, metaEnd + 2 + pLen);
      f.totalLen = metaEnd + 2 + pLen;
    }
  }
  return f;
}
function xudpResp(host, port, payload) {
  const a = encodeAddr(host);
  const ml = 7 + a.length;
  const buf = new Uint8Array(2 + ml + 2 + payload.length);
  [buf[0], buf[1], buf[4], buf[5], buf[6], buf[7], buf[8]] =
    [ml >> 8, ml & 0xff, 2, 1, 2, port >> 8, port & 0xff];
  buf.set(a, 9);
  const pOff = 2 + ml;
  [buf[pOff], buf[pOff + 1]] = [payload.length >> 8, payload.length & 0xff];
  buf.set(payload, pOff + 2);
  return buf;
}

async function turnUDPRelay({ host, port, user, pass }, sendWs) {
  let sock = null, closed = false;
  const perms = new Set(), sess = new Map(), reverse = {};
  const close = () => { closed = true; safeClose(sock); };
  try {
    sock = connect({ hostname: host, port });
    await sock.opened;
    const w = sock.writable.getWriter(), r = sock.readable.getReader();
    const auth = await turnAuth(w, r, 17, { user, pass });
    if (!auth) { close(); return null; }
    const { aa, sign } = auth;
    let buf = auth.ex;
    // 接收循环：DataIndication -> XUDP 响应
    (async () => {
      while (!closed) {
        const [m, nx] = await readStun(r, buf);
        buf = nx;
        if (!m) break;
        if (m.type === MT.DI && m.attrs[AT.PEER] && m.attrs[AT.DATA]) {
          const [ip, pt] = parseXorPeer(m.attrs[AT.PEER]);
          const s = reverse[`${ip}:${pt}`];
          sendWs(xudpResp(s?.host ?? ip, s?.port ?? pt, m.attrs[AT.DATA]));
        }
      }
    })();
    const ensurePerm = ip => {
      if (perms.has(ip)) return;
      perms.add(ip);
      sign(stunMsg(MT.PQ, randomTID(), [stunAttr(AT.PEER, xorPeer(ip, 0)), ...aa])).then(m => w.write(m));
    };
    const sendUDP = (ip, port, data) =>
      w.write(stunMsg(MT.SI, randomTID(), [stunAttr(AT.PEER, xorPeer(ip, port)), stunAttr(AT.DATA, data)]));
    const getIP = (h, p) => {
      const k = `${h}:${p}`, c = sess.get(k);
      if (c) return c.ip;
      const ft = fakeIPType(h);
      if (ft) for (const s of sess.values()) {
        if (s.port === p && s.isV6 === (ft === 6)) {
          const ns = { ip: s.ip, host: h, port: p, isV6: s.isV6 };
          sess.set(k, ns); reverse[`${s.ip}:${p}`] = ns;
          return s.ip;
        }
      }
      return null;
    };
    const resolveAsync = async (h, p, k) => {
      const ip = await resolveIP(h);
      if (ip) {
        const s = { ip, host: h, port: p, isV6: ip.includes(':') };
        sess.set(k, s); reverse[`${ip}:${p}`] = s;
      }
    };
    const processXUDP = data => {
      while (data.length >= 6) {
        const f = parseXUDP(data);
        if (!f) break;
        if (f.network === 2 && f.payload?.length && f.host) {
          const k = `${f.host}:${f.port}`;
          const ip = getIP(f.host, f.port);
          if (ip) { ensurePerm(ip); sendUDP(ip, f.port, f.payload); }
          else if (!sess.has(k)) resolveAsync(f.host, f.port, k);
        }
        data = data.subarray(f.totalLen);
      }
    };
    return { processXUDP, close };
  } catch { close(); return null; }
}

// ============================================================
//  内置 TURN 节点池 (从 turn_results.txt 精选全球 ALL 模式节点)
// ============================================================
const BUILTIN_TURN_NODES = [
  // 亚洲
  { host: '47.99.58.9', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.6.3' },
  { host: '47.97.39.31', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '47.93.45.25', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: '' },
  { host: '8.131.78.90', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.5.1.2' },
  { host: '39.97.23.22', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '39.98.86.59', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '106.55.6.89', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '120.55.3.168', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '42.192.43.33', port: 3478, user: '', pass: '', country: '中国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '47.83.122.49', port: 3478, user: '', pass: '', country: '香港', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '47.86.169.21', port: 3478, user: '', pass: '', country: '香港', mode: 'ALL', sw: 'Coturn-4.5.1.2' },
  { host: '103.50.252.19', port: 3478, user: '', pass: '', country: '香港', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '133.28.25.48', port: 3478, user: '', pass: '', country: '日本', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '13.209.67.50', port: 3478, user: '', pass: '', country: '韩国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '110.4.40.110', port: 3478, user: '', pass: '', country: '马来西亚', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '43.159.38.237', port: 3478, user: '', pass: '', country: '新加坡', mode: 'ALL', sw: 'Coturn-4.5.1.1' },
  { host: '47.84.1.64', port: 3478, user: '', pass: '', country: '新加坡', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '8.222.203.196', port: 3478, user: '', pass: '', country: '新加坡', mode: 'ALL', sw: 'Coturn-4.5.1.2' },
  { host: '18.143.94.83', port: 3478, user: '', pass: '', country: '新加坡', mode: 'ALL', sw: 'Coturn-4.5.1.2' },
  { host: '103.162.1.118', port: 3478, user: '', pass: '', country: '印度尼西亚', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '58.97.196.21', port: 3478, user: '', pass: '', country: '柬埔寨', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '113.23.35.22', port: 3478, user: '', pass: '', country: '越南', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '3.26.25.12', port: 3478, user: '', pass: '', country: '澳大利亚', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '203.12.0.153', port: 3478, user: '', pass: '', country: '澳大利亚', mode: 'ALL', sw: '' },
  // 欧洲
  { host: '5.9.65.38', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '49.12.3.77', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '5.9.96.209', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '78.46.83.79', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.3' },
  { host: '3.70.224.86', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '94.16.105.13', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '89.58.26.249', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '78.46.237.227', port: 3478, user: '', pass: '', country: '德国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '94.23.23.10', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '87.98.159.3', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '54.37.81.111', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '212.47.71.78', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '37.59.151.194', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '188.165.76.14', port: 3478, user: '', pass: '', country: '法国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '5.78.22.159', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '195.80.16.8', port: 3478, user: '', pass: '', country: '英国', mode: 'ALL', sw: '' },
  { host: '80.6.96.142', port: 3478, user: '', pass: '', country: '英国', mode: 'ALL', sw: '' },
  { host: '217.28.19.25', port: 3478, user: '', pass: '', country: '英国', mode: 'ALL', sw: 'Coturn-4.5.1.3' },
  { host: '5.61.218.88', port: 3478, user: '', pass: '', country: '意大利', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '5.133.114.21', port: 3478, user: '', pass: '', country: '意大利', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '65.21.105.78', port: 3478, user: '', pass: '', country: '芬兰', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '34.51.157.43', port: 3478, user: '', pass: '', country: '瑞典', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '45.83.222.99', port: 3478, user: '', pass: '', country: '瑞典', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '37.205.8.43', port: 3478, user: '', pass: '', country: '捷克', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '217.60.1.253', port: 3478, user: '', pass: '', country: '拉脱维亚', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '195.2.70.36', port: 3478, user: '', pass: '', country: '俄罗斯', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '45.12.4.226', port: 3478, user: '', pass: '', country: '俄罗斯', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '82.202.173.6', port: 3478, user: '', pass: '', country: '俄罗斯', mode: 'ALL', sw: 'Coturn-4.6.1' },
  // 美洲
  { host: '34.80.79.85', port: 80, user: 'test', pass: '1234', country: '台湾', mode: 'ALL', sw: 'None' },
  { host: '34.67.13.92', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '54.237.42.1', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.1.1' },
  { host: '52.10.14.24', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '45.79.168.64', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '138.197.9.41', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.0.5' },
  { host: '40.90.203.59', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '34.74.106.63', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '34.138.28.255', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '54.189.233.49', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '154.17.29.151', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '15.200.89.199', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.6.2' },
  { host: '164.92.64.201', port: 3478, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '69.28.51.142', port: 3479, user: '', pass: '', country: '美国', mode: 'ALL', sw: 'None' },
  { host: '158.69.34.65', port: 3478, user: '', pass: '', country: '加拿大', mode: 'ALL', sw: 'Coturn-4.5.1.1' },
  { host: '199.58.81.158', port: 3478, user: '', pass: '', country: '加拿大', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '15.235.29.175', port: 3478, user: '', pass: '', country: '加拿大', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '190.8.18.8', port: 3478, user: '', pass: '', country: '巴西', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '138.204.96.6', port: 3478, user: '', pass: '', country: '巴西', mode: 'ALL', sw: 'Coturn-4.5.2' },
  // 非洲/中东
  { host: '41.76.110.231', port: 3478, user: '', pass: '', country: '南非', mode: 'ALL', sw: 'Coturn-4.5.2' },
  { host: '195.142.6.170', port: 3478, user: '', pass: '', country: '土耳其', mode: 'ALL', sw: 'Coturn-4.5.1.1' },
  { host: '34.47.252.6', port: 3478, user: '', pass: '', country: '印度', mode: 'ALL', sw: 'Coturn-4.6.1' },
  { host: '3.6.151.176', port: 3478, user: '', pass: '', country: '印度', mode: 'ALL', sw: 'Coturn-4.5.1.1' },
  { host: '52.66.233.75', port: 3478, user: '', pass: '', country: '印度', mode: 'ALL', sw: 'Coturn-4.6.1' },
];

// 节点池运行时状态
let nodePool = null;
let roundRobinIdx = 0;

async function initNodePool(env) {
  if (nodePool) return nodePool;
  try {
    const saved = await env.KV?.get('turn_nodes.json');
    if (saved) {
      nodePool = JSON.parse(saved);
    } else {
      nodePool = BUILTIN_TURN_NODES.map((n, i) => ({ ...n, id: `builtin_${i}`, enabled: true, latency: null }));
      await env.KV?.put('turn_nodes.json', JSON.stringify(nodePool));
    }
  } catch {
    nodePool = BUILTIN_TURN_NODES.map((n, i) => ({ ...n, id: `builtin_${i}`, enabled: true, latency: null }));
  }
  return nodePool;
}

function getEnabledNodes() {
  return (nodePool || []).filter(n => n.enabled);
}

// 轮询获取下一个节点
function getNextNodeRR() {
  const nodes = getEnabledNodes();
  if (!nodes.length) return null;
  const n = nodes[roundRobinIdx % nodes.length];
  roundRobinIdx++;
  return n;
}

// 随机获取节点
function getRandomNode() {
  const nodes = getEnabledNodes();
  if (!nodes.length) return null;
  return nodes[Math.floor(Math.random() * nodes.length)];
}

function nodeToTurnURL(n) {
  const cred = n.user && n.pass ? `${encodeURIComponent(n.user)}:${encodeURIComponent(n.pass)}@` : '';
  return `turn://${cred}${n.host}:${n.port}`;
}

// ============================================================
//  配置管理 (KV)
// ============================================================
async function loadConfig(env, host, userID) {
  const defaults = {
    TIME: new Date().toISOString(),
    HOST: host,
    UUID: userID,
    PATH: '/',
    Fingerprint: 'chrome',
    SUBNAME: 'TURN-Worker',
    SUBUpdateTime: 3,
    pollStrategy: 'roundrobin', // roundrobin | random | fixed
    fixedNodeId: null,
    subNodeCount: 10,
    enableUDP: true,
    enableXUDP: true,
    ADMIN: env.ADMIN || env.PASSWORD || env.admin || env.password || '',
  };
  try {
    const saved = await env.KV?.get('config.json');
    if (saved) {
      const cfg = JSON.parse(saved);
      return { ...defaults, ...cfg, HOST: host, UUID: userID };
    }
  } catch {}
  return defaults;
}

async function saveConfig(env, cfg) {
  await env.KV?.put('config.json', JSON.stringify(cfg, null, 2));
}

// ============================================================
//  订阅生成
// ============================================================
function generateVLESSLink(cfg, node, workerHost) {
  const turnPath = `/turn://${node.user && node.pass ? `${encodeURIComponent(node.user)}:${encodeURIComponent(node.pass)}@` : ''}${node.host}:${node.port}?ed=2560`;
  const path = encodeURIComponent((cfg.PATH === '/' ? '' : cfg.PATH) + turnPath);
  const remark = encodeURIComponent(`${cfg.SUBNAME}-${node.country || node.host}-${node.host}`);
  return `vless://${cfg.UUID}@${workerHost}:443?encryption=none&security=tls&sni=${workerHost}&fp=${cfg.Fingerprint}&type=ws&host=${workerHost}&path=${path}&packetEncoding=xudp#${remark}`;
}

function generateSubscription(cfg, workerHost, count) {
  const nodes = getEnabledNodes();
  if (!nodes.length) return '';
  const n = Math.min(count || cfg.subNodeCount || 10, nodes.length);
  const links = [];
  if (cfg.pollStrategy === 'random') {
    const shuffled = [...nodes].sort(() => Math.random() - 0.5);
    for (let i = 0; i < n; i++) links.push(generateVLESSLink(cfg, shuffled[i], workerHost));
  } else if (cfg.pollStrategy === 'fixed' && cfg.fixedNodeId) {
    const fn = nodes.find(x => x.id === cfg.fixedNodeId) || nodes[0];
    for (let i = 0; i < n; i++) links.push(generateVLESSLink(cfg, fn, workerHost));
  } else {
    // roundrobin
    for (let i = 0; i < n; i++) {
      const node = nodes[(roundRobinIdx + i) % nodes.length];
      links.push(generateVLESSLink(cfg, node, workerHost));
    }
    roundRobinIdx = (roundRobinIdx + n) % nodes.length;
  }
  return links.join('\n');
}

// ============================================================
//  WebSocket 代理处理
// ============================================================
async function relayPipe(rd, send, close) {
  try {
    for (;;) {
      const { done, value } = await rd.read();
      if (done) break;
      if (value?.byteLength) send(value);
    }
  } catch {} finally {
    try { rd.releaseLock(); } catch {}
    close();
  }
}

async function handleWS(req, env, cfg) {
  const [client, server] = Object.values(new WebSocketPair());
  server.accept();
  const ed = req.headers.get('sec-websocket-protocol');
  const turn = parseTurnURL(req.url);
  let w = null, sock = null, udp = null, chain = Promise.resolve();
  const close = () => { udp?.close(); safeClose(sock, server); };
  const send = d => { try { server.send(d); } catch {} };

  const process = async chunk => {
    if (w) return w.write(chunk);
    if (udp) return udp.processXUDP(chunk);
    const ack = () => send(new Uint8Array([chunk[0], 0]));
    // UDP / XUDP
    const u = isVLESSUDP(chunk);
    if (u && turn && cfg.enableUDP) {
      ack();
      udp = await turnUDPRelay(turn, send);
      if (!udp) return close();
      const ud = chunk.subarray(u.dataOffset);
      if (ud.length) udp.processXUDP(ud);
      return;
    }
    // TCP
    const v = parseVLESS(chunk);
    if (!v) return close();
    ack();
    const { addrType, addrBytes, dataOffset, port } = v;
    const host = addrStr(addrType, addrBytes);
    const payload = chunk.subarray(dataOffset);
    if (turn) {
      const ip = addrType === 1 ? host : await resolveIP(host);
      if (!ip) return close();
      sock = await turnTCPConn(turn, ip, port).catch(() => null);
      if (!sock) return close();
    } else {
      try {
        sock = connect({ hostname: host, port });
        await sock.opened;
      } catch { return close(); }
    }
    w = sock.writable.getWriter();
    if (payload.byteLength) await w.write(payload);
    relayPipe(sock.readable.getReader(), send, close);
  };

  if (ed?.length <= MAX_ED) {
    chain = chain.then(() => process(Uint8Array.fromBase64(ed, { alphabet: 'base64url' }))).catch(close);
  }
  server.addEventListener('message', e => {
    chain = chain.then(() => process(new Uint8Array(e.data instanceof ArrayBuffer ? e.data : e.data.buffer ?? e.data))).catch(close);
  });
  server.addEventListener('close', close);
  server.addEventListener('error', close);
  return new Response(null, {
    status: 101,
    webSocket: client,
    headers: ed ? { 'sec-websocket-protocol': ed } : {},
  });
}

// ============================================================
//  节点连通性测试
// ============================================================
async function testTurnNode(node) {
  const start = Date.now();
  try {
    const sock = connect({ hostname: node.host, port: node.port });
    await sock.opened;
    const w = sock.writable.getWriter(), r = sock.readable.getReader();
    const auth = await turnAuth(w, r, 6, { user: node.user, pass: node.pass });
    safeClose(sock);
    if (auth) return { ok: true, latency: Date.now() - start };
    return { ok: false, latency: Date.now() - start, error: 'auth failed' };
  } catch (e) {
    return { ok: false, latency: Date.now() - start, error: e.message };
  }
}

// ============================================================
//  Vue3 + Element Plus 管理面板 HTML
// ============================================================
const ADMIN_HTML = `<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1.0">
<title>TURN Worker 管理面板</title>
<link rel="stylesheet" href="https://unpkg.com/element-plus@2.7.6/dist/index.css">
<script src="https://unpkg.com/vue@3.4.38/dist/vue.global.prod.js"></script>
<script src="https://unpkg.com/element-plus@2.7.6/dist/index.full.min.js"></script>
<script src="https://unpkg.com/@element-plus/icons-vue@2.3.1/dist/index.iife.min.js"></script>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;background:#f0f2f5;min-height:100vh}
#app{min-height:100vh}
.login-wrap{display:flex;align-items:center;justify-content:center;min-height:100vh;background:linear-gradient(135deg,#667eea 0%,#764ba2 100%)}
.login-card{width:380px;padding:40px;background:#fff;border-radius:12px;box-shadow:0 20px 60px rgba(0,0,0,.15)}
.login-card h2{text-align:center;margin-bottom:28px;color:#333;font-size:22px}
.layout{display:flex;min-height:100vh}
.sidebar{width:220px;background:#001529;color:#fff;flex-shrink:0}
.sidebar .logo{height:60px;display:flex;align-items:center;justify-content:center;font-size:18px;font-weight:bold;color:#fff;border-bottom:1px solid rgba(255,255,255,.1)}
.sidebar .el-menu{border-right:none}
.main{flex:1;display:flex;flex-direction:column}
.header{height:60px;background:#fff;display:flex;align-items:center;justify-content:space-between;padding:0 24px;box-shadow:0 1px 4px rgba(0,0,0,.08)}
.header .title{font-size:18px;font-weight:600;color:#333}
.content{flex:1;padding:24px;overflow-y:auto}
.stat-card{text-align:center;padding:20px;border-radius:8px;background:#fff;box-shadow:0 2px 12px rgba(0,0,0,.06)}
.stat-card .num{font-size:32px;font-weight:700;color:#409eff}
.stat-card .label{color:#909399;font-size:14px;margin-top:8px}
.card{background:#fff;border-radius:8px;padding:20px;box-shadow:0 2px 12px rgba(0,0,0,.06);margin-bottom:20px}
.card h3{margin-bottom:16px;font-size:16px;color:#333}
.link-box{background:#f5f7fa;padding:12px;border-radius:6px;font-family:monospace;font-size:12px;word-break:break-all;max-height:200px;overflow-y:auto}
.tag-ok{color:#67c23a}.tag-fail{color:#f56c6c}.tag-warn{color:#e6a23c}
</style>
</head>
<body>
<div id="app">
<!-- 登录页 -->
<div v-if="!logged" class="login-wrap">
  <div class="login-card">
    <h2>TURN Worker 管理面板</h2>
    <el-form @submit.prevent="doLogin">
      <el-form-item>
        <el-input v-model="loginPwd" type="password" placeholder="管理员密码" show-password size="large" @keyup.enter="doLogin"></el-input>
      </el-form-item>
      <el-button type="primary" style="width:100%" size="large" @click="doLogin" :loading="logging">登 录</el-button>
    </el-form>
  </div>
</div>
<!-- 主布局 -->
<div v-else class="layout">
  <div class="sidebar">
    <div class="logo">TURN Worker</div>
    <el-menu :default-active="activeTab" background-color="#001529" text-color="rgba(255,255,255,.7)" active-text-color="#fff" @select="activeTab=$event">
      <el-menu-item index="dashboard"><el-icon><Odometer/></el-icon><span>仪表盘</span></el-menu-item>
      <el-menu-item index="nodes"><el-icon><Connection/></el-icon><span>TURN 节点</span></el-menu-item>
      <el-menu-item index="sub"><el-icon><Link/></el-icon><span>订阅管理</span></el-menu-item>
      <el-menu-item index="config"><el-icon><Setting/></el-icon><span>系统配置</span></el-menu-item>
    </el-menu>
  </div>
  <div class="main">
    <div class="header">
      <span class="title">{{ pageTitle }}</span>
      <el-button type="danger" size="small" @click="doLogout">退出登录</el-button>
    </div>
    <div class="content">
      <!-- 仪表盘 -->
      <div v-if="activeTab==='dashboard'">
        <el-row :gutter="20">
          <el-col :span="6"><div class="stat-card"><div class="num">{{config.UUID?.substring(0,8)}}...</div><div class="label">UUID</div></div></el-col>
          <el-col :span="6"><div class="stat-card"><div class="num">{{nodes.length}}</div><div class="label">节点总数</div></div></el-col>
          <el-col :span="6"><div class="stat-card"><div class="num">{{enabledCount}}</div><div class="label">启用节点</div></div></el-col>
          <el-col :span="6"><div class="stat-card"><div class="num">{{config.subNodeCount}}</div><div class="label">订阅节点数</div></div></el-col>
        </el-row>
        <div class="card" style="margin-top:20px">
          <h3>Worker 信息</h3>
          <el-descriptions :column="2" border>
            <el-descriptions-item label="版本">${VERSION}</el-descriptions-item>
            <el-descriptions-item label="主机">{{config.HOST}}</el-descriptions-item>
            <el-descriptions-item label="路径">{{config.PATH}}</el-descriptions-item>
            <el-descriptions-item label="轮询策略">{{strategyText}}</el-descriptions-item>
            <el-descriptions-item label="UDP">{{config.enableUDP?'启用':'禁用'}}</el-descriptions-item>
            <el-descriptions-item label="XUDP">{{config.enableXUDP?'启用':'禁用'}}</el-descriptions-item>
          </el-descriptions>
        </div>
        <div class="card">
          <h3>快速操作</h3>
          <el-button type="primary" @click="activeTab='nodes'">管理节点</el-button>
          <el-button type="success" @click="activeTab='sub'">查看订阅</el-button>
          <el-button type="warning" @click="testAllNodes">测试全部节点</el-button>
        </div>
      </div>
      <!-- 节点管理 -->
      <div v-if="activeTab==='nodes'">
        <div class="card">
          <div style="display:flex;justify-content:space-between;margin-bottom:16px">
            <h3 style="margin:0">TURN 节点列表 ({{nodes.length}})</h3>
            <div>
              <el-button type="primary" size="small" @click="showAddDialog=true">添加节点</el-button>
              <el-button type="success" size="small" @click="testAllNodes">测试全部</el-button>
              <el-button type="danger" size="small" @click="resetNodes">重置内置</el-button>
            </div>
          </div>
          <el-table :data="nodes" stripe size="small" max-height="500">
            <el-table-column prop="host" label="地址" width="160"></el-table-column>
            <el-table-column prop="port" label="端口" width="70"></el-table-column>
            <el-table-column prop="country" label="地区" width="90"></el-table-column>
            <el-table-column prop="mode" label="模式" width="70">
              <template #default="s"><el-tag size="small" :type="s.row.mode==='ALL'?'success':'info'">{{s.row.mode}}</el-tag></template>
            </el-table-column>
            <el-table-column label="认证" width="100">
              <template #default="s">{{s.row.user?'凭据':'无认证'}}</template>
            </el-table-column>
            <el-table-column label="延迟" width="90">
              <template #default="s">
                <span v-if="s.row.latency!=null" :class="s.row.latency<500?'tag-ok':s.row.latency<1500?'tag-warn':'tag-fail'">{{s.row.latency}}ms</span>
                <span v-else class="tag-warn">未测</span>
              </template>
            </el-table-column>
            <el-table-column label="状态" width="80">
              <template #default="s"><el-switch v-model="s.row.enabled" @change="saveNodes"></el-switch></template>
            </el-table-column>
            <el-table-column label="操作" width="160">
              <template #default="s">
                <el-button size="small" @click="testOne(s.row)">测试</el-button>
                <el-button size="small" type="danger" @click="delNode(s.row)">删除</el-button>
              </template>
            </el-table-column>
          </el-table>
        </div>
        <!-- 添加节点对话框 -->
        <el-dialog v-model="showAddDialog" title="添加 TURN 节点" width="500px">
          <el-form :model="newNode" label-width="80px">
            <el-form-item label="主机"><el-input v-model="newNode.host" placeholder="如 1.2.3.4"></el-input></el-form-item>
            <el-form-item label="端口"><el-input-number v-model="newNode.port" :min="1" :max="65535"></el-input-number></el-form-item>
            <el-form-item label="用户名"><el-input v-model="newNode.user" placeholder="无认证留空"></el-input></el-form-item>
            <el-form-item label="密码"><el-input v-model="newNode.pass" type="password" show-password></el-input></el-form-item>
            <el-form-item label="地区"><el-input v-model="newNode.country"></el-input></el-form-item>
            <el-form-item label="模式">
              <el-select v-model="newNode.mode"><el-option label="ALL(TCP+UDP)" value="ALL"></el-option><el-option label="TCP" value="TCP"></el-option><el-option label="UDP" value="UDP"></el-option></el-select>
            </el-form-item>
          </el-form>
          <template #footer>
            <el-button @click="showAddDialog=false">取消</el-button>
            <el-button type="primary" @click="addNode">添加</el-button>
          </template>
        </el-dialog>
      </div>
      <!-- 订阅管理 -->
      <div v-if="activeTab==='sub'">
        <div class="card">
          <h3>订阅链接</h3>
          <p style="color:#909399;margin-bottom:12px;font-size:13px">将以下链接导入 v2rayN / Clash / Sing-box 等客户端，支持 TURN 节点轮询。</p>
          <div class="link-box">{{subURL}}</div>
          <div style="margin-top:12px">
            <el-button type="primary" size="small" @click="copyText(subURL)">复制订阅链接</el-button>
            <el-button type="success" size="small" @click="previewSub">预览节点</el-button>
          </div>
        </div>
        <div class="card" v-if="subPreview">
          <h3>订阅预览 ({{subPreview.split('\\n').length}} 个节点)</h3>
          <div class="link-box" style="max-height:300px">{{subPreview}}</div>
        </div>
        <div class="card">
          <h3>单节点直连链接</h3>
          <el-table :data="nodes.filter(n=>n.enabled).slice(0,20)" size="small" max-height="300">
            <el-table-column prop="country" label="地区" width="90"></el-table-column>
            <el-table-column prop="host" label="TURN服务器" width="150"></el-table-column>
            <el-table-column label="VLESS链接">
              <template #default="s">
                <span style="font-family:monospace;font-size:11px;word-break:break-all">{{singleLink(s.row)}}</span>
              </template>
            </el-table-column>
            <el-table-column label="操作" width="80">
              <template #default="s"><el-button size="small" @click="copyText(singleLink(s.row))">复制</el-button></template>
            </el-table-column>
          </el-table>
        </div>
      </div>
      <!-- 系统配置 -->
      <div v-if="activeTab==='config'">
        <div class="card">
          <h3>基础配置</h3>
          <el-form :model="config" label-width="120px" style="max-width:600px">
            <el-form-item label="UUID"><el-input v-model="config.UUID"></el-input></el-form-item>
            <el-form-item label="WebSocket路径"><el-input v-model="config.PATH"></el-input></el-form-item>
            <el-form-item label="TLS指纹"><el-input v-model="config.Fingerprint"></el-input></el-form-item>
            <el-form-item label="订阅名称"><el-input v-model="config.SUBNAME"></el-input></el-form-item>
            <el-form-item label="订阅更新间隔(小时)"><el-input-number v-model="config.SUBUpdateTime" :min="1" :max="24"></el-input-number></el-form-item>
          </el-form>
        </div>
        <div class="card">
          <h3>TURN 轮询配置</h3>
          <el-form :model="config" label-width="120px" style="max-width:600px">
            <el-form-item label="轮询策略">
              <el-select v-model="config.pollStrategy">
                <el-option label="轮询 (Round-Robin)" value="roundrobin"></el-option>
                <el-option label="随机 (Random)" value="random"></el-option>
                <el-option label="固定节点" value="fixed"></el-option>
              </el-select>
            </el-form-item>
            <el-form-item label="固定节点" v-if="config.pollStrategy==='fixed'">
              <el-select v-model="config.fixedNodeId" placeholder="选择节点">
                <el-option v-for="n in nodes.filter(x=>x.enabled)" :key="n.id" :label="n.country+' - '+n.host" :value="n.id"></el-option>
              </el-select>
            </el-form-item>
            <el-form-item label="订阅节点数"><el-input-number v-model="config.subNodeCount" :min="1" :max="100"></el-input-number></el-form-item>
            <el-form-item label="启用 UDP"><el-switch v-model="config.enableUDP"></el-switch></el-form-item>
            <el-form-item label="启用 XUDP"><el-switch v-model="config.enableXUDP"></el-switch></el-form-item>
          </el-form>
        </div>
        <div class="card">
          <el-button type="primary" @click="saveConfig" :loading="savingCfg">保存配置</el-button>
          <el-button type="danger" @click="resetConfig">重置配置</el-button>
        </div>
      </div>
    </div>
  </div>
</div>
</div>
<script>
const { createApp, ref, computed, onMounted } = Vue;
const app = createApp({
  setup() {
    const logged = ref(false);
    const logging = ref(false);
    const loginPwd = ref('');
    const activeTab = ref('dashboard');
    const config = ref({});
    const nodes = ref([]);
    const showAddDialog = ref(false);
    const savingCfg = ref(false);
    const subPreview = ref('');
    const newNode = ref({ host:'', port:3478, user:'', pass:'', country:'', mode:'ALL' });

    const pageTitle = computed(() => ({dashboard:'仪表盘',nodes:'TURN 节点管理',sub:'订阅管理',config:'系统配置'}[activeTab.value]||''));
    const enabledCount = computed(() => nodes.value.filter(n=>n.enabled).length);
    const strategyText = computed(() => ({roundrobin:'轮询',random:'随机',fixed:'固定节点'}[config.value.pollStrategy]||''));
    const subURL = computed(() => location.origin + '/sub?token=' + (config.value.subToken||''));

    async function api(path, opts) {
      const r = await fetch(path, opts);
      return r.json();
    }
    async function doLogin() {
      if (!loginPwd.value) return ElementPlus.ElMessage.warning('请输入密码');
      logging.value = true;
      try {
        const r = await fetch('/login', { method:'POST', headers:{'Content-Type':'application/x-www-form-urlencoded'}, body:'password='+encodeURIComponent(loginPwd.value) });
        const d = await r.json();
        if (d.success) { logged.value = true; await loadAll(); }
        else ElementPlus.ElMessage.error('密码错误');
      } catch(e) { ElementPlus.ElMessage.error('登录失败'); }
      logging.value = false;
    }
    function doLogout() { fetch('/logout').then(()=>{ logged.value=false; loginPwd.value=''; }); }
    async function loadAll() {
      const [c, n] = await Promise.all([api('/admin/api/config'), api('/admin/api/nodes')]);
      config.value = c; nodes.value = n.nodes || [];
    }
    async function saveNodes() { await api('/admin/api/nodes', {method:'PUT', headers:{'Content-Type':'application/json'}, body:JSON.stringify({nodes:nodes.value})}); }
    async function addNode() {
      if (!newNode.value.host) return ElementPlus.ElMessage.warning('请输入主机');
      const n = {...newNode.value, id:'custom_'+Date.now(), enabled:true, latency:null};
      nodes.value.push(n); await saveNodes();
      showAddDialog.value=false; newNode.value={host:'',port:3478,user:'',pass:'',country:'',mode:'ALL'};
      ElementPlus.ElMessage.success('添加成功');
    }
    function delNode(n) {
      ElementPlus.ElMessageBox.confirm('确认删除节点 '+n.host+'?','提示',{type:'warning'}).then(async()=>{
        nodes.value = nodes.value.filter(x=>x.id!==n.id); await saveNodes();
        ElementPlus.ElMessage.success('已删除');
      }).catch(()=>{});
    }
    async function testOne(n) {
      ElementPlus.ElMessage.info('测试中...');
      const r = await api('/admin/api/nodes/'+encodeURIComponent(n.id)+'/test', {method:'POST'});
      n.latency = r.latency;
      if (r.ok) ElementPlus.ElMessage.success('连通 '+r.latency+'ms');
      else ElementPlus.ElMessage.error('连接失败: '+(r.error||''));
      await saveNodes();
    }
    async function testAllNodes() {
      ElementPlus.ElMessage.info('开始批量测试...');
      for (const n of nodes.value) {
        if (!n.enabled) continue;
        const r = await api('/admin/api/nodes/'+encodeURIComponent(n.id)+'/test', {method:'POST'});
        n.latency = r.latency;
      }
      await saveNodes();
      ElementPlus.ElMessage.success('测试完成');
    }
    async function resetNodes() {
      ElementPlus.ElMessageBox.confirm('将重置为内置节点池，自定义节点将丢失','提示',{type:'warning'}).then(async()=>{
        const r = await api('/admin/api/nodes/reset', {method:'POST'});
        nodes.value = r.nodes; ElementPlus.ElMessage.success('已重置');
      }).catch(()=>{});
    }
    async function previewSub() {
      const r = await fetch('/sub?token='+(config.value.subToken||'')+'&preview=1');
      subPreview.value = await r.text();
    }
    function singleLink(n) {
      const cred = n.user&&n.pass?encodeURIComponent(n.user)+':'+encodeURIComponent(n.pass)+'@':'';
      const path = encodeURIComponent((config.value.PATH==='/'?'':config.value.PATH)+'/turn://'+cred+n.host+':'+n.port+'?ed=2560');
      return 'vless://'+config.value.UUID+'@'+config.value.HOST+':443?encryption=none&security=tls&sni='+config.value.HOST+'&fp='+config.value.Fingerprint+'&type=ws&host='+config.value.HOST+'&path='+path+'&packetEncoding=xudp#'+encodeURIComponent(config.value.SUBNAME+'-'+n.country);
    }
    function copyText(t) {
      navigator.clipboard.writeText(t).then(()=>ElementPlus.ElMessage.success('已复制')).catch(()=>ElementPlus.ElMessage.error('复制失败'));
    }
    async function saveConfig() {
      savingCfg.value = true;
      const r = await api('/admin/api/config', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(config.value)});
      if (r.success) { ElementPlus.ElMessage.success('配置已保存'); await loadAll(); }
      else ElementPlus.ElMessage.error('保存失败');
      savingCfg.value = false;
    }
    async function resetConfig() {
      ElementPlus.ElMessageBox.confirm('确认重置为默认配置?','提示',{type:'warning'}).then(async()=>{
        await api('/admin/api/config/reset',{method:'POST'}); await loadAll(); ElementPlus.ElMessage.success('已重置');
      }).catch(()=>{});
    }
    onMounted(async()=>{
      const r = await fetch('/admin/api/config').catch(()=>null);
      if (r && r.ok) { const d = await r.json(); if (d.UUID) { logged.value=true; config.value=d; await loadAll(); } }
    });
    return { logged,logging,loginPwd,activeTab,config,nodes,showAddDialog,newNode,savingCfg,subPreview,pageTitle,enabledCount,strategyText,subURL,doLogin,doLogout,saveNodes,addNode,delNode,testOne,testAllNodes,resetNodes,previewSub,singleLink,copyText,saveConfig,resetConfig };
  }
});
app.use(ElementPlus);
for (const [key, comp] of Object.entries(ElementPlusIconsVue)) app.component(key, comp);
app.mount('#app');
</script>
</body>
</html>`;

// ============================================================
//  认证中间件
// ============================================================
async function checkAuth(request, env, cfg) {
  const cookies = request.headers.get('Cookie') || '';
  const authCookie = cookies.split(';').find(c => c.trim().startsWith('auth='))?.split('=')[1];
  const UA = request.headers.get('User-Agent') || '';
  const expected = await md5md5(UA + cfg.ADMIN);
  return authCookie === expected;
}

// ============================================================
//  主入口
// ============================================================
export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    const path = url.pathname.slice(1).toLowerCase();
    const UA = request.headers.get('User-Agent') || '';
    const upgrade = (request.headers.get('Upgrade') || '').toLowerCase();

    // 确定 UUID
    const envUUID = env.UUID || env.uuid;
    const uuidRegex = /^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-4[0-9a-fA-F]{3}-[89abAB][0-9a-fA-F]{3}-[0-9a-fA-F]{12}$/;
    const adminPwd = env.ADMIN || env.PASSWORD || env.admin || env.password || env.pswd || env.TOKEN || env.KEY;
    const userID = (envUUID && uuidRegex.test(envUUID)) ? envUUID.toLowerCase()
      : [await md5md5((adminPwd || 'default') + 'salt')].map(h => `${h.slice(0,8)}-${h.slice(8,12)}-4${h.slice(13,16)}-8${h.slice(17,20)}-${h.slice(20,32)}`)[0];
    setUUID(userID);

    // 初始化节点池
    await initNodePool(env);

    // 加载配置
    const cfg = await loadConfig(env, url.hostname, userID);

    // WebSocket 代理
    if (upgrade === 'websocket') {
      return handleWS(request, env, cfg);
    }

    // 登录
    if (path === 'login') {
      if (request.method === 'POST') {
        const form = await request.text();
        const pwd = new URLSearchParams(form).get('password');
        if (pwd === cfg.ADMIN) {
          const resp = new Response(JSON.stringify({ success: true }), { headers: { 'Content-Type': 'application/json' } });
          resp.headers.set('Set-Cookie', `auth=${await md5md5(UA + cfg.ADMIN)}; Path=/; Max-Age=86400; HttpOnly; Secure; SameSite=Lax`);
          return resp;
        }
        return new Response(JSON.stringify({ success: false }), { status: 401, headers: { 'Content-Type': 'application/json' } });
      }
      return new Response(ADMIN_HTML, { headers: { 'Content-Type': 'text/html;charset=utf-8' } });
    }

    // 登出
    if (path === 'logout') {
      const resp = new Response('redirect', { status: 302, headers: { 'Location': '/login' } });
      resp.headers.set('Set-Cookie', 'auth=; Path=/; Max-Age=0; HttpOnly');
      return resp;
    }

    // 订阅
    if (path === 'sub') {
      const token = url.searchParams.get('token');
      const subToken = await md5md5(url.hostname + userID);
      if (token !== subToken) return new Response('Invalid token', { status: 403 });
      const content = generateSubscription(cfg, url.hostname);
      const headers = {
        'Content-Type': 'text/plain;charset=utf-8',
        'Profile-Update-Interval': String(cfg.SUBUpdateTime),
        'Profile-web-page-url': url.origin + '/admin',
        'Cache-Control': 'no-store',
      };
      if (!UA.toLowerCase().includes('mozilla')) {
        headers['Content-Disposition'] = `attachment; filename*=utf-8''${encodeURIComponent(cfg.SUBNAME)}`;
      }
      return new Response(content, { headers });
    }

    // 管理面板
    if (path === 'admin' || path.startsWith('admin/')) {
      const isAuthed = await checkAuth(request, env, cfg);
      if (!isAuthed && path !== 'admin/api/config') {
        // 未认证且不是 API 预检，跳登录
        if (path.startsWith('admin/api/')) {
          return new Response(JSON.stringify({ error: 'unauthorized' }), { status: 401, headers: { 'Content-Type': 'application/json' } });
        }
        return new Response('redirect', { status: 302, headers: { 'Location': '/login' } });
      }

      // === 管理 API ===
      // 获取配置
      if (path === 'admin/api/config' && request.method === 'GET') {
        const subToken = await md5md5(url.hostname + userID);
        return new Response(JSON.stringify({ ...cfg, subToken }, null, 2), { headers: { 'Content-Type': 'application/json' } });
      }
      // 保存配置
      if (path === 'admin/api/config' && request.method === 'POST') {
        const newCfg = await request.json();
        newCfg.HOST = url.hostname;
        newCfg.UUID = userID;
        await saveConfig(env, newCfg);
        return new Response(JSON.stringify({ success: true }), { headers: { 'Content-Type': 'application/json' } });
      }
      // 重置配置
      if (path === 'admin/api/config/reset' && request.method === 'POST') {
        const defaults = await loadConfig(env, url.hostname, userID);
        // 强制重置
        const fresh = {
          TIME: new Date().toISOString(), HOST: url.hostname, UUID: userID,
          PATH: '/', Fingerprint: 'chrome', SUBNAME: 'TURN-Worker', SUBUpdateTime: 3,
          pollStrategy: 'roundrobin', fixedNodeId: null, subNodeCount: 10,
          enableUDP: true, enableXUDP: true, ADMIN: cfg.ADMIN,
        };
        await saveConfig(env, fresh);
        return new Response(JSON.stringify({ success: true }), { headers: { 'Content-Type': 'application/json' } });
      }
      // 获取节点
      if (path === 'admin/api/nodes' && request.method === 'GET') {
        return new Response(JSON.stringify({ nodes: nodePool }), { headers: { 'Content-Type': 'application/json' } });
      }
      // 保存节点（全量更新）
      if (path === 'admin/api/nodes' && request.method === 'PUT') {
        const body = await request.json();
        nodePool = body.nodes || [];
        await env.KV?.put('turn_nodes.json', JSON.stringify(nodePool));
        return new Response(JSON.stringify({ success: true }), { headers: { 'Content-Type': 'application/json' } });
      }
      // 重置节点
      if (path === 'admin/api/nodes/reset' && request.method === 'POST') {
        nodePool = BUILTIN_TURN_NODES.map((n, i) => ({ ...n, id: `builtin_${i}`, enabled: true, latency: null }));
        await env.KV?.put('turn_nodes.json', JSON.stringify(nodePool));
        return new Response(JSON.stringify({ nodes: nodePool }), { headers: { 'Content-Type': 'application/json' } });
      }
      // 测试单个节点
      const testMatch = path.match(/^admin\/api\/nodes\/(.+)\/test$/);
      if (testMatch && request.method === 'POST') {
        const id = decodeURIComponent(testMatch[1]);
        const node = nodePool.find(n => n.id === id);
        if (!node) return new Response(JSON.stringify({ ok: false, error: 'node not found' }), { status: 404, headers: { 'Content-Type': 'application/json' } });
        const result = await testTurnNode(node);
        return new Response(JSON.stringify(result), { headers: { 'Content-Type': 'application/json' } });
      }

      // 管理面板 HTML
      return new Response(ADMIN_HTML, { headers: { 'Content-Type': 'text/html;charset=utf-8' } });
    }

    // 根路径 -> 登录
    if (path === '' || path === '/') {
      return new Response('redirect', { status: 302, headers: { 'Location': '/login' } });
    }

    return new Response('Not Found', { status: 404 });
  },
};
//（注：内容由AI生成）
