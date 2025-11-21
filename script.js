// 离线 RSA + OAEP (SHA-256) 实现 (纯原生 JS, 不依赖外部库)
// 目标: 生成 2048 位密钥, 大文本分块加密/解密
// 注意: 纯 RSA 分块对上万字符性能较慢, 建议实际生产使用混合加密(AES+RSA)

// ---------------- 工具函数: 编码/转换 ----------------
function utf8ToBytes(str){
  return new TextEncoder().encode(str);
}
function bytesToUtf8(bytes){
  return new TextDecoder().decode(bytes);
}
function concatBytes(arrays){
  let total = arrays.reduce((s,a)=>s+a.length,0);
  let out = new Uint8Array(total); let offset=0;
  for(let a of arrays){ out.set(a, offset); offset += a.length; }
  return out;
}
function byteArrayToHex(b){ return Array.from(b).map(x=>x.toString(16).padStart(2,'0')).join(''); }
function bytesToBase64(bytes){
  let binary = Array.from(bytes).map(b=>String.fromCharCode(b)).join('');
  return btoa(binary);
}
function base64ToBytes(b64){
  let bin = atob(b64); let out = new Uint8Array(bin.length);
  for(let i=0;i<bin.length;i++) out[i] = bin.charCodeAt(i);
  return out;
}

// ---------------- SHA-256 实现（标准、Uint8Array 输入） ----------------
function sha256(bytes){
  // 将输入转换为大端 32 位字
  const words = [];
  for (let i = 0; i < bytes.length; i += 4) {
    words[i >> 2] = ((bytes[i] || 0) << 24) | ((bytes[i + 1] || 0) << 16) | ((bytes[i + 2] || 0) << 8) | (bytes[i + 3] || 0);
  }
  // 附加 1 比特（0x80）
  const bitLen = (bytes.length * 8) >>> 0; // 低 32 位
  words[bitLen >> 5] = (words[bitLen >> 5] || 0) | (0x80 << (24 - (bitLen % 32)));
  // 附加 64 位长度（高 32 位与低 32 位）
  const totalLenWords = (((bitLen + 64) >> 9) << 4) + 16; // 需要的总 word 数（补齐后 + 长度域）
  words.length = totalLenWords;
  const hi = Math.floor((bytes.length * 8) / 0x100000000);
  const lo = (bytes.length * 8) >>> 0;
  words[totalLenWords - 2] = hi;
  words[totalLenWords - 1] = lo;

  const K = [
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
  ];
  let H0 = 0x6a09e667, H1 = 0xbb67ae85, H2 = 0x3c6ef372, H3 = 0xa54ff53a,
      H4 = 0x510e527f, H5 = 0x9b05688c, H6 = 0x1f83d9ab, H7 = 0x5be0cd19;

  const w = new Array(64);
  const rotr = (x,n)=> (x>>>n) | (x<<(32-n));
  const Ch = (x,y,z)=> (x & y) ^ (~x & z);
  const Maj = (x,y,z)=> (x & y) ^ (x & z) ^ (y & z);
  const Sigma0 = x=> rotr(x,2) ^ rotr(x,13) ^ rotr(x,22);
  const Sigma1 = x=> rotr(x,6) ^ rotr(x,11) ^ rotr(x,25);
  const sigma0 = x=> rotr(x,7) ^ rotr(x,18) ^ (x>>>3);
  const sigma1 = x=> rotr(x,17) ^ rotr(x,19) ^ (x>>>10);

  for (let i = 0; i < words.length; i += 16) {
    for (let t = 0; t < 64; t++) {
      if (t < 16) {
        w[t] = words[i + t] | 0;
      } else {
        w[t] = (((w[t-16] | 0) + (sigma0(w[t-15] | 0) | 0) + (w[t-7] | 0) + (sigma1(w[t-2] | 0) | 0)) | 0) >>> 0;
      }
    }

    let a = H0, b = H1, c = H2, d = H3, e = H4, f = H5, g = H6, h = H7;

    for (let t = 0; t < 64; t++) {
      const T1 = ((((((h + Sigma1(e)) | 0) + Ch(e, f, g)) | 0) + K[t]) | 0) + (w[t] | 0) | 0;
      const T2 = (Sigma0(a) + Maj(a, b, c)) | 0;
      h = g; g = f; f = e; e = (d + T1) | 0; d = c; c = b; b = a; a = (T1 + T2) | 0;
    }

    H0 = (H0 + a) | 0;
    H1 = (H1 + b) | 0;
    H2 = (H2 + c) | 0;
    H3 = (H3 + d) | 0;
    H4 = (H4 + e) | 0;
    H5 = (H5 + f) | 0;
    H6 = (H6 + g) | 0;
    H7 = (H7 + h) | 0;
  }

  const out = new Uint8Array(32);
  const hs = [H0,H1,H2,H3,H4,H5,H6,H7];
  for (let i = 0; i < 8; i++) {
    out[i*4]   = (hs[i] >>> 24) & 0xff;
    out[i*4+1] = (hs[i] >>> 16) & 0xff;
    out[i*4+2] = (hs[i] >>> 8) & 0xff;
    out[i*4+3] = (hs[i] >>> 0) & 0xff;
  }
  return out;
}

// ---------------- DRBG (基于 SHA-256 计数器) ----------------
class DRBG {
  constructor(seedBytes){
    this.seed = seedBytes;
    this.counter = 0;
    this.cache = new Uint8Array(0);
  }
  next(bytes){
    const out = new Uint8Array(bytes);
    let filled = 0;
    while (filled < bytes) {
      if (this.cache.length === 0) {
        const ctr = new Uint8Array(4);
        ctr[0]=(this.counter>>>24)&0xff; ctr[1]=(this.counter>>>16)&0xff; ctr[2]=(this.counter>>>8)&0xff; ctr[3]=this.counter&0xff;
        const block = sha256(concatBytes([this.seed, ctr]));
        this.cache = block;
        this.counter++;
      }
      const need = Math.min(this.cache.length, bytes - filled);
      out.set(this.cache.subarray(0, need), filled);
      this.cache = this.cache.subarray(need);
      filled += need;
    }
    return out;
  }
}

// ---------------- 大整数工具 ----------------
function bytesToBigInt(bytes){
  let x = 0n;
  for(let b of bytes){ x = (x << 8n) + BigInt(b); }
  return x;
}
function bigIntToBytes(b, length){
  let out = new Uint8Array(length);
  for(let i=length-1;i>=0;i--){ out[i] = Number(b & 0xffn); b >>= 8n; }
  return out;
}
function modPow(base, exp, mod){
  let result = 1n;
  base = base % mod;
  while(exp > 0){
    if(exp & 1n) result = (result * base) % mod;
    base = (base * base) % mod;
    exp >>= 1n;
  }
  return result;
}
function modInv(a, m){
  // 扩展欧几里得
  let m0=m, x0=0n, x1=1n;
  if(m===1n) return 0n;
  while(a>1n){
    let q = a / m;
    [a, m] = [m, a % m];
    [x0, x1] = [x1 - q * x0, x0];
  }
  if(x1 < 0n) x1 += m0;
  return x1;
}

// Miller-Rabin 试验
function isProbablePrime(n, k=32){
  if(n < 2n) return false;
  for(let p of [2n,3n,5n,7n,11n,13n,17n,19n,23n,29n]){ if(n===p) return true; if(n%p===0n) return n===p; }
  let r=0n, d=n-1n;
  while((d & 1n) === 0n){ d >>= 1n; r++; }
  outer: for(let i=0;i<k;i++){
    let a = 2n + randBetween(n-4n, 'keygen'); // [2, n-2]
    let x = modPow(a, d, n);
    if(x===1n || x===n-1n) continue;
    for(let j=1n;j<r;j++){
      x = (x * x) % n;
      if(x===n-1n) continue outer;
    }
    return false;
  }
  return true;
}

let _drbg; // 兼容旧变量名（不再使用）
let _drbgKey = null;   // 密钥生成专用 DRBG
let _drbgOaep = null;  // OAEP 专用 DRBG
function randBytes(len, purpose='keygen'){
  if (purpose === 'oaep') {
    if (_drbgOaep) return _drbgOaep.next(len);
  } else {
    if (_drbgKey) return _drbgKey.next(len);
  }
  if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
    const b = new Uint8Array(len);
    crypto.getRandomValues(b);
    return b;
  }
  throw new Error('随机源未初始化');
}
function randBetween(n, purpose='keygen'){
  const bytesLen = Math.ceil(n.toString(2).length / 8);
  while (true) {
    const b = randBytes(bytesLen, purpose);
    const x = bytesToBigInt(b);
    if (x <= n) return x;
  }
}

function randomOddBigInt(bits){
  let bytes = Math.ceil(bits/8);
  let rnd = randBytes(bytes, 'keygen');
  // 保证最高位与最低位
  rnd[0] |= 0x80; // 确保位数
  rnd[rnd.length-1] |= 0x01; // odd
  return bytesToBigInt(rnd);
}

async function generatePrime(bits, progressCb){
  let attempts=0;
  while(true){
    let cand = randomOddBigInt(bits);
    attempts++;
    if(isProbablePrime(cand)){
      progressCb && progressCb(`找到素数 (尝试 ${attempts})`);
      return cand;
    }
    if(attempts % 20 === 0){ progressCb && progressCb(`尝试 ${attempts} 次仍在搜索...`); await sleep(0); }
  }
}
function sleep(ms){ return new Promise(r=>setTimeout(r,ms)); }

// ---------------- RSA 密钥生成 ----------------
async function generateRSA(progressCb){
  progressCb('初始化 DRBG...');
  let entropyStr = document.getElementById('entropyInput').value;
  const eBytes = utf8ToBytes(entropyStr);
  const seedKey = sha256(concatBytes([utf8ToBytes('p2p-keygen|v1|'), eBytes]));
  const seedOaep = sha256(concatBytes([utf8ToBytes('p2p-oaep|v1|'), eBytes]));
  _drbgKey = new DRBG(seedKey);
  _drbgOaep = new DRBG(seedOaep);
  const bits = 2048;
  progressCb('开始搜索 p...');
  let p = await generatePrime(bits/2, progressCb);
  progressCb('开始搜索 q...');
  let q;
  do { q = await generatePrime(bits/2, progressCb); } while(q===p);
  let n = p * q;
  let phi = (p-1n) * (q-1n);
  let e = 65537n;
  let d = modInv(e, phi);
  return { n, e, d, p, q };
}

// ---------------- ASN.1/PEM 编码 (最小 PKCS#1) ----------------
function encodeLength(len){
  if(len < 0x80) return [len];
  let bytes=[]; while(len>0){ bytes.unshift(len & 0xff); len >>= 8; }
  return [0x80 | bytes.length, ...bytes];
}
function encodeInteger(big){
  if(big === undefined) throw new Error('big undefined');
  let hex = big.toString(16);
  if(hex.length % 2) hex = '0' + hex;
  let bytes = hex.match(/.{2}/g).map(h=>parseInt(h,16));
  if(bytes[0] & 0x80) bytes.unshift(0); // 正数标识
  return [0x02, ...encodeLength(bytes.length), ...bytes];
}
function derPrivateKey({n,e,d,p,q}){
  // version=0, n,e,d,p,q, dp, dq, qi
  let version=[0x02,0x01,0x00];
  let dp = d % (p-1n); let dq = d % (q-1n); let qi = modInv(q, p);
  let seq = [0x30];
  let content = [
    ...version,
    ...encodeInteger(n),
    ...encodeInteger(e),
    ...encodeInteger(d),
    ...encodeInteger(p),
    ...encodeInteger(q),
    ...encodeInteger(dp),
    ...encodeInteger(dq),
    ...encodeInteger(qi)
  ];
  seq.push(...encodeLength(content.length));
  seq.push(...content);
  return new Uint8Array(seq);
}
function derPublicKey({n,e}){
  let seq=[0x30];
  let content=[ ...encodeInteger(n), ...encodeInteger(e) ];
  seq.push(...encodeLength(content.length));
  seq.push(...content);
  return new Uint8Array(seq);
}
function pem(label, der){
  let b64 = bytesToBase64(der);
  let lines = b64.match(/.{1,64}/g).join('\n');
  return `-----BEGIN ${label}-----\n${lines}\n-----END ${label}-----`;
}

// ---------------- OAEP + 分块加密 ----------------
const HASH_LEN = 32; // SHA-256
function mgf1(seed, length){
  let out = new Uint8Array(length);
  let done=0; let counter=0;
  while(done < length){
    let c = new Uint8Array(4);
    c[0]=(counter>>>24)&0xff; c[1]=(counter>>>16)&0xff; c[2]=(counter>>>8)&0xff; c[3]=counter&0xff;
    let h = sha256(concatBytes([seed,c]));
    let need = Math.min(h.length, length-done);
    out.set(h.subarray(0,need), done);
    done += need; counter++;
  }
  return out;
}

function oaepEncode(messageBytes, k){ // k = modulus length bytes
  const lHash = sha256(new Uint8Array());
  const psLen = k - messageBytes.length - 2*HASH_LEN - 2;
  if(psLen < 0) throw new Error('消息过长 (块大小不足)');
  let PS = new Uint8Array(psLen); // 全 0
  let DB = concatBytes([lHash, PS, new Uint8Array([0x01]), messageBytes]);
  let seed = randBytes(HASH_LEN, 'oaep');
  let dbMask = mgf1(seed, DB.length);
  let maskedDB = DB.map((b,i)=>b ^ dbMask[i]);
  let seedMask = mgf1(maskedDB, HASH_LEN);
  let maskedSeed = seed.map((b,i)=>b ^ seedMask[i]);
  return concatBytes([new Uint8Array([0x00]), maskedSeed, maskedDB]);
}

function oaepDecode(em){
  const lHash = sha256(new Uint8Array());
  if(em[0] !== 0x00) throw new Error('OAEP 格式错误');
  let maskedSeed = em.slice(1, 1+HASH_LEN);
  let maskedDB = em.slice(1+HASH_LEN);
  let seedMask = mgf1(maskedDB, HASH_LEN);
  let seed = maskedSeed.map((b,i)=>b ^ seedMask[i]);
  let dbMask = mgf1(seed, maskedDB.length);
  let DB = maskedDB.map((b,i)=>b ^ dbMask[i]);
  let lHash2 = DB.slice(0,HASH_LEN);
  if(byteArrayToHex(lHash2) !== byteArrayToHex(lHash)) throw new Error('标签哈希不匹配');
  let idx = HASH_LEN;
  while(idx < DB.length && DB[idx] === 0x00) idx++;
  if(idx >= DB.length || DB[idx] !== 0x01) throw new Error('分隔符缺失');
  let msg = DB.slice(idx+1);
  return msg;
}

function rsaEncryptBlock(mBig, key){
  return modPow(mBig, key.e, key.n);
}
function rsaDecryptBlock(cBig, key){
  return modPow(cBig, key.d, key.n);
}

function modulusByteLength(nBig){
  return Math.ceil(nBig.toString(2).length / 8);
}

function encryptLargeText(plain, key, progressCb){
  let k = modulusByteLength(key.n); // 精确模数字节长度
  let plainBytes = utf8ToBytes(plain);
  let blocks=[]; let ptr=0; let blockIndex=0;
  const maxMsgLen = k - 2*HASH_LEN - 2; // OAEP 标准公式
  while(ptr < plainBytes.length){
    let chunk = plainBytes.slice(ptr, ptr+maxMsgLen);
    let encoded = oaepEncode(chunk, k);
    let m = bytesToBigInt(encoded);
    let c = rsaEncryptBlock(m, key);
    let cBytes = bigIntToBytes(c, k);
    blocks.push(bytesToBase64(cBytes));
    ptr += chunk.length; blockIndex++;
    if(blockIndex % 10 === 0){ progressCb && progressCb(`已加密块 ${blockIndex}`); }
  }
  progressCb && progressCb(`完成, 共 ${blockIndex} 块`);
  return blocks.join('.'); // 用 . 分隔
}

function decryptLargeText(cipherText, key, progressCb){
  let parts = cipherText.trim().split('.').filter(x=>x);
  let k = modulusByteLength(key.n);
  let outBytes=[]; let idx=0;
  for(let part of parts){
    let cBytes = base64ToBytes(part);
    if(cBytes.length !== k) throw new Error('密文块长度异常');
    let c = bytesToBigInt(cBytes);
    let m = rsaDecryptBlock(c, key);
    let em = bigIntToBytes(m, k);
    let msgBytes = oaepDecode(em);
    outBytes.push(msgBytes);
    idx++;
    if(idx % 10 === 0){ progressCb && progressCb(`已解密块 ${idx}`); }
  }
  progressCb && progressCb(`完成, 共 ${idx} 块`);
  return bytesToUtf8(concatBytes(outBytes));
}

// ---------------- UI 逻辑 ----------------
let generatedKey=null; // 仅保存生成密钥对
const entropyInput = document.getElementById('entropyInput');
entropyInput.addEventListener('input', ()=>{
  let len = entropyInput.value.length;
  document.getElementById('entropyCount').textContent = len;
  document.getElementById('btnGenerateKeys').disabled = len < 50;
});

document.getElementById('btnClearEntropy').addEventListener('click', ()=>{
  entropyInput.value=''; entropyInput.dispatchEvent(new Event('input'));
});

document.getElementById('btnGenerateKeys').addEventListener('click', async ()=>{
  if(entropyInput.value.length < 50){ alert('熵不足 50 字符'); return; }
  const btn = document.getElementById('btnGenerateKeys');
  btn.disabled = true;
  setProgress('keyGenProgress','开始生成密钥...');
  try {
  generatedKey = await generateRSA(msg=>setProgress('keyGenProgress',msg));
  // 导出 PEM
  let privDer = derPrivateKey(generatedKey);
  let pubDer = derPublicKey(generatedKey);
    document.getElementById('privateKey').value = pem('RSA PRIVATE KEY', privDer);
    document.getElementById('publicKey').value = pem('RSA PUBLIC KEY', pubDer);
    document.getElementById('keyOutputs').classList.remove('hidden');
  refreshButtons();
  } catch(e){
    alert('密钥生成失败: ' + e.message);
  } finally {
    btn.disabled = false;
  }
});

function setProgress(id, text){
  document.getElementById(id).textContent = text;
}

function getEncryptPublicKey(){
  const pubText = document.getElementById('importPublic').value.trim() || document.getElementById('publicKey').value.trim();
  if(!pubText) return null;
  try { return loadPublicKey(pubText); } catch(e){ setProgress('importPubStatus','公钥错误: '+e.message); return null; }
}
function getDecryptPrivateKey(){
  const privText = document.getElementById('importPrivate').value.trim() || document.getElementById('privateKey').value.trim();
  if(!privText) return null;
  try { return loadPrivateKey(privText); } catch(e){ setProgress('importPrivStatus','私钥错误: '+e.message); return null; }
}
document.getElementById('btnEncrypt').addEventListener('click', ()=>{
  let pubKey = getEncryptPublicKey();
  if(!pubKey){ alert('缺少或无效公钥'); return; }
  let plain = document.getElementById('plainInput').value;
  if(!plain){ alert('明文为空'); return; }
  try {
    let cipher = encryptLargeText(plain, pubKey, msg=>setProgress('encryptProgress',msg));
    document.getElementById('cipherOutput').value = cipher;
  } catch(e){
    alert('加密失败: ' + e.message);
  }
});

// 解密
 document.getElementById('btnDecrypt').addEventListener('click', ()=>{
  let privKey = getDecryptPrivateKey();
  if(!privKey){ alert('缺少或无效私钥'); return; }
  let cipher = document.getElementById('cipherInput').value.trim();
  if(!cipher){ alert('密文为空'); return; }
  try {
    let plain = decryptLargeText(cipher, privKey, msg=>setProgress('decryptProgress',msg));
    document.getElementById('plainOutput').value = plain;
  } catch(e){
    alert('解密失败: ' + e.message);
  }
 });

// 下载 PEM
 document.getElementById('btnDownloadKeys').addEventListener('click', ()=>{
  let priv = document.getElementById('privateKey').value;
  let pub = document.getElementById('publicKey').value;
  downloadText('rsa_private_key.pem', priv);
  downloadText('rsa_public_key.pem', pub);
 });

function downloadText(filename, text){
  let blob = new Blob([text], {type:'text/plain'});
  let a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = filename;
  document.body.appendChild(a); a.click(); document.body.removeChild(a);
}

// 安全提示: 本实现为教学用途, 不包含侧信道防护或强随机性来源 (仅基于用户输入熵 + SHA-256 DRBG)。

// ---------------- 密钥导入解析 ----------------
function parsePem(pemText){
  if(!pemText) return null;
  let lines = pemText.trim().split(/\r?\n/).filter(l=>!l.startsWith('-----BEGIN') && !l.startsWith('-----END'));
  let b64 = lines.join('');
  try { return base64ToBytes(b64); } catch { return null; }
}
function parseDerInteger(bytes, offset){
  if(bytes[offset] !== 0x02) throw new Error('期望 INTEGER');
  let lenInfo = bytes[offset+1]; let lenBytes=0; let len;
  if(lenInfo & 0x80){ lenBytes = lenInfo & 0x7f; len=0; for(let i=0;i<lenBytes;i++){ len = (len<<8) | bytes[offset+2+i]; } } else { len=lenInfo; }
  let start = offset+2+lenBytes; let end = start+len; let intBytes = bytes.slice(start,end);
  if(intBytes[0]===0x00) intBytes = intBytes.slice(1);
  let bi = bytesToBigInt(intBytes);
  return { value: bi, next: end };
}
function loadPublicKey(pemText){
  let der = parsePem(pemText); if(!der) throw new Error('公钥PEM解析失败');
  // 结构: SEQUENCE { n, e }
  if(der[0]!==0x30) throw new Error('公钥DER格式错误');
  // 跳过长度
  let idx=2; if((der[1] & 0x80)===0x80){ let l=der[1]&0x7f; idx=2+l; }
  let nInt = parseDerInteger(der, idx); let eInt = parseDerInteger(der, nInt.next);
  return { n: nInt.value, e: eInt.value };
}
function loadPrivateKey(pemText){
  let der = parsePem(pemText); if(!der) throw new Error('私钥PEM解析失败');
  if(der[0]!==0x30) throw new Error('私钥DER格式错误');
  let idx=2; if((der[1]&0x80)===0x80){ let l=der[1]&0x7f; idx=2+l; }
  // version
  let ver = parseDerInteger(der, idx); idx = ver.next;
  let nInt = parseDerInteger(der, idx); idx = nInt.next;
  let eInt = parseDerInteger(der, idx); idx = eInt.next;
  let dInt = parseDerInteger(der, idx); idx = dInt.next;
  let pInt = parseDerInteger(der, idx); idx = pInt.next;
  let qInt = parseDerInteger(der, idx); idx = qInt.next;
  let dpInt = parseDerInteger(der, idx); idx = dpInt.next;
  let dqInt = parseDerInteger(der, idx); idx = dqInt.next;
  let qiInt = parseDerInteger(der, idx); idx = qiInt.next;
  return { n: nInt.value, e: eInt.value, d: dInt.value, p: pInt.value, q: qInt.value };
}
function refreshButtons(){
  const pubKeyText = document.getElementById('importPublic').value.trim() || document.getElementById('publicKey').value.trim();
  const privKeyText = document.getElementById('importPrivate').value.trim() || document.getElementById('privateKey').value.trim();
  document.getElementById('btnEncrypt').disabled = !pubKeyText;
  document.getElementById('btnDecrypt').disabled = !privKeyText;
}
['importPublic','importPrivate','publicKey','privateKey','plainInput','cipherInput'].forEach(id=>{
  const el = document.getElementById(id);
  if(el){ el.addEventListener('input', refreshButtons); }
});
refreshButtons();

// ---------------- 复制功能 ----------------
function copyTextFrom(id){
  const el = document.getElementById(id);
  if(!el) return;
  const text = el.value;
  if(!text){ alert('内容为空，无法复制'); return; }
  try {
    navigator.clipboard.writeText(text).then(()=>{
      alert('已复制到剪贴板');
    }).catch(()=>{
      // 回退
      el.select(); document.execCommand('copy'); alert('已复制 (旧API)');
    });
  } catch(e){
    el.select(); document.execCommand('copy'); alert('已复制');
  }
}
document.getElementById('btnCopyCipher')?.addEventListener('click', ()=>copyTextFrom('cipherOutput'));
document.getElementById('btnCopyPlain')?.addEventListener('click', ()=>copyTextFrom('plainOutput'));
document.getElementById('btnCopyGenPub')?.addEventListener('click', ()=>copyTextFrom('publicKey'));
document.getElementById('btnCopyGenPriv')?.addEventListener('click', ()=>copyTextFrom('privateKey'));

// ---------------- 主题切换 ----------------
const themeBtn = document.getElementById('btnToggleTheme');
const savedTheme = localStorage.getItem('theme');
if(savedTheme === 'dark'){ document.documentElement.setAttribute('data-theme','dark'); themeBtn.textContent='切换浅色'; }
else { document.documentElement.removeAttribute('data-theme'); themeBtn.textContent='切换深色'; }
themeBtn?.addEventListener('click', ()=>{
  const isDark = document.documentElement.getAttribute('data-theme') === 'dark';
  if(isDark){
    document.documentElement.removeAttribute('data-theme');
    localStorage.setItem('theme','light');
    themeBtn.textContent='切换深色';
  } else {
    document.documentElement.setAttribute('data-theme','dark');
    localStorage.setItem('theme','dark');
    themeBtn.textContent='切换浅色';
  }
});
