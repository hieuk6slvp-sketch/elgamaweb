let currentPair = null, currentMsg = '', currentHash = '';

// ── SHA-256 ──────────────────────────────────────────────────────
async function sha256Hex(text) {
  const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(text));
  return Array.from(new Uint8Array(buf)).map(b => b.toString(16).padStart(2,'0')).join('');
}
function hexToBigInt(hex) { return BigInt('0x' + hex); }


function modpowBig(base, exp, mod) {
  let r = 1n; base %= mod;
  while (exp > 0n) {
    if (exp % 2n === 1n) r = r * base % mod;
    exp >>= 1n; base = base * base % mod;
  }
  return r;
}
function extEuclidBig(a, m) {
  let [a0, m0, y, x] = [a, m, 0n, 1n];
  if (m === 1n) return 0n;
  while (a0 > 1n) {
    const q = a0 / m0, t = m0;
    m0 = a0 % m0; a0 = t;
    [y, x] = [x - q * y, y];
  }
  return x < 0n ? x + m : x;
}
function gcdBig(a, b) {
  [a, b] = [BigInt(a), BigInt(b)];
  while (b) { [a, b] = [b, a % b]; }
  return a;
}

// ── KIỂM TRA NGUYÊN TỐ (Miller-Rabin) ───────────────────────────
function isPrime(n) {
  const nn = BigInt(n);
  if (nn < 2n) return false;
  if (nn === 2n || nn === 3n || nn === 5n) return true;
  if (nn % 2n === 0n || nn % 3n === 0n) return false;
  let d = nn - 1n, r = 0;
  while (d % 2n === 0n) { d >>= 1n; r++; }
  for (const a of [2n,3n,5n,7n,11n,13n,17n,19n,23n,29n,31n,37n]) {
    if (a >= nn) continue;
    let x = modpowBig(a, d, nn);
    if (x === 1n || x === nn - 1n) continue;
    let composite = true;
    for (let i = 0; i < r - 1; i++) {
      x = x * x % nn;
      if (x === nn - 1n) { composite = false; break; }
    }
    if (composite) return false;
  }
  return true;
}

// ── SINH SỐ NGẪU NHIÊN ──────────────────────────────────────────
function randomBigBits(nBits) {
  const bytes = new Uint8Array(Math.ceil(nBits / 8));
  crypto.getRandomValues(bytes);
  let val = 0n;
  for (const b of bytes) val = (val << 8n) | BigInt(b);
  val &= (1n << BigInt(nBits)) - 1n;
  val |= 1n << BigInt(nBits - 1);
  return val;
}
function randomPrime(nBits) {
  while (true) {
    let c = randomBigBits(nBits) | 1n;
    for (let i = 0; i < 2000; i++) {
      if (isPrime(c)) return c;
      c += 2n;
      if (c.toString(2).length > nBits) break;
    }
  }
}
function randBigInRange(lo, hi) {
  const [loB, hiB] = [BigInt(lo), BigInt(hi)];
  const range = hiB - loB + 1n;
  const bits  = range.toString(2).length;
  const bytes = Math.ceil(bits / 8);
  let rand;
  do {
    const arr = new Uint8Array(bytes);
    crypto.getRandomValues(arr);
    rand = 0n;
    for (const b of arr) rand = (rand << 8n) | BigInt(b);
    rand &= (1n << BigInt(bits)) - 1n;
  } while (rand >= range);
  return loB + rand;
}

// ── CĂN NGUYÊN THỦY ─────────────────────────────────────────────
function primeFactors(phi) {
  const f = []; let t = phi;
  for (let q = 2n; q * q <= t; q++) {
    if (t % q === 0n) { f.push(q); while (t % q === 0n) t /= q; }
  }
  if (t > 1n) f.push(t);
  return f;
}
function smallestPrimitiveRoot(p) {
  const pp = BigInt(p), phi = pp - 1n, factors = primeFactors(phi);
  for (let g = 2n; g < pp; g++) {
    if (factors.every(q => modpowBig(g, phi / q, pp) !== 1n)) return g;
  }
  return null;
}

// ── KÝ ELGAMAL ──────────────────────────────────────────────────
function Encry_S(hashHex) {
  const p = BigInt($('p').value), a = BigInt($('a').value), x = BigInt($('x').value);
  const pm1 = p - 1n, m = hexToBigInt(hashHex) % pm1;
  let K;
  do { K = randBigInRange(2n, p - 2n); } while (gcdBig(K, pm1) !== 1n);
  const s1   = modpowBig(a, K, p);
  const kinv = extEuclidBig(K, pm1);
  const s2   = ((kinv * ((m - x * s1) % pm1)) % pm1 + pm1) % pm1;
  return [s1, s2];
}

// ── XÁC MINH ELGAMAL ────────────────────────────────────────────
function _verify(pair, hashHex, p, a, y) {
  const pm1 = p - 1n, m = hexToBigInt(hashHex) % pm1, [s1, s2] = pair;
  const v1  = modpowBig(a, m, p);
  const v2  = modpowBig(y, s1, p) * modpowBig(s1, s2, p) % p;
  return { hopLe: v1 === v2 };
}
function Decry_S(pair, hashHex) {
  return _verify(pair, hashHex, BigInt($('p').value), BigInt($('a').value), BigInt($('y').value));
}
function Decry_S_WithKey(pair, hashHex, p, a, y) {
  return _verify(pair, hashHex, BigInt(p), BigInt(a), BigInt(y));
}

// ── ĐỌC FILE ────────────────────────────────────────────────────
async function readFileContent(file) {
  const name = file.name.toLowerCase();
  if (name.endsWith('.txt'))
    return new Promise((res, rej) => {
      const r = new FileReader();
      r.onload = e => res(e.target.result);
      r.onerror = () => rej(new Error('Không đọc được file văn bản.'));
      r.readAsText(file, 'UTF-8');
    });
  if (name.endsWith('.docx')) {
    if (typeof mammoth === 'undefined') throw new Error('Thiếu thư viện mammoth.js.');
    return new Promise((res, rej) => {
      const r = new FileReader();
      r.onload = async e => {
        try { res((await mammoth.extractRawText({ arrayBuffer: e.target.result })).value.trim()); }
        catch (err) { rej(new Error('Lỗi đọc .docx: ' + err.message)); }
      };
      r.onerror = () => rej(new Error('Không đọc được file .docx.'));
      r.readAsArrayBuffer(file);
    });
  }
  if (name.endsWith('.doc')) throw new Error('Định dạng .doc không hỗ trợ. Lưu lại thành .docx.');
  const ext = name.includes('.') ? name.split('.').pop().toUpperCase() : 'không rõ';
  throw new Error(`Định dạng .${ext} chưa hỗ trợ. Chỉ dùng: .txt, .docx`);
}

// ── UI HELPERS ───────────────────────────────────────────────────
const $ = id => document.getElementById(id);

function showToast(msg, type = 'info', duration = 3500) {
  const t = $('toast');
  t.textContent = msg; t.className = type; t.style.display = 'block';
  clearTimeout(t._timer);
  t._timer = setTimeout(() => { t.style.display = 'none'; }, duration);
}
function onFileChosen(inputId) {
  const file = $(inputId).files[0];
  if (!file) return;
  const txtId = 'txt-' + inputId;
  const txtEl = $(txtId);
  if (txtEl) { txtEl.textContent = '📄 ' + file.name; txtEl.className = 'file-pill-text chosen'; }
}
function clearFile(inputId, labelId, txtId) {
  $(inputId).value = '';
  $(txtId).textContent = 'Chọn file .txt / .docx'; $(txtId).className = 'file-pill-text';
}
function onSigFileChosen() {
  const file = $('file-sig').files[0];
  if (file) { $('txt-file-sig').textContent = '📦 ' + file.name; $('txt-file-sig').className = 'file-pill-text chosen'; }
}
function clearSigFile() {
  $('file-sig').value = '';
  $('txt-file-sig').textContent = 'Chọn file .elgsig đã tải về';
  $('txt-file-sig').className = 'file-pill-text';
  $('verify-result').style.display = 'none';
}
function switchTab(tab) {
  const f = tab === 'file';
  $('panel-file').style.display = f ? '' : 'none';
  $('panel-manual').style.display = f ? 'none' : '';
  $('tab-file').classList.toggle('active', f);
  $('tab-manual').classList.toggle('active', !f);
  $('verify-result').style.display = 'none';
}
function showVerifyResult(ok) {
  const el = $('verify-result');
  el.style.display = ''; el.className = 'verify-result ' + (ok ? 'valid' : 'invalid');
  el.innerHTML = ok
    ? `<span class="vr-icon">✅</span><span>Chữ ký hợp lệ!</span>`
    : `<span class="vr-icon">❌</span><span>Chữ ký không hợp lệ — Văn bản bị sửa đổi hoặc sai khóa.</span>`;
}
function switchKeyTab(tab) {
  const a = tab === 'auto';
  $('panel-auto-key').style.display = a ? '' : 'none';
  $('panel-manual-key').style.display = a ? 'none' : '';
  $('tab-auto').classList.toggle('active', a);
  $('tab-manual-key').classList.toggle('active', !a);
  $('btn-tao-khoa').style.display = a ? '' : 'none';
}
document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('input[name="psize"]').forEach(r => {
    r.addEventListener('change', () => {
      $('secure-hint').style.display = (r.value === 'secure' && r.checked) ? '' : 'none';
    });
  });
});

// ── NHẬP KHÓA THỦ CÔNG ──────────────────────────────────────────
function validateAManual() {
  const pVal = $('p-manual').value.trim(), aVal = $('a-manual').value.trim();
  const errEl = $('a-manual-err');
  errEl.style.display = 'none';
  if (!pVal || !aVal) return;
  try {
    const pBig = BigInt(pVal), aBig = BigInt(aVal);
    if (!isPrime(pBig)) return;
    const minRoot = smallestPrimitiveRoot(pBig);
    if (minRoot !== null && aBig !== minRoot) {
      errEl.textContent = `⚠ A phải là ${minRoot} (căn nguyên thủy nhỏ nhất)`;
      errEl.style.display = 'inline';
    }
  } catch (e) {}
}
function nhapKhoaThuCong() {
  const pVal = $('p-manual').value.trim(), aVal = $('a-manual').value.trim(), xVal = $('x-manual').value.trim();
  if (!pVal || !aVal || !xVal) { showToast('⚠️ Vui lòng nhập đủ P, A, X!', 'err'); return; }
  let pBig, aBig, xBig;
  try { pBig = BigInt(pVal); aBig = BigInt(aVal); xBig = BigInt(xVal); }
  catch { showToast('❌ Giá trị không hợp lệ! Chỉ nhập số nguyên.', 'err'); return; }
  if (!isPrime(pBig)) { showToast('❌ P không phải số nguyên tố!', 'err'); return; }
  const minRoot = smallestPrimitiveRoot(pBig);
  if (minRoot === null || aBig !== minRoot) {
    showToast(`❌ A không phù hợp! Căn nguyên thủy nhỏ nhất của P là ${minRoot}.`, 'err', 6000);
    return;
  }
  if (xBig < 2n || xBig > pBig - 2n) { showToast('❌ X phải thỏa mãn 2 ≤ X ≤ P−2!', 'err'); return; }
  const yBig = modpowBig(aBig, xBig, pBig);
  $('p').value = pBig.toString(); $('a').value = aBig.toString();
  $('x').value = xBig.toString(); $('y').value = yBig.toString();
  resetSignArea();
  showToast(`✅ Đã áp dụng khóa thủ công! Y = ${yBig}`, 'ok', 4000);
}
function clearManualInputs() {
  ['p-manual','a-manual','x-manual'].forEach(id => $(id).value = '');
  $('a-manual-err').style.display = 'none';
}

// ── TẠO KHÓA TỰ ĐỘNG ────────────────────────────────────────────
function taoKhoa() {
  const size = document.querySelector('input[name="psize"]:checked').value;
  const cfg  = {
    demo:   { min: 8,    max: 16,   label: 'demo',         msg: '⏳ Đang sinh số nguyên tố...',                  dur: 99999  },
    medium: { min: 32,   max: 64,   label: 'vừa',          msg: '⏳ Đang sinh số nguyên tố 32–64 bit...',        dur: 15000  },
    secure: { min: 2048, max: 4096, label: 'bảo mật cao',  msg: '⏳ Đang sinh số nguyên tố lớn... Có thể mất vài phút.', dur: 120000 }
  }[size];
  showToast(cfg.msg, 'info', cfg.dur);
  setTimeout(() => {
    try {
      const nBits = cfg.min + Math.floor(Math.random() * (cfg.max - cfg.min + 1));
      const pBig  = randomPrime(nBits);
      const aBig  = smallestPrimitiveRoot(pBig);
      const xBig  = randBigInRange(2n, pBig - 2n);
      const yBig  = modpowBig(aBig, xBig, pBig);
      $('p').value = pBig.toString(); $('a').value = aBig.toString();
      $('x').value = xBig.toString(); $('y').value = yBig.toString();
      resetSignArea();
      showToast(`✅ Đã tạo khóa ${nBits}-bit (${cfg.label}) thành công!`, 'ok', 5000);
    } catch (e) { showToast('❌ Lỗi tạo khóa: ' + e.message, 'err'); }
  }, 80);
}
function resetSignArea() {
  ['chu-ky','hash-display','msg-ky','msg-xacnhan'].forEach(id => $(id).value = '');
  $('ky-count').textContent = '';
  $('btn-export').style.display = $('export-info').style.display = $('verify-result').style.display = 'none';
  currentPair = null; currentMsg = ''; currentHash = '';
}

// ── XÓA TẤT CẢ ──────────────────────────────────────────────────
function xoaHet() {
  ['p','a','x','y','msg-ky','msg-xacnhan','chu-ky','hash-display','p-manual','a-manual','x-manual','msg-sig-doc']
    .forEach(id => { const el = $(id); if (el) el.value = ''; });
  resetSignArea();
  clearFile('file-ky', 'label-file-ky', 'txt-file-ky');
  clearFile('file-xacnhan', 'label-file-xacnhan', 'txt-file-xacnhan');
  clearFile('file-sig-doc', 'label-file-sig-doc', 'txt-file-sig-doc');
  clearSigFile();
  $('a-manual-err').style.display = 'none';
  showToast('🗑 Đã xóa tất cả.', 'info');
}

// ── KÝ SỐ ───────────────────────────────────────────────────────
async function kyso() {
  if (!$('p').value || !$('a').value || !$('x').value) {
    showToast('⚠️ Chưa có khóa! Hãy tạo hoặc nhập khóa trước.', 'err'); return;
  }
  const fileInput = $('file-ky');
  let msg;
  try {
    if (fileInput.files.length > 0) {
      showToast('⏳ Đang đọc file...', 'info', 99999);
      msg = await readFileContent(fileInput.files[0]);
      if (!msg) { showToast('⚠️ File trống!', 'err'); return; }
      $('msg-ky').value = msg.length > 200 ? msg.slice(0,200) + '...(rút gọn)' : msg;
    } else {
      msg = $('msg-ky').value;
      if (!msg.trim()) { showToast('⚠️ Vui lòng nhập văn bản hoặc chọn file!', 'err'); return; }
    }
  } catch (err) { showToast('❌ ' + err.message, 'err'); return; }

  showToast('⏳ Đang băm & ký...', 'info', 99999);
  try {
    const hashHex = await sha256Hex(msg);
    $('hash-display').value = hashHex;
    const pair = Encry_S(hashHex);
    currentMsg = msg; currentHash = hashHex; currentPair = pair;
    const fmt = v => v.toString().length > 30 ? v.toString().slice(0,15)+'…'+v.toString().slice(-8) : v.toString();
    $('chu-ky').value = `s1=${fmt(pair[0])}  |  s2=${fmt(pair[1])}`;
    $('ky-count').textContent = '1 cặp (s1, s2)';
    $('btn-export').style.display = '';
    $('export-info').style.display = 'none';
    showToast('✅ Đã ký thành công! Nhấn "Gắn chữ ký vào tệp" để tải về.', 'ok', 5000);
  } catch (e) { showToast('❌ Lỗi khi ký: ' + e.message, 'err'); }
}

// ══════════════════════════════════════════════════════════════════
//  XUẤT FILE .elgsig
//  Chỉ lưu publicKey + signature — KHÔNG lưu message
//  → Buộc người xác nhận phải nộp văn bản gốc thật sự
// ══════════════════════════════════════════════════════════════════
function xuatFileDaKy() {
  if (!currentPair) { showToast('⚠️ Chưa có chữ ký! Hãy ký văn bản trước.', 'err'); return; }

  const payload = {
    version:   '2.0',
    algorithm: 'ElGamal + SHA-256',
    signedAt:  new Date().toISOString(),
    // Không lưu message và hash — người xác nhận phải cung cấp văn bản gốc
    publicKey: {
      p: $('p').value,
      a: $('a').value,
      y: $('y').value
    },
    signature: [
      currentPair[0].toString(),
      currentPair[1].toString()
    ]
  };

  const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
  const url  = URL.createObjectURL(blob);
  const slug = currentMsg.slice(0,10).replace(/[^a-zA-Z0-9À-ỹ]/g,'_');
  const filename = `signed_${slug}_${Date.now()}.elgsig`;
  Object.assign(document.createElement('a'), { href: url, download: filename }).click();
  URL.revokeObjectURL(url);
  $('export-filename').textContent = filename;
  $('export-info').style.display = '';
  showToast(`💾 Đã tải về: ${filename}`, 'ok', 5000);
}

// ══════════════════════════════════════════════════════════════════
//  XÁC NHẬN TỪ FILE .elgsig
//
//  Quy trình đúng:
//    Văn bản gốc (người dùng cung cấp)
//        ↓ SHA-256
//       H' (hash tính tại chỗ)
//        ↓
//    So với chữ ký (s1, s2) và khóa công khai từ .elgsig:
//      v1 = a^H' mod p
//      v2 = y^s1 × s1^s2 mod p
//      v1 == v2 → ✅ Hợp lệ
//      v1 != v2 → ❌ Không hợp lệ (văn bản bị sửa dù 1 ký tự)
// ══════════════════════════════════════════════════════════════════
async function xacNhanFile() {
  const fileInput = $('file-sig');
  if (!fileInput.files.length) { showToast('⚠️ Hãy chọn file .elgsig!', 'err'); return; }

  // Bước 1: Đọc file .elgsig
  let data;
  try {
    const text = await new Promise((res, rej) => {
      const r = new FileReader();
      r.onload = e => res(e.target.result);
      r.onerror = () => rej(new Error('Không đọc được file .elgsig.'));
      r.readAsText(fileInput.files[0], 'UTF-8');
    });
    data = JSON.parse(text);
  } catch (e) { showToast('❌ Lỗi đọc file .elgsig: ' + e.message, 'err'); return; }

  if (!data.publicKey || !data.signature) {
    showToast('❌ File không đúng định dạng .elgsig!', 'err'); return;
  }

  // Bước 2: Lấy văn bản gốc từ người dùng (file hoặc ô nhập)
  let msg;
  try {
    const docInput = $('file-sig-doc');
    if (docInput && docInput.files.length > 0) {
      showToast('⏳ Đang đọc file văn bản...', 'info', 99999);
      msg = await readFileContent(docInput.files[0]);
      if (!msg) { showToast('⚠️ File văn bản trống!', 'err'); return; }
    } else {
      const txtEl = $('msg-sig-doc');
      msg = txtEl ? txtEl.value : '';
      if (!msg.trim()) {
        showToast('⚠️ Vui lòng nhập văn bản gốc hoặc chọn file!', 'err'); return;
      }
    }
  } catch (e) { showToast('❌ ' + e.message, 'err'); return; }

  showToast('⏳ Đang băm & xác nhận...', 'info', 99999);
  try {
    // Bước 3: Băm văn bản người dùng cung cấp → H'
    const hashHex = await sha256Hex(msg);

    // Bước 4: Xác minh ElGamal bằng H' (không dùng hash cũ trong file)
    const { p, a, y } = data.publicKey;
    const pair = [BigInt(data.signature[0]), BigInt(data.signature[1])];

    $('p').value = p; $('a').value = a; $('y').value = y;

    const { hopLe } = Decry_S_WithKey(pair, hashHex, p, a, y);
    showVerifyResult(hopLe);
    showToast(hopLe ? '✅ Xác nhận thành công!' : '❌ Chữ ký không hợp lệ!', hopLe ? 'ok' : 'err', 5000);
  } catch (e) { showToast('❌ Lỗi: ' + e.message, 'err'); }
}

// ── XÁC NHẬN THỦ CÔNG ───────────────────────────────────────────
async function xacNhanThuCong() {
  if (!currentPair) { showToast('⚠️ Chưa có chữ ký! Hãy ký văn bản trước.', 'err'); return; }
  const fileInput = $('file-xacnhan');
  let msg;
  try {
    if (fileInput.files.length > 0) {
      showToast('⏳ Đang đọc file...', 'info', 99999);
      msg = await readFileContent(fileInput.files[0]);
      if (!msg) { showToast('⚠️ File trống!', 'err'); return; }
      $('msg-xacnhan').value = msg.length > 200 ? msg.slice(0,200) + '...(rút gọn)' : msg;
    } else {
      msg = $('msg-xacnhan').value;
      if (!msg.trim()) { showToast('⚠️ Vui lòng nhập văn bản!', 'err'); return; }
    }
  } catch (err) { showToast('❌ ' + err.message, 'err'); return; }
  showToast('⏳ Đang băm & xác nhận...', 'info', 99999);
  try {
    const { hopLe } = Decry_S(currentPair, await sha256Hex(msg));
    showVerifyResult(hopLe);
    showToast(hopLe ? '✅ Chữ ký hợp lệ!' : '❌ Chữ ký không hợp lệ!', hopLe ? 'ok' : 'err', 5000);
  } catch (e) { showToast('❌ Lỗi xác nhận: ' + e.message, 'err'); }
}