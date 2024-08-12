/*! noble-secp256k1 - MIT License (c) 2019 Paul Miller (paulmillr.com) */
const B256 = 2n ** 256n;                                // secp256k1 is short weierstrass curve
const P = B256 - 0x1000003d1n;                          // curve's field prime
const N = B256 - 0x14551231950b75fc4402da1732fc9bebfn;  // curve (group) order
const Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n; // base point x
const Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n; // base point y
const CURVE = {p: P, n: N, a: 0n, b: 7n, Gx, Gy};       // exported variables incl. a, b
const fLen = 32;                                        // field / group byte length
type Bytes = Uint8Array; type Hex = Bytes | string; type PrivKey = Hex | bigint;
const crv = (x: bigint) => mod(mod(x * x) * x + CURVE.b); // x³ + ax + b weierstrass formula; a=0
const err = (m = ''): never => { throw new Error(m); }; // error helper, messes-up stack trace
const big = (n: unknown): n is bigint => typeof n === 'bigint'; // is big integer
const str = (s: unknown): s is string => typeof s === 'string'; // is string
const fe = (n: bigint) => big(n) && 0n < n && n < P;    // is field element (invertible)
const ge = (n: bigint) => big(n) && 0n < n && n < N;    // is group element
const isu8 = (a: unknown): a is Uint8Array => (
  a instanceof Uint8Array ||
  (a != null && typeof a === 'object' && a.constructor.name === 'Uint8Array')
);
const au8 = (a: unknown, l?: number): Bytes =>          // assert is Uint8Array (of specific length)
  !isu8(a) || (typeof l === 'number' && l > 0 && a.length !== l) ?
    err('Uint8Array expected') : a;
const u8n = (data?: any) => new Uint8Array(data);       // creates Uint8Array
const toU8 = (a: Hex, len?: number) => au8(str(a) ? h2b(a) : u8n(au8(a)), len); // norm(hex/u8a) to u8a
const mod = (a: bigint, b = P) => { let r = a % b; return r >= 0n ? r : b + r; }; // mod division
const isPoint = (p: unknown) => (p instanceof Point ? p : err('Point expected')); // is 3d point
interface AffinePoint { x: bigint, y: bigint }          // Point in 2d xy affine coordinates
class Point {                                           // Point in 3d xyz projective coordinates
  constructor(readonly px: bigint, readonly py: bigint, readonly pz: bigint) {} //3d=less inversions
  static readonly BASE = new Point(Gx, Gy, 1n);         // Generator / base point
  static readonly ZERO = new Point(0n, 1n, 0n);         // Identity / zero point
  static fromAffine (p: AffinePoint) {                  // (0, 0) => (0, 1, 0), not (0, 0, 1)
    return ((p.x === 0n) && (p.y === 0n)) ? Point.ZERO : new Point(p.x, p.y, 1n);
  }
  static fromHex(hex: Hex): Point {                     // Convert Uint8Array or hex string to Point
    hex = toU8(hex);                                    // convert hex string to Uint8Array
    let p: Point | undefined = undefined;
    const head = hex[0], tail = hex.subarray(1);        // first byte is prefix, rest is data
    const x = slcNum(tail, 0, fLen), len = hex.length;  // next 32 bytes are x coordinate
    if (len === 33 && [0x02, 0x03].includes(head)) {    // compressed points: 33b, start
      if (!fe(x)) err('Point hex invalid: x not FE');   // with byte 0x02 or 0x03. Check if 0<x<P
      let y = sqrt(crv(x));                             // x³ + ax + b is right side of equation
      const isYOdd = (y & 1n) === 1n;                   // y² is equivalent left-side. Calculate y²:
      const headOdd = (head & 1) === 1;                 // y = √y²; there are two solutions: y, -y
      if (headOdd !== isYOdd) y = mod(-y);              // determine proper solution
      p = new Point(x, y, 1n);                          // create point
    }                                                   // Uncompressed points: 65b, start with 0x04
    if (len === 65 && head === 0x04) p = new Point(x, slcNum(tail, fLen, 2 * fLen), 1n);
    return p ? p.ok() : err('Point is not on curve');   // Verify the result
  }
  static fromPrivateKey(k: PrivKey) { return G.mul(toPriv(k)); } // Create point from a private key.
  get x() { return this.aff().x; }                      // .x, .y will call expensive toAffine:
  get y() { return this.aff().y; }                      // should be used with care.
  equals(other: Point): boolean {                       // Equality check: compare points
    const { px: X1, py: Y1, pz: Z1 } = this;
    const { px: X2, py: Y2, pz: Z2 } = isPoint(other);  // isPoint() checks class equality
    const X1Z2 = mod(X1 * Z2), X2Z1 = mod(X2 * Z1);
    const Y1Z2 = mod(Y1 * Z2), Y2Z1 = mod(Y2 * Z1);
    return X1Z2 === X2Z1 && Y1Z2 === Y2Z1;
  }
  negate() { return new Point(this.px, mod(-this.py), this.pz); } // Flip point over y coord
  double() { return this.add(this); }                   // Point doubling: P+P, complete formula.
  add(other: Point) {                                   // Point addition: P+Q, complete, exception
    const { px: X1, py: Y1, pz: Z1 } = this;            // free formula from Renes-Costello-Batina
    const { px: X2, py: Y2, pz: Z2 } = isPoint(other);  // https://eprint.iacr.org/2015/1060, algo 1
    const { a, b } = CURVE;                             // Cost: 12M + 0S + 3*a + 3*b3 + 23add
    let X3 = 0n, Y3 = 0n, Z3 = 0n;
    const b3 = mod(b * 3n);
    let t0 = mod(X1 * X2), t1 = mod(Y1 * Y2), t2 = mod(Z1 * Z2), t3 = mod(X1 + Y1); // step 1
    let t4 = mod(X2 + Y2);                              // step 5
    t3 = mod(t3 * t4); t4 = mod(t0 + t1); t3 = mod(t3 - t4); t4 = mod(X1 + Z1);
    let t5 = mod(X2 + Z2);                              // step 10
    t4 = mod(t4 * t5); t5 = mod(t0 + t2); t4 = mod(t4 - t5); t5 = mod(Y1 + Z1);
    X3 = mod(Y2 + Z2);                                  // step 15
    t5 = mod(t5 * X3); X3 = mod(t1 + t2); t5 = mod(t5 - X3); Z3 = mod(a * t4);
    X3 = mod(b3 * t2);                                  // step 20
    Z3 = mod(X3 + Z3); X3 = mod(t1 - Z3); Z3 = mod(t1 + Z3); Y3 = mod(X3 * Z3);
    t1 = mod(t0 + t0);                                  // step 25
    t1 = mod(t1 + t0); t2 = mod(a * t2); t4 = mod(b3 * t4); t1 = mod(t1 + t2);
    t2 = mod(t0 - t2);                                  // step 30
    t2 = mod(a * t2); t4 = mod(t4 + t2); t0 = mod(t1 * t4); Y3 = mod(Y3 + t0);
    t0 = mod(t5 * t4);                                  // step 35
    X3 = mod(t3 * X3); X3 = mod(X3 - t0); t0 = mod(t3 * t1); Z3 = mod(t5 * Z3);
    Z3 = mod(Z3 + t0);                                  // step 40
    return new Point(X3, Y3, Z3);
  }
  mul(n: bigint, safe = true) {                         // Point scalar multiplication.
    if (!safe && n === 0n) return I;                    // in unsafe mode, allow zero
    if (!ge(n)) err('invalid scalar');                  // must be 0 < n < CURVE.n
    if (this.equals(G)) return wNAF(n).p;               // use precomputes for base point
    let p = I, f = G;                                   // init result point & fake point
    for (let d: Point = this; n > 0n; d = d.double(), n >>= 1n) { // double-and-add ladder
      if (n & 1n) p = p.add(d);                         // if bit is present, add to point
      else if (safe) f = f.add(d);                      // if not, add to fake for timing safety
    }
    return p;
  }
  mulAddQUns(R: Point, u1: bigint, u2: bigint) {        // Double scalar mult. Q = u1⋅G + u2⋅R.
    return this.mul(u1, false).add(R.mul(u2, false)).ok(); // Unsafe: do NOT use for stuff related
  }                                                     // to private keys. Doesn't use Shamir trick
  toAffine(): AffinePoint {                             // Convert point to 2d xy affine point.
    const { px: x, py: y, pz: z } = this;               // (x, y, z) ∋ (x=x/z, y=y/z)
    if (this.equals(I)) return { x: 0n, y: 0n };        // fast-path for zero point
    if (z === 1n) return { x, y };                      // if z is 1, pass affine coordinates as-is
    const iz = inv(z);                                  // z^-1: invert z
    if (mod(z * iz) !== 1n) err('invalid inverse');     // (z * z^-1) must be 1, otherwise bad math
    return { x: mod(x * iz), y: mod(y * iz) };          // x = x*z^-1; y = y*z^-1
  }
  assertValidity(): Point {                             // Checks if the point is valid and on-curve
    const { x, y } = this.aff();                        // convert to 2d xy affine point.
    if (!fe(x) || !fe(y)) err('Point invalid: x or y'); // x and y must be in range 0 < n < P
    return mod(y * y) === crv(x) ?                      // y² = x³ + ax + b, must be equal
      this : err('Point invalid: not on curve');
  }
  multiply(n: bigint) { return this.mul(n); }           // Aliases to compress code
  aff() { return this.toAffine(); }
  ok() { return this.assertValidity(); }
  toHex(isCompressed = true) {                          // Encode point to hex string.
    const { x, y } = this.aff();                        // convert to 2d xy affine point
    const head = isCompressed ? ((y & 1n) === 0n ? '02' : '03') : '04'; // 0x02, 0x03, 0x04 prefix
    return head + n2h(x) + (isCompressed ? '' : n2h(y));// prefix||x and ||y
  }
  toRawBytes(isCompressed = true) {                     // Encode point to Uint8Array.
    return h2b(this.toHex(isCompressed));               // re-use toHex(), convert hex to bytes
  }
}
const { BASE: G, ZERO: I } = Point;                     // Generator, identity points
const padh = (n: number | bigint, pad: number) => n.toString(16).padStart(pad, '0');
const b2h = (b: Bytes): string => Array.from(b).map(e => padh(e, 2)).join(''); // bytes to hex
const h2b = (hex: string): Bytes => {                   // hex to bytes
  const l = hex.length;                                 // error if not string,
  if (!str(hex) || l % 2) err('hex invalid 1');         // or has odd length like 3, 5.
  const arr = u8n(l / 2);                               // create result array
  for (let i = 0; i < arr.length; i++) {
    const j = i * 2;
    const h = hex.slice(j, j + 2);                      // hexByte. slice is faster than substr
    const b = Number.parseInt(h, 16);                   // byte, created from string part
    if (Number.isNaN(b) || b < 0) err('hex invalid 2'); // byte must be valid 0 <= byte < 256
    arr[i] = b;
  }
  return arr;
};
const b2n = (b: Bytes): bigint => BigInt('0x' + (b2h(b) || '0')); // bytes to number
const slcNum = (b: Bytes, from: number, to: number) => b2n(b.slice(from, to)); // slice bytes num
const n2b = (num: bigint): Bytes => {                   // number to 32b. Must be 0 <= num < B256
  return big(num) && num >= 0n && num < B256 ? h2b(padh(num, 2 * fLen)) : err('bigint expected');
};
const n2h = (num: bigint): string => b2h(n2b(num));     // number to 32b hex
const concatB = (...arrs: Bytes[]) => {                 // concatenate Uint8Array-s
  const r = u8n(arrs.reduce((sum, a) => sum + au8(a).length, 0)); // create u8a of summed length
  let pad = 0;                                          // walk through each array,
  arrs.forEach(a => {r.set(a, pad); pad += a.length});  // ensure they have proper type
  return r;
};
const inv = (num: bigint, md = P): bigint => {          // modular inversion
  if (num === 0n || md <= 0n) err('no inverse n=' + num + ' mod=' + md); // no neg exponent for now
  let a = mod(num, md), b = md, x = 0n, y = 1n, u = 1n, v = 0n;
  while (a !== 0n) {                                    // uses euclidean gcd algorithm
    const q = b / a, r = b % a;                         // not constant-time
    const m = x - u * q, n = y - v * q;
    b = a, a = r, x = u, y = v, u = m, v = n;
  }
  return b === 1n ? mod(x, md) : err('no inverse');     // b is gcd at this point
};
const sqrt = (n: bigint) => {                           // √n = n^((p+1)/4) for fields p = 3 mod 4
  let r = 1n;     // So, a special, fast case. Paper: "Square Roots from 1;24,51,10 to Dan Shanks".
  for (let num = n, e = (P + 1n) / 4n; e > 0n; e >>= 1n) { // powMod: modular exponentiation.
    if (e & 1n) r = (r * num) % P;                      // Uses exponentiation by squaring.
    num = (num * num) % P;                              // Not constant-time.
  }
  return mod(r * r) === n ? r : err('sqrt invalid');    // check if result is valid
};
const toPriv = (p: PrivKey): bigint => {                // normalize private key to bigint
  if (!big(p)) p = b2n(toU8(p, fLen));                  // convert to bigint when bytes
  return ge(p) ? p : err('private key out of range');   // check if bigint is in range
};
const moreThanHalfN = (n: bigint): boolean => n > (N >> 1n); // if a number is bigger than CURVE.n/2
const getPublicKey = (privKey: PrivKey, isCompressed = true) => {   // Make public key from priv
  return Point.fromPrivateKey(privKey).toRawBytes(isCompressed);        // 33b or 65b output
}
type SignatureWithRecovery = Signature & { recovery: number }
class Signature {                                       // ECDSA Signature class
  constructor(readonly r: bigint, readonly s: bigint, readonly recovery?: number) {
    this.assertValidity();                              // recovery bit is optional when
  }                                                     // constructed outside.
  static fromCompact(hex: Hex) {                        // create signature from 64b compact repr
    hex = toU8(hex, 64);                                // compact repr is (32b r)||(32b s)
    return new Signature(slcNum(hex, 0, fLen), slcNum(hex, fLen, 2 * fLen));
  }
  assertValidity() { return ge(this.r) && ge(this.s) ? this : err(); } // 0 < r or s < CURVE.n
  addRecoveryBit(rec: number): SignatureWithRecovery {
    return new Signature(this.r, this.s, rec) as SignatureWithRecovery;
  }
  hasHighS() { return moreThanHalfN(this.s); }
  normalizeS() {
    return this.hasHighS() ? new Signature(this.r, mod(this.s, N), this.recovery) : this
  }
  recoverPublicKey(msgh: Hex): Point {                  // ECDSA public key recovery
    const { r, s, recovery: rec } = this;               // secg.org/sec1-v2.pdf 4.1.6
    if (![0, 1, 2, 3].includes(rec!)) err('recovery id invalid'); // check recovery id
    const h = bits2int_modN(toU8(msgh, fLen));          // Truncate hash
    const radj = rec === 2 || rec === 3 ? r + N : r;    // If rec was 2 or 3, q.x is bigger than n
    if (radj >= P) err('q.x invalid');                  // ensure q.x is still a field element
    const head = (rec! & 1) === 0 ? '02' : '03';        // head is 0x02 or 0x03
    const R = Point.fromHex(head + n2h(radj));          // concat head + hex repr of r
    const ir = inv(radj, N);                            // r^-1
    const u1 = mod(-h * ir, N);                         // -hr^-1
    const u2 = mod(s * ir, N);                          // sr^-1
    return G.mulAddQUns(R, u1, u2);                     // (sr^-1)R-(hr^-1)G = -(hr^-1)G + (sr^-1)
  }
  toCompactRawBytes() { return h2b(this.toCompactHex()); } // Uint8Array 64b compact repr
  toCompactHex() { return n2h(this.r) + n2h(this.s); }  // hex 64b compact repr
}
const bits2int = (bytes: Uint8Array): bigint => {       // RFC6979: ensure ECDSA msg is X bytes.
  const delta = bytes.length * 8 - 256; // RFC suggests optional truncating via bits2octets
  const num = b2n(bytes); // FIPS 186-4 4.6 suggests the leftmost min(nBitLen, outLen) bits, which
  return delta > 0 ? num >> BigInt(delta) : num; // matches bits2int. bits2int can produce res>N.
};
const bits2int_modN = (bytes: Uint8Array): bigint => {  // int2octets can't be used; pads small msgs
  return mod(bits2int(bytes), N);                       // with 0: BAD for trunc as per RFC vectors
};
const i2o = (num: bigint): Bytes => n2b(num);           // int to octets
declare const globalThis: Record<string, any> | undefined; // Typescript symbol present in browsers
const cr = () => // We support: 1) browsers 2) node.js 19+ 3) deno, other envs with crypto
  typeof globalThis === 'object' && 'crypto' in globalThis ? globalThis.crypto : undefined;
type HmacFnSync = undefined | ((key: Bytes, ...msgs: Bytes[]) => Bytes);
let _hmacSync: HmacFnSync;    // Can be redefined by use in utils; built-ins don't provide it
const optS: { lowS?: boolean; extraEntropy?: boolean | Hex; } = { lowS: true }; // opts for sign()
const optV: { lowS?: boolean } = { lowS: true };        // standard opts for verify()
type BC = { seed: Bytes, k2sig : (kb: Bytes) => SignatureWithRecovery | undefined }; // Bytes+predicate checker
const prepSig = (msgh: Hex, priv: PrivKey, opts=optS): BC => {// prepare for RFC6979 sig generation
  if (['der', 'recovered', 'canonical'].some(k => k in opts)) // Ban legacy options
    err('sign() legacy options not supported');
  let { lowS } = opts;                                  // generates low-s sigs by default
  if (lowS == null) lowS = true;                        // RFC6979 3.2: we skip step A
  const h1i = bits2int_modN(toU8(msgh));                // msg bigint
  const h1o = i2o(h1i);                                 // msg octets
  const d = toPriv(priv);                               // validate private key, convert to bigint
  const seed = [i2o(d), h1o];                           // Step D of RFC6979 3.2
  let ent = opts.extraEntropy;                          // RFC6979 3.6: additional k' (optional)
  if (ent) {        // K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1) || k')
    if (ent === true) ent = etc.randomBytes(fLen);      // if true, use CSPRNG to generate data
    const e = toU8(ent);                                // convert Hex|Bytes to Bytes
    if (e.length !== fLen) err();                       // Expected 32 bytes of extra data
    seed.push(e);
  }
  const m = h1i;                                        // convert msg to bigint
  const k2sig = (kBytes: Bytes): SignatureWithRecovery | undefined => { // Transform k => Signature.
    const k = bits2int(kBytes);                         // RFC6979 method.
    if (!ge(k)) return;                                 // Check 0 < k < CURVE.n
    const ik = inv(k, N);                               // k^-1 mod n, NOT mod P
    const q = G.mul(k).aff();                           // q = Gk
    const r = mod(q.x, N);                              // r = q.x mod n
    if (r === 0n) return;                               // r=0 invalid
    const s = mod(ik * mod(m + mod(d * r, N), N), N);   // s = k^-1(m + rd) mod n
    if (s === 0n) return;                               // s=0 invalid
    let normS = s;                                      // normalized S
    let rec = (q.x === r ? 0 : 2) | Number(q.y & 1n);   // recovery bit
    if (lowS && moreThanHalfN(s)) {                     // if lowS was passed, ensure s is always
      normS = mod(-s, N);                               // in the bottom half of CURVE.n
      rec ^= 1;
    }
    return new Signature(r, normS, rec) as SignatureWithRecovery;       // use normS, not s
  };
  return { seed: concatB(...seed), k2sig }
}
type Pred<T> = (v: Uint8Array) => T | undefined;
function hmacDrbg<T>(asynchronous: true): (seed: Bytes, predicate: Pred<T>) => Promise<T>;
function hmacDrbg<T>(asynchronous: false): (seed: Bytes, predicate: Pred<T>) => T;
function hmacDrbg<T>(asynchronous: boolean) { // HMAC-DRBG async
  let v = u8n(fLen);  // Minimal non-full-spec HMAC-DRBG from NIST 800-90 for RFC6979 sigs.
  let k = u8n(fLen);  // Steps B, C of RFC6979 3.2: set hashLen, in our case always same
  let i = 0;          // Iterations counter, will throw when over 1000
  const reset = () => { v.fill(1); k.fill(0); i = 0; };
  const _e = 'drbg: tried 1000 values';
  if (asynchronous) {                                   // asynchronous=true
    const h = (...b: Bytes[]) => etc.hmacSha256Async(k, v, ...b); // hmac(k)(v, ...values)
    const reseed = async (seed = u8n()) => {            // HMAC-DRBG reseed() function. Steps D-G
      k = await h(u8n([0x00]), seed);                   // k = hmac(K || V || 0x00 || seed)
      v = await h();                                    // v = hmac(K || V)
      if (seed.length === 0) return;
      k = await h(u8n([0x01]), seed);                   // k = hmac(K || V || 0x01 || seed)
      v = await h();                                    // v = hmac(K || V)
    };
    const gen = async () => {                           // HMAC-DRBG generate() function
      if (i++ >= 1000) err(_e);
      v = await h();                                    // v = hmac(K || V)
      return v;
    };
    return async (seed: Bytes, pred: Pred<T>): Promise<T> => { // Even though it feels safe to reuse
      reset(); // the returned fn, don't, it's: 1. slower (JIT). 2. unsafe (async race conditions)
      await reseed(seed);                               // Steps D-G
      let res: T | undefined = undefined;               // Step H: grind until k is in [1..n-1]
      while (!(res = pred(await gen()))) await reseed();// test predicate until it returns ok
      reset();
      return res!;
    };
  } else {
    const h = (...b: Bytes[]) => {                      // asynchronous=false; same, but synchronous
      const f = _hmacSync;
      if (!f) err('etc.hmacSha256Sync not set');
      return f!(k, v, ...b);                            // hmac(k)(v, ...values)
    };
    const reseed = (seed = u8n()) => {                  // HMAC-DRBG reseed() function. Steps D-G
      k = h(u8n([0x00]), seed);                         // k = hmac(k || v || 0x00 || seed)
      v = h();                                          // v = hmac(k || v)
      if (seed.length === 0) return;
      k = h(u8n([0x01]), seed);                         // k = hmac(k || v || 0x01 || seed)
      v = h();                                          // v = hmac(k || v)
    };
    const gen = () => {                                 // HMAC-DRBG generate() function
      if (i++ >= 1000) err(_e);
      v = h();                                          // v = hmac(k || v)
      return v;
    };
    return (seed: Bytes, pred: Pred<T>): T => {
      reset();
      reseed(seed);                                     // Steps D-G
      let res: T | undefined = undefined;               // Step H: grind until k is in [1..n-1]
      while (!(res = pred(gen()))) reseed();            // test predicate until it returns ok
      reset();
      return res!;
    };
  }
}
// ECDSA signature generation. via secg.org/sec1-v2.pdf 4.1.2 + RFC6979 deterministic k
const signAsync = async (msgh: Hex, priv: PrivKey, opts = optS): Promise<SignatureWithRecovery> => {
  const { seed, k2sig } = prepSig(msgh, priv, opts);    // Extract arguments for hmac-drbg
  return hmacDrbg<SignatureWithRecovery>(true)(seed, k2sig);  // Re-run drbg until k2sig returns ok
}
const sign = (msgh: Hex, priv: PrivKey, opts = optS): SignatureWithRecovery => {
  const { seed, k2sig } = prepSig(msgh, priv, opts);    // Extract arguments for hmac-drbg
  return hmacDrbg<SignatureWithRecovery>(false)(seed, k2sig); // Re-run drbg until k2sig returns ok
}
type SigLike = { r: bigint, s: bigint };
const verify = (sig: Hex | SigLike, msgh: Hex, pub: Hex, opts = optV): boolean => {
  let { lowS } = opts;                                  // ECDSA signature verification
  if (lowS == null) lowS = true;                        // Default lowS=true
  if ('strict' in opts) err('verify() legacy options not supported'); // legacy param
  let sig_: Signature, h: bigint, P: Point;             // secg.org/sec1-v2.pdf 4.1.4
  const rs = sig && typeof sig === 'object' && 'r' in sig; // Previous ver supported DER sigs. We
  if (!rs && (toU8(sig).length !== 2 * fLen))           // throw error when DER is suspected now.
    err('signature must be 64 bytes');
  try {
    sig_ = rs ? new Signature(sig.r, sig.s).assertValidity() : Signature.fromCompact(sig);
    h = bits2int_modN(toU8(msgh));                // Truncate hash
    P = pub instanceof Point ? pub.ok() : Point.fromHex(pub); // Validate public key
  } catch (e) { return false; }                         // Check sig for validity in both cases
  if (!sig_) return false;
  const { r, s } = sig_;
  if (lowS && moreThanHalfN(s)) return false;           // lowS bans sig.s >= CURVE.n/2
  let R: AffinePoint;
  try {
    const is = inv(s, N);                               // s^-1
    const u1 = mod(h * is, N);                          // u1 = hs^-1 mod n
    const u2 = mod(r * is, N);                          // u2 = rs^-1 mod n
    R = G.mulAddQUns(P, u1, u2).aff();                  // R = u1⋅G + u2⋅P
  } catch (error) { return false; }
  if (!R) return false;                                 // stop if R is identity / zero point
  const v = mod(R.x, N);                                // R.x must be in N's field, not P's
  return v === r;                                       // mod(R.x, n) == r
}
const getSharedSecret = (privA: Hex, pubB: Hex, isCompressed = true): Bytes => {
  return Point.fromHex(pubB).mul(toPriv(privA)).toRawBytes(isCompressed); // ECDH
}
const hashToPrivateKey = (hash: Hex): Bytes => {        // FIPS 186 B.4.1 compliant key generation
  hash = toU8(hash);                                    // produces private keys with modulo bias
  const minLen = fLen + 8;                              // being neglible.
  if (hash.length < minLen || hash.length > 1024) err('expected proper params');
  const num = mod(b2n(hash), N - 1n) + 1n;              // takes at least n+8 bytes
  return n2b(num);
}
const etc = {                                           // Not placed in utils because they
  hexToBytes: h2b, bytesToHex: b2h,                     // share API with noble-curves.
  concatBytes: concatB, bytesToNumberBE: b2n, numberToBytesBE: n2b,
  mod, invert: inv,                                     // math utilities
  hmacSha256Async: async (key: Bytes, ...msgs: Bytes[]): Promise<Bytes> => {
    const c = cr();                                     // async HMAC-SHA256, no sync built-in!
    const s = c && c.subtle;                            // For React Native support, see README.
    if (!s) return err('etc.hmacSha256Async not set');  // Uses webcrypto built-in cryptography.
    const k = await s.importKey('raw', key, {name:'HMAC',hash:{name:'SHA-256'}}, false, ['sign']);
    return u8n(await s.sign('HMAC', k, concatB(...msgs)));
  },
  hmacSha256Sync: _hmacSync,                            // For TypeScript. Actual logic is below
  hashToPrivateKey,
  randomBytes: (len = 32): Bytes => {                   // CSPRNG (random number generator)
    const crypto = cr(); // Must be shimmed in node.js <= 18 to prevent error. See README.
    if (!crypto || !crypto.getRandomValues) err('crypto.getRandomValues must be defined');
    return crypto.getRandomValues(u8n(len));
  },
}
const utils = {                                         // utilities
  normPrivateKeyToScalar: toPriv,
  isValidPrivateKey: (key: Hex) => { try { return !!toPriv(key); } catch (e) { return false; } },
  randomPrivateKey: (): Bytes => hashToPrivateKey(etc.randomBytes(fLen + 16)), // FIPS 186 B.4.1.
  precompute(w=8, p: Point = G) { p.multiply(3n); w; return p; }, // no-op
};
Object.defineProperties(etc, { hmacSha256Sync: {        // Allow setting it once, ignore then
  configurable: false, get() { return _hmacSync; }, set(f) { if (!_hmacSync) _hmacSync = f; },
} });
const W = 8;                                            // Precomputes-related code. W = window size
const precompute = () => {                              // They give 12x faster getPublicKey(),
  const points: Point[] = [];                           // 10x sign(), 2x verify(). To achieve this,
  const windows = 256 / W + 1;                          // app needs to spend 40ms+ to calculate
  let p = G, b = p;                                     // a lot of points related to base point G.
  for (let w = 0; w < windows; w++) {                   // Points are stored in array and used
    b = p;                                              // any time Gx multiplication is done.
    points.push(b);                                     // They consume 16-32 MiB of RAM.
    for (let i = 1; i < 2 ** (W - 1); i++) { b = b.add(p); points.push(b); }
    p = b.double();                                     // Precomputes don't speed-up getSharedKey,
  }                                                     // which multiplies user point by scalar,
  return points;                                        // when precomputes are using base point
}
let Gpows: Point[] | undefined = undefined;             // precomputes for base point G
const wNAF = (n: bigint): { p: Point; f: Point } => {   // w-ary non-adjacent form (wNAF) method.
                                                        // Compared to other point mult methods,
  const comp = Gpows || (Gpows = precompute());         // stores 2x less points using subtraction
  const neg = (cnd: boolean, p: Point) => { let n = p.negate(); return cnd ? n : p; } // negate
  let p = I, f = G;                                     // f must be G, or could become I in the end
  const windows = 1 + 256 / W;                          // W=8 17 windows
  const wsize = 2 ** (W - 1);                           // W=8 128 window size
  const mask = BigInt(2 ** W - 1);                      // W=8 will create mask 0b11111111
  const maxNum = 2 ** W;                                // W=8 256
  const shiftBy = BigInt(W);                            // W=8 8
  for (let w = 0; w < windows; w++) {
    const off = w * wsize;
    let wbits = Number(n & mask);                       // extract W bits.
    n >>= shiftBy;                                      // shift number by W bits.
    if (wbits > wsize) { wbits -= maxNum; n += 1n; }    // split if bits > max: +224 => 256-32
    const off1 = off, off2 = off + Math.abs(wbits) - 1; // offsets, evaluate both
    const cnd1 = w % 2 !== 0, cnd2 = wbits < 0;         // conditions, evaluate both
    if (wbits === 0) {
      f = f.add(neg(cnd1, comp[off1]));                 // bits are 0: add garbage to fake point
    } else {                                            //          ^ can't add off2, off2 = I
      p = p.add(neg(cnd2, comp[off2]));                 // bits are 1: add to result point
    }
  }
  return { p, f }                                       // return both real and fake points for JIT
};        // !! you can disable precomputes by commenting-out call of the wNAF() inside Point#mul()
export { getPublicKey, sign, signAsync, verify, CURVE,  // Remove the export to easily use in REPL
  getSharedSecret, etc, utils, Point as ProjectivePoint, Signature, pedersenCommitment } // envs like browser console
//

const modPow = (base: bigint, exp: bigint, mod: bigint) => {
  let result = 1n;
  base = etc.mod(base, mod);
  while (exp > 0) {
    if (exp % 2n === 1n) {
      result = etc.mod(result * base, mod);
    }
    exp = exp >> 1n;
    base = etc.mod(base * base, mod);
  }
  return result;
};

const jacobiSymbol = (a: bigint, n: bigint):number => {
  if (a === 0n) return 0;
  if (a === 1n) return 1;

  let s;
  if (a % 2n === 0n) {
    s = jacobiSymbol(a / 2n, n);
    if (n % 8n === 3n || n % 8n === 5n) s = -s;
  } else {
    s = jacobiSymbol(n % a, a);
    if (a % 4n === 3n && n % 4n === 3n) s = -s;
  }
  return s;
};

function serializePoint(point: Point) {
  const data = new Uint8Array(33);
  const yBigInt = BigInt(point.y);
  data[0] = isSquare(yBigInt) ? 0x00 : 0x01;

  const xBigInt = BigInt(point.x);
  const xHex = xBigInt.toString(16).padStart(64, "0");
  const xBytes = Uint8Array.from(Buffer.from(xHex, "hex"));

  data.set(xBytes, 1);

  return data;
}

function isSquare(fe: bigint) {
  const normalized = etc.mod(fe, CURVE.p);

  if (normalized === 0n) return true;

  const jacobi = jacobiSymbol(normalized, CURVE.p);
  if (jacobi === -1) {
    return false;
  } else if (jacobi === 1) {
    return true;
  } else {
    const sqrtResult = sqrt(normalized);
    return sqrtResult ** 2n % CURVE.p === normalized;
  }
}

const pedersenCommitment = (ge: Point) => {
  const xBytes = n2b(ge.x);
  const yIsSquare = isSquare(ge.y);
  const prefixByte = 9 ^ (yIsSquare ? 1 : 0);

  let commit = new Uint8Array(33);
  commit[0] = prefixByte;
  commit.set(xBytes, 1);
  return commit;
}

class SHA256 {
  private _data: Uint8Array[];

  constructor() {
    this._data = [];
  }

  update(data: Bytes) {
    this._data.push(new Uint8Array(data));
    return this; // Enable method chaining
  }

  async digest(): Promise<Bytes> {
    const c = cr();
    const s = c && c.subtle;  // Get subtle API
    if (!s) throw new Error('Web Crypto API not available');

    const concatenatedData = this._concatData(this._data);
    const hashBuffer = await s.digest('SHA-256', concatenatedData);
    return new Uint8Array(hashBuffer);
  }

  private _concatData(chunks: Uint8Array[]): Uint8Array {
    const totalLength = chunks.reduce((sum, chunk) => sum + chunk.length, 0);
    const result = new Uint8Array(totalLength);
    let offset = 0;
    for (const chunk of chunks) {
      result.set(chunk, offset);
      offset += chunk.length;
    }
    return result;
  }

  static create(): SHA256 {
    return new SHA256();
  }
}

const borromeanHash = async (m: Bytes, e: Bytes, ridx: number, eidx: number) => {
  const ring = new Uint8Array(4);
  const epos = new Uint8Array(4);

  const writeBe32 = (buffer: Bytes, value: number) => {
    buffer[0] = (value >> 24) & 0xff;
    buffer[1] = (value >> 16) & 0xff;
    buffer[2] = (value >> 8) & 0xff;
    buffer[3] = value & 0xff;
  };

  writeBe32(ring, ridx);
  writeBe32(epos, eidx);

  const sha256Context = SHA256.create();
  sha256Context.update(e);
  sha256Context.update(m);
  sha256Context.update(ring);
  sha256Context.update(epos);

  return sha256Context.digest();
}

function clz64(x: bigint) {
  if (x === 0n) return 64;
  let n = 0;
  while ((x & 0x8000000000000000n) === 0n) {
    x <<= 1n;
    n++;
  }
  return n;
}

type ProveParams = {
  rings: number,
  rsizes: number[],
  npub: number,
  secidx: number[],
  minValue: bigint,
  mantissa: number,
  scale: bigint,
  minBits: number,
  v: bigint,
  exp: number,
}

const rangeProveParams = (minBits: number, minValue: bigint, exp: number, value: bigint): ProveParams => {
  let i, v;
  let rsizes = new Array(32);
  let secidx = new Array(32);
  let rings = 1;
  rsizes[0] = 1;
  secidx[0] = 0;
  let scale = 1n;
  let mantissa = 0;
  let npub = 0;

  if (minValue === 0xffffffffffffffffn) exp = -1;

  if (exp >= 0) {
    let maxBits;
    let v2;
    if (
      (minValue && value > 0x7fffffffffffffffn) ||
      (value && minValue >= 0x7fffffffffffffffn)
    ) {
      throw new Error("value out of range");
    }
    maxBits = minValue ? clz64(BigInt(minValue)) : 64;
    if (minBits > maxBits) {
      minBits = maxBits;
    }
    if (minBits > 61 || value > 0x7fffffffffffffffn) {
      exp = 0;
    }
    v = value - BigInt(minValue);
    v2 = minBits ? 0xffffffffffffffffn >> BigInt(64 - minBits) : 0n;
    for (i = 0; i < exp && v2 <= 0xffffffffffffffffn / 10n; i++) {
      v /= 10n;
      v2 *= 10n;
    }
    exp = i;
    v2 = v;
    for (i = 0; i < exp; i++) {
      v2 *= 10n;
      scale *= 10n;
    }
    minValue = value - v2;
    mantissa = v ? 64 - clz64(v) : 1;
    if (minBits > mantissa) {
      mantissa = minBits;
    }
    rings = (mantissa + 1) >> 1;
    for (i = 0; i < rings; i++) {
      rsizes[i] = i < rings - 1 || !(mantissa & 1) ? 4 : 2;
      npub += rsizes[i];
      secidx[i] = Number((v >> BigInt(i * 2)) & 3n);
    }
    if (mantissa <= 0) throw new Error("Invalid mantissa value");
    if ((v & ~(0xffffffffffffffffn >> BigInt(64 - mantissa))) !== 0n)
      throw new Error("Did not get all the bits");
  } else {
    exp = 0;
    minValue = value;
    v = 0n;
    npub = 2;
  }

  if (v * scale + minValue !== value) throw new Error("Invalid value");
  if (rings <= 0 || rings > 32) throw new Error("Invalid number of rings");
  if (npub > 128) throw new Error("Invalid number of public keys");

  return {
    rings,
    rsizes,
    npub,
    secidx,
    minValue,
    mantissa,
    scale,
    minBits,
    v,
    exp,
  };
}

const borromeanSign = async (e0: Bytes, s: bigint[], pubs: Point[], k: bigint[], sec: bigint[], rsizes: number[], secidx: number[], nrings: number, m: Bytes) => {
  let rgej;
  let tmp = new Uint8Array(33);
  let count = 0;

  if (!e0 || !s || !pubs || !k || !sec || !rsizes || !secidx || !nrings || !m) {
    throw new Error("Invalid input");
  }

  const sha256_e0 = SHA256.create();
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    rgej = G.mul(k[i]);
    if (rgej.equals(Point.ZERO)) {
      return 0;
    }

    tmp = rgej.toRawBytes(true);

    for (let j = secidx[i] + 1; j < rsizes[i]; j++) {
      tmp = await borromeanHash(m, tmp, i, j);
      let ens = b2n(tmp);
      if (ens >= CURVE.n) ens = ens % CURVE.n;

      rgej = pubs[count + j].multiply(ens).add(G.mul(s[count + j]));
      if (rgej.equals(Point.ZERO)) {
        return 0;
      }

      tmp = rgej.toRawBytes(true);
    }

    sha256_e0.update(tmp);
    count += rsizes[i];
  }

  sha256_e0.update(m);
  let digest = await sha256_e0.digest();
  e0.set(digest);

  count = 0;
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    tmp = await borromeanHash(m, e0.slice(0, 32), i, 0);
    let ens = b2n(tmp) % CURVE.n;

    if (ens === 0n || ens >= CURVE.n) {
      return 0;
    }

    for (let j = 0; j < secidx[i]; j++) {
      rgej = pubs[count + j].mul(ens).add(G.mul(s[count + j]));

      if (rgej.equals(Point.ZERO)) {
        return 0;
      }

      tmp = rgej.toRawBytes(true);
      tmp = await borromeanHash(m, tmp, i, j + 1);
      ens = b2n(tmp) % CURVE.n;

      if (ens === 0n || ens >= CURVE.n) {
        return 0;
      }
    }

    s[count + secidx[i]] =
      (CURVE.n - ((ens * sec[i]) % CURVE.n) + k[i]) % CURVE.n;

    if (s[count + secidx[i]] === 0n) {
      return 0;
    }

    count += rsizes[i];
  }

  return 1;
}

const rangeproofPubExpand = (pubs: Point[], exp: number, rsizes: number[], rings: number, genp: string) => {
  var base = Point.fromHex(genp);
  var i, j, npub;
  if (exp < 0) {
    exp = 0;
  }

  base = base.negate();

  while (exp--) {
    var tmp = base.double();
    base = tmp.double().add(tmp);
  }

  npub = 0;
  for (i = 0; i < rings; i++) {
    for (j = 1; j < rsizes[i]; j++) {
      pubs[npub + j] = pubs[npub + j - 1].add(base);
    }
    if (i < rings - 1) {
      base = base.double().double();
    }
    npub += rsizes[i];
  }
}

async function rangeproofSign(
  minValue: bigint,
  commit: string,
  blind: string,
  nonce: string,
  exp: number,
  minBits: number,
  value: bigint,
  msg: string,
  extraCommit: string,
  genp: string,
) {
  let proof = new Uint8Array(5134);
  let pubs = new Array(128);
  let s = new Array(128);
  let sec = new Array(32);
  let k = new Array(32);
  let sha256M = SHA256.create();
  let prep = new Uint8Array(4096);
  let len;
  let i;

  let genP = Point.fromHex(genp);

  len = 0;
  if (minValue > value || minBits > 64 || minBits < 0 || exp < -1 || exp > 18) {
    return 0;
  }

  let v, rings, rsizes, npub, secidx, mantissa, scale;
  ({ v, rings, rsizes, npub, secidx, mantissa, scale, exp, minBits, minValue } = await rangeProveParams(minBits, minValue, exp, value));
  
  if (!v) return 0;

  proof[len] = (rsizes[0] > 1 ? 64 | exp : 0) | (minValue ? 32 : 0);
  len++;
  if (rsizes[0] > 1) {
    if (mantissa <= 0 || mantissa > 64) {
      throw new Error("Mantissa out of range");
    }
    proof[len] = mantissa - 1;
    len++;
  }
  if (minValue) {
    for (i = 0; i < 8; i++) {
      proof[len + i] = Number((minValue >> BigInt((7 - i) * 8)) & BigInt(255));
    }
    len += 8;
  }
  if (msg.length > 0 && msg.length > 128 * (rings - 1)) {
    return 0;
  }

  sha256M.update(h2b(commit));
  sha256M.update(serializePoint(genP));
  sha256M.update(proof.slice(0, len));

  prep.fill(0);
  if (msg != null) {
    prep.set(h2b(msg).slice(0, msg.length));
  }

  if (rsizes[rings - 1] > 1) {
    let idx = rsizes[rings - 1] - 1;
    idx -= Number(secidx[rings - 1] === idx);
    idx = ((rings - 1) * 4 + idx) * 32;
    for (i = 0; i < 8; i++) {
      let n = Number((v >> BigInt(56 - i * 8)) & BigInt(255));
      prep[8 + i + idx] = prep[16 + i + idx] = prep[24 + i + idx] = n;
      prep[i + idx] = 0;
    }
    prep[idx] = 128;
  }

  if (
    !(await rangeproofGenrand(
      sec,
      s,
      prep,
      rsizes,
      rings,
      nonce,
      commit,
      proof,
      len,
      genp,
    ))
  ) {
    return 0;
  }

  prep.fill(0);
  for (i = 0; i < rings; i++) {
    k[i] = s[i * 4 + secidx[i]];
    s[i * 4 + secidx[i]] = 0n;
  }

  let stmp = setScalarFromB32(h2b(blind));
  sec[rings - 1] = (sec[rings - 1] + stmp) % CURVE.n;

  let signs = new Uint8Array(proof.buffer, len, (rings + 6) >> 3);

  for (i = 0; i < (rings + 6) >> 3; i++) {
    signs[i] = 0;
    len++;
  }
  npub = 0;
  for (i = 0; i < rings; i++) {
    let val = (BigInt(secidx[i]) * scale) << BigInt(i * 2);
    let P1 = sec[i] ? G.mul(sec[i]) : I;
    let P2 = secidx[i] ? genP.mul(val) : I;
    pubs[npub] = P1.add(P2);

    if (pubs[npub].equals(I)) return 0;

    if (i < rings - 1) {
      var tmpc = serializePoint(pubs[npub]);
      var quadness = tmpc[0];
      sha256M.update(tmpc);
      signs[i >> 3] |= quadness << (i & 7);
      proof.set(tmpc.slice(1), len);
      len += 32;
    }
    npub += rsizes[i];
  }

  rangeproofPubExpand(pubs, exp, rsizes, rings, genp);
  if (extraCommit != null) {
    sha256M.update(h2b(extraCommit));
  }
  
  let signed = await borromeanSign(
    proof.subarray(len),
    s,
    pubs,
    k,
    sec,
    rsizes,
    secidx,
    rings,
    await sha256M.digest(),
  );

  if (!signed) return 0;

  len += 32;
  for (let i = 0; i < npub; i++) {
    proof.set(n2b(s[i]), len);
    len += 32;
  }

  proof = proof.slice(0, len);
  return proof;
}

class RNG {
  constructor(k: Bytes, v: Bytes, retry = false) {
    this.k = k;
    this.v = v;
    this.retry = retry;
  }

  static async create(key) {
    const zero = new Uint8Array([0x00]);
    const one = new Uint8Array([0x01]);

    let v = new Uint8Array(32).fill(0x01); // RFC6979 3.2.b.
    let k = new Uint8Array(32).fill(0x00); // RFC6979 3.2.c.

    // RFC6979 3.2.d.
    k = await hmacSha256Async(k, v, zero, key);
    v = await hmacSha256Async(k, v);

    // RFC6979 3.2.f.
    k = await hmacSha256Async(k, v, one, key);
    v = await hmacSha256Async(k, v);

    return new RNG(k, v, false);
  }

  async generate(out, outlen) {
    const zero = new Uint8Array([0x00]);
    if (this.retry) {
      this.k = await hmacSha256Async(this.k, this.v, zero);
      this.v = await hmacSha256Async(this.k, this.v);
    }

    while (outlen > 0) {
      let now = outlen > 32 ? 32 : outlen;
      this.v = await hmacSha256Async(this.k, this.v);
      out.set(this.v.slice(0, now), out.length - outlen);
      outlen -= now;
    }

    this.retry = true;
  }

  finalize() {
    this.k.fill(0);
    this.v.fill(0);
    this.retry = false;
  }
}

// let negateScalar = (a) => (a === 0n ? 0n : (CURVE.n - a) % CURVE.n);
let negateScalar = (a) => {
  if (a === 0n) {
    return 0n;
  }

  // Handle negation with modular arithmetic
  let result = CURVE.n - a;

  // Ensure result is in the range [0, CURVE.n - 1]
  if (result < 0n) {
    result += CURVE.n;
  } else if (result >= CURVE.n) {
    result -= CURVE.n;
  }

  return result;
};

async function rangeproofGenrand(
  sec,
  s,
  message,
  rsizes,
  rings,
  nonce,
  commit,
  proof,
  len,
  gen,
) {
  let tmp = new Uint8Array(32);
  let rngseed = new Uint8Array(32 + 33 + 33 + len);
  let acc = 0n;
  let overflow;
  let ret = 1;
  let npub = 0;

  if (len > 10) {
    throw new Error("Invalid length");
  }

  let slice = commit.slice(2);
  const genP = Point.fromHex(gen);
  const commitP = Point.fromHex("02" + slice);

  rngseed.set(h2b(nonce).slice(0, 32), 0);
  rngseed.set(serializePoint(commitP), 32);
  rngseed.set(serializePoint(genP), 32 + 33);
  rngseed.set(proof.slice(0, len), 32 + 33 + 33);

  let rng = await RNG.create(rngseed);

  for (let i = 0; i < rings; i++) {
    if (i < rings - 1) {
      await rng.generate(tmp, 32);
      do {
        await rng.generate(tmp, 32);
        sec[i] = b2n(tmp) % CURVE.n;
      } while (b2n(tmp) > CURVE.n || sec[i] === 0n);
      acc = (acc + sec[i]) % CURVE.n;
    } else {
      sec[i] = negateScalar(acc);
    }

    for (let j = 0; j < rsizes[i]; j++) {
      await rng.generate(tmp, 32);
      if (message) {
        for (let b = 0; b < 32; b++) {
          tmp[b] ^= message[(i * 4 + j) * 32 + b];
          message[(i * 4 + j) * 32 + b] = tmp[b];
        }
      }
      s[npub] = b2n(tmp) % CURVE.n;
      ret &= s[npub] !== 0n;
      npub++;
    }
  }
  acc = 0n;

  return ret;
}

const setScalarFromB32 = (b32) => {
  if (b32.length !== 32) {
    throw new Error("Input must be a 32-byte array");
  }

  const d0 = b2n(b32.slice(24, 32));
  const d1 = b2n(b32.slice(16, 24));
  const d2 = b2n(b32.slice(8, 16));
  const d3 = b2n(b32.slice(0, 8));

  let scalar = (d3 << 192n) | (d2 << 128n) | (d1 << 64n) | d0;

  if (scalar >= CURVE.n) {
    scalar -= CURVE.n;
  }

  return scalar;
};
