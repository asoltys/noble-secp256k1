/*! noble-secp256k1 - MIT License (c) Paul Miller (paulmillr.com) */
export declare const P: bigint;
export declare const PRIME_ORDER: bigint;
declare type PrivKey = Uint8Array | string | bigint | number;
declare type PubKey = Uint8Array | string | Point;
declare type Hex = Uint8Array | string;
declare type Signature = Uint8Array | string | SignResult;
export declare class Point {
    x: bigint;
    y: bigint;
    constructor(x: bigint, y: bigint);
    private static fromCompressedHex;
    private static fromUncompressedHex;
    static fromHex(hash: Hex): Point;
    private uncompressedHex;
    private compressedHex;
    toRawBytes(isCompressed?: boolean): Uint8Array;
    toHex(isCompressed?: boolean): string;
}
export declare class SignResult {
    r: bigint;
    s: bigint;
    constructor(r: bigint, s: bigint);
    static fromHex(hex: Hex): SignResult;
    toHex(): string;
}
export declare const BASE_POINT: Point;
export declare function getPublicKey(privateKey: Uint8Array, isCompressed?: boolean): Uint8Array;
export declare function getPublicKey(privateKey: string, isCompressed?: boolean): string;
export declare function getPublicKey(privateKey: bigint | number, isCompressed?: boolean): Point;
export declare function sign(hash: Uint8Array, privateKey: PrivKey, k?: bigint | number): Uint8Array;
export declare function sign(hash: string, privateKey: PrivKey, k?: bigint | number): string;
export declare function verify(signature: Signature, hash: Hex, publicKey: PubKey): boolean;
export {};