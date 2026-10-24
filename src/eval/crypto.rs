//! `std/crypto` for the reference: OpenSSL's libcrypto, as natively, loaded when first used so
//! that the compiler depends on no library. `FLY_LIBCRYPTO` names it if the loader cannot find it.

use std::ffi::{CStr, CString, c_char, c_int, c_uint, c_void};
use std::sync::OnceLock;

unsafe extern "C" {
    fn dlopen(path: *const c_char, mode: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, name: *const c_char) -> *mut c_void;
}

const RTLD_NOW: c_int = 2;

type P = *mut c_void;
type CP = *const c_void;
type U8 = *const u8;
type M8 = *mut u8;

/// libcrypto's functions, by name.
macro_rules! functions {
    ($($name:ident: fn($($arg:ty),*) -> $ret:ty;)*) => {
        #[allow(non_snake_case)]
        struct Lib { $($name: unsafe extern "C" fn($($arg),*) -> $ret,)* }
        fn load(h: P) -> Result<Lib, String> {
            Ok(Lib { $($name: unsafe {
                let s = dlsym(h, concat!(stringify!($name), "\0").as_ptr().cast());
                if s.is_null() { return Err(format!("this libcrypto has no {}: cryptography needs OpenSSL 3 or later", stringify!($name))); }
                std::mem::transmute::<*mut c_void, unsafe extern "C" fn($($arg),*) -> $ret>(s)
            },)* })
        }
    };
}

functions! {
    EVP_sha256: fn() -> CP;
    EVP_sha384: fn() -> CP;
    EVP_sha512: fn() -> CP;
    EVP_Digest: fn(CP, usize, M8, *mut c_uint, CP, P) -> c_int;
    EVP_Q_mac: fn(P, *const c_char, *const c_char, *const c_char, CP, CP, usize, U8, usize, M8, usize, *mut usize) -> M8;
    EVP_KDF_fetch: fn(P, *const c_char, *const c_char) -> P;
    EVP_KDF_free: fn(P) -> ();
    EVP_KDF_CTX_new: fn(P) -> P;
    EVP_KDF_CTX_free: fn(P) -> ();
    EVP_KDF_derive: fn(P, M8, usize, CP) -> c_int;
    EVP_aes_256_gcm: fn() -> CP;
    EVP_CIPHER_CTX_new: fn() -> P;
    EVP_CIPHER_CTX_free: fn(P) -> ();
    EVP_CIPHER_CTX_ctrl: fn(P, c_int, c_int, P) -> c_int;
    EVP_EncryptInit_ex: fn(P, CP, P, U8, U8) -> c_int;
    EVP_EncryptUpdate: fn(P, M8, *mut c_int, U8, c_int) -> c_int;
    EVP_EncryptFinal_ex: fn(P, M8, *mut c_int) -> c_int;
    EVP_DecryptInit_ex: fn(P, CP, P, U8, U8) -> c_int;
    EVP_DecryptUpdate: fn(P, M8, *mut c_int, U8, c_int) -> c_int;
    EVP_DecryptFinal_ex: fn(P, M8, *mut c_int) -> c_int;
    EVP_PKEY_new_raw_private_key: fn(c_int, P, U8, usize) -> P;
    EVP_PKEY_new_raw_public_key: fn(c_int, P, U8, usize) -> P;
    EVP_PKEY_get_raw_public_key: fn(CP, M8, *mut usize) -> c_int;
    EVP_PKEY_free: fn(P) -> ();
    EVP_MD_CTX_new: fn() -> P;
    EVP_MD_CTX_free: fn(P) -> ();
    EVP_DigestSignInit: fn(P, *mut P, CP, P, P) -> c_int;
    EVP_DigestSign: fn(P, M8, *mut usize, U8, usize) -> c_int;
    EVP_DigestVerifyInit: fn(P, *mut P, CP, P, P) -> c_int;
    EVP_DigestVerify: fn(P, U8, usize, U8, usize) -> c_int;
}

// Raw pointers are not `Send`; these are a library's functions, callable from any thread.
unsafe impl Send for Lib {}
unsafe impl Sync for Lib {}

fn lib() -> Result<&'static Lib, String> {
    static LIB: OnceLock<Result<Lib, String>> = OnceLock::new();
    LIB.get_or_init(|| {
        let mut names: Vec<String> = Vec::new();
        if let Ok(own) = std::env::var("FLY_LIBCRYPTO") {
            names.push(own);
        } else if cfg!(target_os = "macos") {
            // Never the system's unversioned libcrypto, which ends any program that loads it.
            for v in ["3", "4"] {
                names.push(format!("libcrypto.{v}.dylib"));
                names.push(format!("/opt/homebrew/opt/openssl@{v}/lib/libcrypto.{v}.dylib"));
                names.push(format!("/usr/local/opt/openssl@{v}/lib/libcrypto.{v}.dylib"));
            }
        } else {
            names = vec!["libcrypto.so.3".into(), "libcrypto.so.4".into()];
        }
        for n in &names {
            let c = CString::new(n.as_str()).map_err(|e| e.to_string())?;
            let h = unsafe { dlopen(c.as_ptr(), RTLD_NOW) };
            if !h.is_null() {
                return load(h);
            }
        }
        Err("cryptography needs OpenSSL 3 or later (libcrypto), which was not found: set FLY_LIBCRYPTO to it".into())
    })
    .as_ref()
    .map_err(|e| e.clone())
}

fn c(s: &CStr) -> *const c_char {
    s.as_ptr()
}

pub fn digest(bits: u32, data: &[u8]) -> Result<Vec<u8>, String> {
    let l = lib()?;
    let mut out = vec![0u8; 64];
    let mut n: c_uint = 0;
    unsafe {
        let md = match bits {
            256 => (l.EVP_sha256)(),
            384 => (l.EVP_sha384)(),
            _ => (l.EVP_sha512)(),
        };
        if (l.EVP_Digest)(data.as_ptr().cast(), data.len(), out.as_mut_ptr(), &mut n, md, std::ptr::null_mut()) == 0 {
            return Err("libcrypto failed to hash".into());
        }
    }
    out.truncate(n as usize);
    Ok(out)
}

pub fn hmac(bits: u32, key: &[u8], data: &[u8]) -> Result<Vec<u8>, String> {
    let l = lib()?;
    let mut out = vec![0u8; 64];
    let mut n = 0usize;
    let alg = if bits == 256 { c(c"SHA256") } else { c(c"SHA512") };
    let r = unsafe {
        (l.EVP_Q_mac)(std::ptr::null_mut(), c(c"HMAC"), std::ptr::null(), alg, std::ptr::null(), key.as_ptr().cast(), key.len(), data.as_ptr(), data.len(), out.as_mut_ptr(), out.len(), &mut n)
    };
    if r.is_null() {
        return Err("libcrypto failed to run HMAC".into());
    }
    out.truncate(n);
    Ok(out)
}

/// OpenSSL's parameter of an operation, as `OSSL_PARAM` lays it out.
#[repr(C)]
struct Param {
    key: *const c_char,
    kind: c_uint,
    data: *const c_void,
    size: usize,
    returned: usize,
}

pub fn hkdf(secret: &[u8], salt: &[u8], info: &[u8], length: usize) -> Result<Vec<u8>, String> {
    if length > 255 * 32 {
        return Err("HKDF-SHA-256 makes at most 8160 bytes".into());
    }
    let l = lib()?;
    let mut out = vec![0u8; length];
    if length == 0 {
        return Ok(out);
    }
    // OSSL_PARAM_UTF8_STRING 4, OSSL_PARAM_OCTET_STRING 5, OSSL_PARAM_UNMODIFIED.
    static ZERO: u8 = 0;
    let octets = |key: &CStr, b: &[u8]| Param { key: c(key), kind: 5, data: if b.is_empty() { (&raw const ZERO).cast() } else { b.as_ptr().cast() }, size: b.len(), returned: usize::MAX };
    let params = [
        Param { key: c(c"digest"), kind: 4, data: c"SHA256".as_ptr().cast(), size: 6, returned: usize::MAX },
        octets(c"key", secret),
        octets(c"salt", salt),
        octets(c"info", info),
        Param { key: std::ptr::null(), kind: 0, data: std::ptr::null(), size: 0, returned: 0 },
    ];
    unsafe {
        let kdf = (l.EVP_KDF_fetch)(std::ptr::null_mut(), c(c"HKDF"), std::ptr::null());
        let ctx = if kdf.is_null() { std::ptr::null_mut() } else { (l.EVP_KDF_CTX_new)(kdf) };
        let ok = !ctx.is_null() && (l.EVP_KDF_derive)(ctx, out.as_mut_ptr(), length, params.as_ptr().cast()) > 0;
        if !ctx.is_null() {
            (l.EVP_KDF_CTX_free)(ctx);
        }
        if !kdf.is_null() {
            (l.EVP_KDF_free)(kdf);
        }
        if !ok {
            return Err("libcrypto failed to run HKDF".into());
        }
    }
    Ok(out)
}

/// AES-256-GCM: what it sealed or opened, `None` if what it opened was forged.
pub fn gcm(seal: bool, key: &[u8], nonce: &[u8], text: &[u8], aad: &[u8]) -> Result<Option<Vec<u8>>, String> {
    if key.len() != 32 || nonce.len() != 12 {
        return Err("AES-256-GCM takes a 32-byte key and a 12-byte nonce".into());
    }
    if !seal && text.len() < 16 {
        return Ok(None);
    }
    let l = lib()?;
    let n = if seal { text.len() } else { text.len() - 16 };
    let mut out = vec![0u8; n + 16];
    let mut k: c_int = 0;
    unsafe {
        let ctx = (l.EVP_CIPHER_CTX_new)();
        let init = if seal { l.EVP_EncryptInit_ex } else { l.EVP_DecryptInit_ex };
        let update = if seal { l.EVP_EncryptUpdate } else { l.EVP_DecryptUpdate };
        let mut ok = init(ctx, (l.EVP_aes_256_gcm)(), std::ptr::null_mut(), key.as_ptr(), nonce.as_ptr()) > 0;
        if !aad.is_empty() {
            ok &= update(ctx, std::ptr::null_mut(), &mut k, aad.as_ptr(), aad.len() as c_int) > 0;
        }
        if n > 0 {
            ok &= update(ctx, out.as_mut_ptr(), &mut k, text.as_ptr(), n as c_int) > 0;
        }
        // EVP_CTRL_GCM_SET_TAG and EVP_CTRL_GCM_GET_TAG: the tag is checked before the end, made after.
        if !seal {
            ok &= (l.EVP_CIPHER_CTX_ctrl)(ctx, 0x11, 16, text[n..].as_ptr() as P) > 0;
        }
        let done = if seal { (l.EVP_EncryptFinal_ex)(ctx, out.as_mut_ptr().add(n), &mut k) } else { (l.EVP_DecryptFinal_ex)(ctx, out.as_mut_ptr().add(n), &mut k) };
        if seal {
            ok &= done > 0 && (l.EVP_CIPHER_CTX_ctrl)(ctx, 0x10, 16, out.as_mut_ptr().add(n).cast()) > 0;
        }
        (l.EVP_CIPHER_CTX_free)(ctx);
        if !seal && done <= 0 {
            return Ok(None);
        }
        if !ok {
            return Err("libcrypto failed to run AES-256-GCM".into());
        }
    }
    out.truncate(if seal { n + 16 } else { n });
    Ok(Some(out))
}

/// EVP_PKEY_ED25519, which is NID_ED25519.
const ED25519: c_int = 1087;

/// The public key of an Ed25519 secret key, or a signature by it of `message`.
pub fn ed25519(secret: &[u8], message: Option<&[u8]>) -> Result<Vec<u8>, String> {
    if secret.len() != 32 {
        return Err("an Ed25519 secret key is 32 bytes".into());
    }
    let l = lib()?;
    let mut out = vec![0u8; 64];
    let mut n = out.len();
    unsafe {
        let key = (l.EVP_PKEY_new_raw_private_key)(ED25519, std::ptr::null_mut(), secret.as_ptr(), 32);
        if key.is_null() {
            return Err("libcrypto failed to make an Ed25519 key".into());
        }
        let ok = match message {
            None => (l.EVP_PKEY_get_raw_public_key)(key, out.as_mut_ptr(), &mut n) > 0,
            Some(m) => {
                let ctx = (l.EVP_MD_CTX_new)();
                let ok = (l.EVP_DigestSignInit)(ctx, std::ptr::null_mut(), std::ptr::null(), std::ptr::null_mut(), key) > 0
                    && (l.EVP_DigestSign)(ctx, out.as_mut_ptr(), &mut n, m.as_ptr(), m.len()) > 0;
                (l.EVP_MD_CTX_free)(ctx);
                ok
            }
        };
        (l.EVP_PKEY_free)(key);
        if !ok {
            return Err("libcrypto failed to sign with Ed25519".into());
        }
    }
    out.truncate(n);
    Ok(out)
}

pub fn ed25519_verify(public: &[u8], message: &[u8], signature: &[u8]) -> Result<bool, String> {
    if public.len() != 32 || signature.len() != 64 {
        return Ok(false);
    }
    let l = lib()?;
    unsafe {
        let key = (l.EVP_PKEY_new_raw_public_key)(ED25519, std::ptr::null_mut(), public.as_ptr(), 32);
        if key.is_null() {
            return Ok(false);
        }
        let ctx = (l.EVP_MD_CTX_new)();
        let ok = (l.EVP_DigestVerifyInit)(ctx, std::ptr::null_mut(), std::ptr::null(), std::ptr::null_mut(), key) > 0
            && (l.EVP_DigestVerify)(ctx, signature.as_ptr(), 64, message.as_ptr(), message.len()) == 1;
        (l.EVP_MD_CTX_free)(ctx);
        (l.EVP_PKEY_free)(key);
        Ok(ok)
    }
}
