import Commons.Tests.Hex
import Commons.Schemes.BlockCipher.AES
import Commons.Schemes.Stream.CTR

/-!
# Known-answer tests for CTR mode

CTR under AES-128, AES-192 and AES-256 against NIST SP 800-38A (F.5.1–F.5.6), from the initial
counter block `f0f1…feff`: four blocks encrypted and decrypted, a truncated last block, and the
counter wrapping in its last 32 bits. The checks run the functions by evaluation (`#guard`).
-/

namespace Commons.Tests.CTR

open Commons Commons.AES Commons.CTR

/-- The bytes of a hexadecimal string. -/
def bytes (s : String) : List UInt8 := (parseHex s).toList

/-- The initial counter block of SP 800-38A. -/
def initial : Bytes 16 := hexBytes 16 "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"

/-- The SP 800-38A plaintext. -/
def plaintext : List UInt8 :=
  bytes ("6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e51" ++
    "30c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710")

/-- The plaintext encrypts to the ciphertext, the ciphertext decrypts to the plaintext, and the
first 20 bytes encrypt to the first 20 bytes. -/
def check (k : KeyLength) (key : Key k) (ciphertext : String) : Bool :=
  let E := cipher k key
  crypt E initial plaintext == bytes ciphertext &&
    crypt E initial (bytes ciphertext) == plaintext &&
    crypt E initial (plaintext.take 20) == (bytes ciphertext).take 20

-- NIST SP 800-38A, F.5.1–F.5.2: CTR-AES128.
#guard check .aes128 (hexBytes _ "2b7e151628aed2a6abf7158809cf4f3c")
  ("874d6191b620e3261bef6864990db6ce9806f66b7970fdff8617187bb9fffdff" ++
    "5ae4df3edbd5d35e5b4f09020db03eab1e031dda2fbe03d1792170a0f3009cee")

-- NIST SP 800-38A, F.5.3–F.5.4: CTR-AES192.
#guard check .aes192 (hexBytes _ "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b")
  ("1abc932417521ca24f2b0459fe7e6e0b090339ec0aa6faefd5ccc2c6f4ce8e94" ++
    "1e36b26bd1ebc670d1bd1d665620abf74f78a7f6d29809585a97daec58c6b050")

-- NIST SP 800-38A, F.5.5–F.5.6: CTR-AES256.
#guard check .aes256
  (hexBytes _ "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4")
  ("601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c5" ++
    "2b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6")

-- The counter wraps in its last 32 bits and keeps the first 96.
#guard inc32 (hexBytes 16 "000102030405060708090a0bffffffff") ==
  hexBytes 16 "000102030405060708090a0b00000000"
#guard inc32 (initialBlock (hexBytes 12 "000102030405060708090a0b")) ==
  hexBytes 16 "000102030405060708090a0b00000001"

end Commons.Tests.CTR
