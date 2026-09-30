import Commons.Tests.Hex
import Commons.Schemes.BlockCipher.AES

/-!
# Known-answer tests for AES

AES-128, AES-192 and AES-256 against FIPS 197: the last word of each key expansion (Appendix A),
the cipher example (Appendix B), and the cipher and inverse cipher examples (Appendix C); and
against the ECB vectors of NIST SP 800-38A (F.1.1–F.1.6), four blocks per key length, encrypted
and decrypted. The checks run the functions by evaluation (`#guard`).
-/

namespace Commons.Tests.AES

open Commons Commons.AES

/-- A block from hexadecimal. -/
def block (s : String) : Block := hexBytes 16 s

/-- The SP 800-38A plaintext blocks. -/
def plaintexts : List Block :=
  ["6bc1bee22e409f96e93d7e117393172a", "ae2d8a571e03ac9c9eb76fac45af8e51",
    "30c81c46a35ce411e5fbc1191a0a52ef", "f69f2445df4f9b17ad2b417be66c3710"].map block

/-- Every plaintext encrypts to its ciphertext, and every ciphertext decrypts to its
plaintext. -/
def ecb (k : KeyLength) (key : Key k) (ciphertexts : List String) : Bool :=
  (plaintexts.zip (ciphertexts.map block)).all fun (p, c) =>
    cipher k key p == c && invCipher k key c == p

-- FIPS 197, Appendix A: the last word of the key expansion.
#guard (keyExpansion .aes128 (hexBytes _ "2b7e151628aed2a6abf7158809cf4f3c")).back? ==
  some (hexBytes 4 "b6630ca6")
#guard (keyExpansion .aes192
    (hexBytes _ "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b")).back? ==
  some (hexBytes 4 "01002202")
#guard (keyExpansion .aes256
    (hexBytes _ "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4")).back? ==
  some (hexBytes 4 "706c631e")

-- FIPS 197, Appendix B.
#guard cipher .aes128 (hexBytes _ "2b7e151628aed2a6abf7158809cf4f3c")
    (block "3243f6a8885a308d313198a2e0370734") == block "3925841d02dc09fbdc118597196a0b32"

-- FIPS 197, Appendix C: the cipher and the inverse cipher.
#guard
  let key : Key .aes128 := hexBytes _ "000102030405060708090a0b0c0d0e0f"
  let c := block "69c4e0d86a7b0430d8cdb78070b4c55a"
  cipher .aes128 key (block "00112233445566778899aabbccddeeff") == c &&
    invCipher .aes128 key c == block "00112233445566778899aabbccddeeff"
#guard
  let key : Key .aes192 := hexBytes _ "000102030405060708090a0b0c0d0e0f1011121314151617"
  let c := block "dda97ca4864cdfe06eaf70a0ec0d7191"
  cipher .aes192 key (block "00112233445566778899aabbccddeeff") == c &&
    invCipher .aes192 key c == block "00112233445566778899aabbccddeeff"
#guard
  let key : Key .aes256 :=
    hexBytes _ "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  let c := block "8ea2b7ca516745bfeafc49904b496089"
  cipher .aes256 key (block "00112233445566778899aabbccddeeff") == c &&
    invCipher .aes256 key c == block "00112233445566778899aabbccddeeff"

-- NIST SP 800-38A, F.1.1–F.1.6: ECB encryption and decryption.
#guard ecb .aes128 (hexBytes _ "2b7e151628aed2a6abf7158809cf4f3c")
  ["3ad77bb40d7a3660a89ecaf32466ef97", "f5d3d58503b9699de785895a96fdbaaf",
    "43b1cd7f598ece23881b00e3ed030688", "7b0c785e27e8ad3f8223207104725dd4"]
#guard ecb .aes192 (hexBytes _ "8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b")
  ["bd334f1d6e45f25ff712a214571fa5cc", "974104846d0ad3ad7734ecb3ecee4eef",
    "ef7afd2270e2e60adce0ba2face6444e", "9a4b41ba738d6c72fb16691603c18e0e"]
#guard ecb .aes256
  (hexBytes _ "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4")
  ["f3eed1bdb5d2a03c064b5a7e3db181f8", "591ccb10d410ed26dc5ba74a31362870",
    "b6ed21b99ca6f4f9f153e7b1beafed1d", "23304b7a39f9f3ff067d8d8f9e24ecc7"]

end Commons.Tests.AES
