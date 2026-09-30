import Commons.Tests.Hex
import Commons.Schemes.BlockCipher.AES
import Commons.Schemes.MAC.PMAC

/-!
# Known-answer tests for PMAC

PMAC under AES-128 and AES-256 against the published vectors (`pmac128.txt` and `pmac256.txt` of
https://www.cs.ucdavis.edu/~rogaway/ocb/): the messages `00 01 02 …` of 0, 3, 16, 20, 32 and 34
bytes, covering the empty message and partial and full last blocks, and 1000 zero bytes. The
checks run the functions by evaluation (`#guard`).
-/

namespace Commons.Tests.PMAC

open Commons Commons.AES Commons.PMAC

/-- The tags of the messages `00 01 02 …` of 0, 3, 16, 20, 32 and 34 bytes and of 1000 zero
bytes. -/
def check (E : Bytes 16 → Bytes 16) (tags : List String) : Bool :=
  let messages := [0, 3, 16, 20, 32, 34].map (fun n => (List.range n).map Nat.toUInt8) ++
    [List.replicate 1000 0]
  (messages.zip tags).all fun (message, tag) => pmac E message == hexBytes 16 tag

-- PMAC-AES-128.
#guard check (cipher .aes128 (hexBytes _ "000102030405060708090a0b0c0d0e0f"))
  ["4399572cd6ea5341b8d35876a7098af7", "256ba5193c1b991b4df0c51f388a9e27",
    "ebbd822fa458daf6dfdad7c27da76338", "0412ca150bbf79058d8c75a58c993f55",
    "e97ac04e9e5e3399ce5355cd7407bc75", "5cba7d5eb24f7c86ccc54604e53d5512",
    "c2c9fa1d9985f6f0d2aff915a0e8d910"]

-- PMAC-AES-256.
#guard check
  (cipher .aes256 (hexBytes _ "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"))
  ["e620f52fe75bbe87ab758c0624943d8b", "ffe124cc152cfb2bf1ef5409333c1c9a",
    "853fdbf3f91dcd36380d698a64770bab", "7711395fbe9dec19861aeb96e052cd1b",
    "08fa25c28678c84d383130653e77f4c0", "edd8a05f4b66761f9eee4feb4ed0c3a1",
    "69aa77f231eb0cdff960f5561d29a96e"]

end Commons.Tests.PMAC
