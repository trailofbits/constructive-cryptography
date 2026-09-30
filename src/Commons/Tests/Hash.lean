import Commons.Tests.Hex
import Commons.Schemes.Hash.SHA256
import Commons.Schemes.Hash.Keccak

/-!
# Known-answer tests for the hash functions

SHA-256 against FIPS 180-4 (the empty message, `"abc"`, the two-block 448-bit message), and
SHA-3, SHAKE and Keccak-256 against the reference implementations, on inputs around the Keccak
rate: 135, 136 and 200 bytes, and outputs longer than one rate block. The checks run the
functions by evaluation (`#guard`).
-/

namespace Commons.Tests.Hash

open Commons

/-- `n` copies of the byte `a`. -/
def a (n : Nat) : ByteArray := ⟨Array.replicate n 0x61⟩

/-- The two-block message of FIPS 180-4. -/
def twoBlock : ByteArray := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8

-- SHA-256
#guard toHex (SHA256.sha256 ByteArray.empty) =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard toHex (SHA256.sha256 "abc".toUTF8) =
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard toHex (SHA256.sha256 twoBlock) =
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard toHex (SHA256.sha256 (a 135)) =
  "dfa58dfd72f3c7080d0249a7758fd3636872f63fa24b18473ed36f031e248347"
#guard toHex (SHA256.sha256 (a 136)) =
  "6f0e44b9ce4ea61d52a3479c10f60ef916937f799f11964b7f1c7771063905c4"
#guard toHex (SHA256.sha256 (a 200)) =
  "c2a908d98f5df987ade41b5fce213067efbcc21ef2240212a41e54b5e7c28ae5"

-- SHA3-224
#guard toHex (Keccak.sha3_224 ByteArray.empty) =
  "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7"
#guard toHex (Keccak.sha3_224 "abc".toUTF8) =
  "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf"
#guard toHex (Keccak.sha3_224 twoBlock) =
  "8a24108b154ada21c9fd5574494479ba5c7e7ab76ef264ead0fcce33"
#guard toHex (Keccak.sha3_224 (a 135)) =
  "f9f28c21a2b0884bbd3594cae82bf811c0c1ede427e083d5576e909d"
#guard toHex (Keccak.sha3_224 (a 136)) =
  "96136a6a094433b4aa855f163829a2ce6bca7d56cfd2163b47f1f1c4"
#guard toHex (Keccak.sha3_224 (a 200)) =
  "455e0ccfc6010738ed93a793dffd79aff36debbd1a7eb6621bd6c722"

-- SHA3-256
#guard toHex (Keccak.sha3_256 ByteArray.empty) =
  "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
#guard toHex (Keccak.sha3_256 "abc".toUTF8) =
  "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
#guard toHex (Keccak.sha3_256 twoBlock) =
  "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
#guard toHex (Keccak.sha3_256 (a 135)) =
  "8094bb53c44cfb1e67b7c30447f9a1c33696d2463ecc1d9c92538913392843c9"
#guard toHex (Keccak.sha3_256 (a 136)) =
  "3fc5559f14db8e453a0a3091edbd2bc25e11528d81c66fa570a4efdcc2695ee1"
#guard toHex (Keccak.sha3_256 (a 200)) =
  "cce34485baf2bf2aca99b94833892a4f52896d3d153f7b840cc4f9fe695f1387"

-- SHA3-384
#guard toHex (Keccak.sha3_384 ByteArray.empty) =
  "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004"
#guard toHex (Keccak.sha3_384 "abc".toUTF8) =
  "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25"
#guard toHex (Keccak.sha3_384 twoBlock) =
  "991c665755eb3a4b6bbdfb75c78a492e8c56a22c5c4d7e429bfdbc32b9d4ad5aa04a1f076e62fea19eef51acd0657c22"
#guard toHex (Keccak.sha3_384 (a 135)) =
  "a2d51907c0611e25c058f0675042e8f53cc473dc347c5ea8a813d886b3aa8f8dcab61a236237d94de404cd66606243f9"
#guard toHex (Keccak.sha3_384 (a 136)) =
  "cbbcb466417a2f6d466479bb6dc659434d9589de3a53acc9b427580482e305948888c8fa6d069c5e6a899aa34a9af15a"
#guard toHex (Keccak.sha3_384 (a 200)) =
  "f97756776c1874724c94a8008f7f155553b4bf00fbf8fbeac246624ad59c258a3c0977d9f2543d7cbd75b9ac8fdc0d40"

-- SHA3-512
#guard toHex (Keccak.sha3_512 ByteArray.empty) =
  "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"
#guard toHex (Keccak.sha3_512 "abc".toUTF8) =
  "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
#guard toHex (Keccak.sha3_512 twoBlock) =
  "04a371e84ecfb5b8b77cb48610fca8182dd457ce6f326a0fd3d7ec2f1e91636dee691fbe0c985302ba1b0d8dc78c086346b533b49c030d99a27daf1139d6e75e"
#guard toHex (Keccak.sha3_512 (a 135)) =
  "4be1e70276f9122f470a54c27240c7d0709dab7469958b48a950d69da6dd07ca135826d9d23e975cb9283e7d236ef98a80451dca8e311f52096308b2c8d70cc7"
#guard toHex (Keccak.sha3_512 (a 136)) =
  "e50392c91ed95768c8dcf52a12e5db1ecd0347fb995f7ff4ea06994649bbd1a0de7ae36a62aadc00a704d730b52bda191b72951e2afc9b6fb6824787b2086257"
#guard toHex (Keccak.sha3_512 (a 200)) =
  "eae6c85c6904f11075de9f9d5e1064371d000510fa3d2d79d40cf9be34892fb01859d0a0234e138bcb0ad5c84f6c0dca226a414b0c9a2897cb695f5185fe36ec"

-- SHAKE128 and SHAKE256, including outputs past one and two rate blocks
#guard toHex (Keccak.shake128 ByteArray.empty 32) =
  "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"
#guard toHex (Keccak.shake256 ByteArray.empty 64) =
  "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be"
#guard toHex (Keccak.shake128 "abc".toUTF8 32) =
  "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
#guard toHex (Keccak.shake256 "abc".toUTF8 64) =
  "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4"
#guard toHex (Keccak.shake128 twoBlock 32) =
  "1a96182b50fb8c7e74e0a707788f55e98209b8d91fade8f32f8dd5cff7bf21f5"
#guard toHex (Keccak.shake256 twoBlock 64) =
  "4d8c2dd2435a0128eefbb8c36f6f87133a7911e18d979ee1ae6be5d4fd2e332940d8688a4e6a59aa8060f1f9bc996c05aca3c696a8b66279dc672c740bb224ec"
#guard toHex (Keccak.shake128 (a 135) 32) =
  "a5e2b2278d1b75866c7877a0ffa24737e91def84e20944b23f1854012e29148a"
#guard toHex (Keccak.shake256 (a 135) 64) =
  "55b991ece1e567b6e7c2c714444dd201cd51f4f3832d08e1d26bebc63e07a3d7ddeed4a5aa6df7a15f89f2050566f75d9cf1a4dea4ed1f578df0985d5706d49e"
#guard toHex (Keccak.shake128 (a 136) 32) =
  "0d0158d446783a9b18a6908c08bb5de6f9aab1be71b56b11a4b1c9cbb4d0f422"
#guard toHex (Keccak.shake256 (a 136) 64) =
  "8fcc5a08f0a1f6827c9cf64ee8d16e0443106359ca6c8efd230759256f44996a703c7fa566b8308f7050f4c717418c5ef75f512d1ba01f4f1ff5984e1bc89efd"
#guard toHex (Keccak.shake128 (a 200) 32) =
  "70ac9b97e891be583e08929ce4cce50d346b05f9597356d6af94d4643d2af3b6"
#guard toHex (Keccak.shake256 (a 200) 64) =
  "e49647491c9d12d125a2f75826c96f6307d2fabebcbb9fb1616d76b09499380e8bcf60f72750879140e73fb7453a979b69d25efa8de613462f108ce7f2f1d7c5"
#guard toHex (Keccak.shake128 "abc".toUTF8 200) =
  "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc844c50af32acd3f2cdd066568706f509bc1bdde58295dae3f891a9a0fca5783789a41f8611214ce612394df286a62d1a2252aa94db9c538956c717dc2bed4f232a0294c857c730aa16067ac1062f1201fb0d377cfb9cde4c63599b27f3462bba4a0ed296c801f9ff7f57302bb3076ee145f97a32ae68e76ab66c48d51675bd49acc29082f5647584e6aa01b3f5af057805f973ff8ecb8b226ac32ada6f01c1fcd4818cb006aa5b4cd"
#guard toHex (Keccak.shake256 "abc".toUTF8 300) =
  "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e41385141204f329979fd3047a13c5657724ada64d2470157b3cdc288620944d78dbcddbd912993f0913f164fb2ce95131a2d09a3e6d51cbfc622720d7a75c6334e8a2d7ec71a7cc29cf0ea610eeff1a588290a53000faa79932becec0bd3cd0b33a7e5d397fed1ada9442b99903f4dcfd8559ed3950faf40fe6f3b5d710ed3b677513771af6bfe11934817e8762d9896ba579d88d84ba7aa3cdc7055f6796f195bd9ae788f2f5bb96100d6bbaff7fbc6eea24d4449a2477d172a5507dcc931412fc346b1bb39b878330e026b12ddf384af3334560ea1d363966caa7d8ddcbec7da52b42215c11d5f8ee57f341"

-- Keccak-256
#guard toHex (Keccak.keccak256 ByteArray.empty) =
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard toHex (Keccak.keccak256 "abc".toUTF8) =
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
#guard toHex (Keccak.keccak256 twoBlock) =
  "45d3b367a6904e6e8d502ee04999a7c27647f91fa845d456525fd352ae3d7371"
#guard toHex (Keccak.keccak256 (a 135)) =
  "34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446"
#guard toHex (Keccak.keccak256 (a 136)) =
  "a6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e"
#guard toHex (Keccak.keccak256 (a 200)) =
  "96ea54061def936c4be90b518992fdc6f12f535068a256229aca54267b4d084d"

end Commons.Tests.Hash
