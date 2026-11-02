module

public import ConstructiveCryptography.DSL

/-!
# Nonce-based stream-cipher interface

`StreamCipher N M` exposes `crypt(n, m)` on a nonce in `N` and a message or ciphertext in `M`.
The same operation serves encryption and decryption; its functional correctness contract is
`crypt(n, crypt(n, m)) = m`. This specializes the nonce-based correctness equation of
[1, §5.5, p. 202], “D(k, E(k, m, N), N) = m”, to a cipher whose two operations coincide.
The interface permits every input history within its query budget. A caller imposing fresh
nonces on encryption uses `nonceRestricted` at its outer encryption interface.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `N` carries caller-supplied nonces; `M` carries both plaintexts and ciphertexts.
-- Each `crypt(n, m)` call returns one value in `M` and consumes one query.
interface StreamCipher(N M : Type) [Fintype N] [Fintype M]
  crypt(nonce : N, message : M) → M

end

end Commons
