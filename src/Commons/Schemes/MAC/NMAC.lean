import Commons.Definitions.Ideal

/-!
# The cascade and NMAC

Gaži, Pietrzak and Rybár, *The Exact PRF-Security of NMAC and HMAC*, §2.2 (printed pp. 120–121),
from `nmac-cc` (`NMAC/Objects.lean`). For a keyed function `f : C → B → C`, a compression function
with keys and chaining values in `C` and blocks in `B`, the cascade chains `f` through the blocks
of a message from the key, `Cascᶠ(K, λ) = K`; NMAC applies `f` under an independent second key to
the padded cascade, `NMACᶠ((K₁, K₂), M) = f(K₂, Cascᶠ(K₁, M) ∥ 0^{b−c})`. The embedding
`pad : C ↪ B` generalizes the zero padding, and a message is encoded as its blocks by
`blockForm : M → List B`. Under two uniform keys, NMAC is a system on the interface of a function,
whose security as a PRF is its substitution for `URF`.

## Main definitions

* `NMAC.cascade f K blocks`: the cascade
* `NMAC.nmac f pad (K₁, K₂) blocks`: NMAC
* `NMAC.Real f pad blockForm`: NMAC of the encoded messages under two uniform keys
-/

namespace Commons

open SystemAlgebra Probability

namespace NMAC

variable {B C M : Type}

/-- **The cascade** (§2.2): `f` chained through the blocks from the key, `Cascᶠ(K, λ) = K`. -/
def cascade (f : C → B → C) (key : C) (blocks : List B) : C :=
  blocks.foldl f key

/-- **NMAC** (§2.2): `f` under the second key on the padded cascade under the first. -/
def nmac (f : C → B → C) (pad : C ↪ B) (keys : C × C) (blocks : List B) : C :=
  f keys.2 (pad (cascade f keys.1 blocks))

noncomputable section

variable [Fintype C] [Nonempty C] [Fintype M] {q : ℕ}

/-- **NMAC under two uniform keys**: for independent uniform `K₁` and `K₂`, each message is
answered with NMAC of its blocks. -/
def Real (f : C → B → C) (pad : C ↪ B) (blockForm : M → List B) :
    Interface.Resource (Evaluation M C q) :=
  Interface.Resource.sample (Distribution.uniform (C × C)) fun keys =>
    Interface.Resource.ofFunction fun _ message => nmac f pad keys (blockForm message)

end

end NMAC

end Commons
