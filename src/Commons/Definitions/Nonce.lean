module

public import RandomSystems.Typed.Filter

/-!
# Nonce-unique input domains

`nonceUnique nonce h` requires the selected nonces in input history `h` to be distinct.
The selector returns `some n` for encryption with nonce `n` and `none` for other queries.
`nonceRestricted A nonce` has domain `A.domain h ∧ nonceUnique nonce h`;
`nonceUnique_prefix` supplies prefix closure. `TypedConverter.filter A (nonceUnique nonce)
(nonceUnique_prefix nonce)` restricts a system on `A` to this interface.

`nonceUnique_snoc_some` leaves exactly the new nonce's freshness obligation;
`nonceUnique_snoc_none` permits queries, such as decryption, which consume no fresh nonce.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra

-- `X` carries inputs; `N` carries their selected nonces.
variable {X N : Type}

/-- The selected encryption nonces have no repeats: `(h.filterMap nonce).Nodup`.
[1, Attack Game 5.3, p. 202] requires that the encryption nonces “are unique”.
Decryption selects `none`: [1, §5.5, p. 202] says a message “should be decrypted with the
same nonce”. -/
def nonceUnique
    -- `nonce x = some n` consumes nonce `n`; `none` leaves the used-nonce list unchanged.
    (nonce : X → Option N)
    -- `h` lists the queries made so far.
    (h : List X) : Prop :=
  (h.filterMap nonce).Nodup

/-- Every prefix of a nonce-unique input history is nonce-unique. -/
lemma nonceUnique_prefix
    -- `nonce` selects encryption nonces; `hp` makes `p` a prefix of history `h`.
    (nonce : X → Option N) (p h : List X) (hp : p <+: h)
    -- `hh` states that the full history `h` has no repeated selected nonce.
    (hh : nonceUnique nonce h) : nonceUnique nonce p :=
  hh.sublist (hp.sublist.filterMap nonce)

/-- A query with no selected nonce preserves exactly the uniqueness condition. -/
lemma nonceUnique_snoc_none
    -- `h` is the past input history; the next input `x` consumes no nonce by `hx`.
    (nonce : X → Option N) (h : List X) (x : X) (hx : nonce x = none) :
    nonceUnique nonce (h ++ [x]) ↔ nonceUnique nonce h := by
  simp only [nonceUnique, List.filterMap_append, List.filterMap_cons, hx,
    List.filterMap_nil, List.append_nil]

/-- An encryption with nonce `n` preserves uniqueness exactly when `n` is fresh in `h`. -/
lemma nonceUnique_snoc_some
    -- `h` is the past input history; `hx` selects nonce `n` for the next input `x`.
    (nonce : X → Option N) (h : List X) (x : X) (n : N) (hx : nonce x = some n) :
    nonceUnique nonce (h ++ [x]) ↔ nonceUnique nonce h ∧ n ∉ h.filterMap nonce := by
  simp only [nonceUnique, List.filterMap_append, List.filterMap_cons, hx,
    List.filterMap_nil]
  rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons, and_comm]

/-- Restrict `A` to histories with distinct selected encryption nonces, retaining `A.domain`. -/
abbrev nonceRestricted
    -- `A` supplies ports, alphabets and the existing input domain.
    (A : Interface)
    -- `nonce` selects encryption nonces; decryption and other queries may return `none`.
    (nonce : (Σ i, A.X i) → Option N) : Interface :=
  A.restrict (nonceUnique nonce) (nonceUnique_prefix nonce)

end Commons
