module

public import Commons.Constructions.KEMDEM.Correctness
public import ConstructiveCryptography.Notation
public import RandomSystems.Typed.QueryRouting

/-!
# Applying explicit component contracts

`cc_construct` exposes an equality or distance bound in a common context, and the component
fact stays a premise. `KEMDEM.correct` leaves key support; `routingConverter_isDDCFrom` leaves
complete-history admission. Goal guards check these remaining obligations and that
`cc_normalize` keeps one shared draw distinct from two independent draws.
-/

@[expose] public section

open SystemAlgebra Commons Probability.Distribution
open scoped SystemAlgebra NNReal

namespace Tests.ContractApplication

section Context

-- `A`, `B` are the outside and inside interfaces of `context`; `R`, `S` are systems on `B`.
variable {A B : Interface} (context : TypedConverter A B) (R S : TypedSystem B)

/-- A supplied component equality proves the construction through its fixed outer converter. -/
example
    -- `component : R = S` is the local semantic input.
    (component : R = S) : {R} —[context]→ {context • S} := by
  cc_construct
  guard_target =ₛ ConstructiveCryptography.ResourceTheory.attach context R = context • S
  cc_normalize
  guard_target =ₛ context • R = context • S
  rw [component]

/-- Non-expansion transports the supplied bound through the domain-preserving context. -/
example
    -- `error` is a scalar budget; `component` bounds only the differing systems on `B`.
    (error : ℝ≥0) (component : Δ R S ≤ error) :
    {R} —[context; error]→ {context • S} := by
  cc_construct
  guard_target =ₛ Δ (ConstructiveCryptography.ResourceTheory.attach context R) (context • S) ≤
    (error : ENNReal)
  cc_normalize
  guard_target =ₛ Δ (context • R) (context • S) ≤ (error : ENNReal)
  fail_if_success solve | cc_nonexpand
  calc
    Δ (context • R) (context • S) ≤ Δ R S := by cc_nonexpand
    _ ≤ error := component

end Context

/-- Correctness of both primitives leaves the encapsulated-key support obligation. -/
example
    -- `PK`, `SK` are asymmetric keys; `K` is the DEM key; `CK`, `CD` are ciphertext parts.
    -- `M` carries messages; `kem` and `dem` supply the two primitive algorithms.
    {PK SK K CK CD M : Type} (kem : KEM PK SK CK K) (dem : SymmetricEncryption K M CD)
    -- `hkem`, `hdem` are the two primitive correctness contracts.
    (hkem : kem.Correct) (hdem : dem.Correct)
    -- `compatible` places each supported encapsulated key within the DEM correctness contract.
    (compatible : ∀ pk sk, (pk, sk) ∈ kem.gen.1.support →
      ∀ ck k, (ck, k) ∈ (kem.encaps pk).1.support → k ∈ dem.gen.1.support) :
    (KEMDEM.scheme kem dem).Correct := by
  apply KEMDEM.correct kem dem hkem hdem
  guard_target = ∀ pk sk, (pk, sk) ∈ kem.gen.1.support →
    ∀ ck k, (ck, k) ∈ (kem.encaps pk).1.support → k ∈ dem.gen.1.support
  exact compatible

/-- The router maps `A.domain` to `B.domain` with one inside query per outside query;
complete-history admission remains a premise. -/
example
    -- `A`, `B` carry outside and inside alphabets and domains.
    {A B : Interface}
    -- `request` translates tagged inputs; `answer` returns an inside reply at its outside port.
    (request : (Σ i, A.X i) → Σ j, B.X j)
    (answer : (u : Σ i, A.X i) → (Σ j, B.Y j) → A.Y u.1)
    -- `admitted` admits the whole translated history, including any pending inside query.
    (admitted : ∀ xs, A.domain xs → B.domain (xs.map request)) :
    IsDDCFrom B.domain A.domain 1 (routingConverter request answer A.domain) := by
  -- The outside domain is closed under nonempty prefixes by the interface contract.
  apply routingConverter_isDDCFrom request answer A.nonempty_prefix.2
  guard_target = ∀ xs, A.domain xs → B.domain (xs.map request)
  exact admitted

/-- `cc_normalize` does not identify one shared draw with two independent draws. -/
example
    -- `P` samples `k : K`; `R k`, `S k` are systems on interfaces `A`, `B` at that parameter.
    {A B : Interface} {K : Type} (P : ProbDist K)
    (R : K → TypedSystem A) (S : K → TypedSystem B)
    -- `factorizes` is an explicit additional property of these particular systems and law.
    (factorizes : (sample k ←$ P; R k ∥ S k) =
      (sample k ←$ P; R k) ∥ (sample k ←$ P; S k)) :
    (sample k ←$ P; R k ∥ S k) =
      (sample k ←$ P; R k) ∥ (sample k ←$ P; S k) := by
  cc_normalize
  guard_target = TypedSystem.sample P.1 (fun k => TypedSystem.parallel (R k) (S k)) =
    TypedSystem.parallel (TypedSystem.sample P.1 R) (TypedSystem.sample P.1 S)
  exact factorizes

end Tests.ContractApplication
