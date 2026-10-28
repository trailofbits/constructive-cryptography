import RandomSystems.Typed.QueryRouting

/-!
# Input-dependent routing regression

The first Boolean of an outside payload selects the inside port; the second Boolean becomes
the inside query. A label-only renaming cannot express this value-dependent choice.
The identity oracle checks the payload; a port-returning oracle checks the selected label.
A final example uses different reply alphabets and a translation that also needs the retained
outside input.
-/

namespace SystemAlgebra.Tests.QueryRouting

/-- Outside interface: one port `⋆`, queries `(b,x) ∈ Bool²`, and Boolean replies.
Its domain is `F = {[(⋆,(b,x))] | b,x ∈ Bool}`: one query. -/
def outside : Interface := Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Bool) 1

/-- Inside interface: ports `j ∈ Bool` with Boolean queries and replies.
Its domain is `E = {[(j,x)] | j,x ∈ Bool}`: one query at either port. -/
def inside : Interface := Interface.queryBudget Bool (fun _ => Bool) (fun _ => Bool) 1

/-- `request(⋆,(b,x)) = (b,x)`: the selector `b` becomes the inside port label. -/
def request (u : Σ o, outside.X o) : Σ j, inside.X j := ⟨u.2.1, u.2.2⟩

/-- `answer(u,(j,y)) = y`: forward the inside Boolean to the original outside port. -/
def answer (u : Σ o, outside.X o) (r : Σ j, inside.Y j) : outside.Y u.1 := r.2

/-- The value-dependent request preserves the exact one-query domain. -/
lemma request_domain (us : List (Σ o, outside.X o)) (hu : outside.domain us) :
    inside.domain (us.map request) := by
  -- Mapping preserves both nonemptiness and the one-query bound.
  exact ⟨fun he => hu.1 (List.map_eq_nil_iff.mp he),
    (List.length_map request).trans_le hu.2⟩

/-- The direct router has its exact domain certificate, including the payload-to-port map. -/
lemma certified : IsDDCFrom inside.domain outside.domain 1
    (routingConverter request answer outside.domain) :=
  routingConverter_isDDCFrom request answer outside.nonempty_prefix request_domain

/-- A routed identity oracle returns the query's Boolean at the original outside port. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (_ : Bool) (x : Bool) => x) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.2) := by
  -- Substituting f_j(x) = x in the routing equation gives g(b,x) = x.
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (_ : Bool) (x : Bool) => x)

/-- With `f_j(x) = j`, routing returns `g(b,x) = b`. A constant port choice fails this law. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (j : Bool) (_ : Bool) => j) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.1) := by
  -- The returned inside label exposes the selector used by request.
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (j : Bool) (_ : Bool) => j)

/-- Inside ports and queries are Boolean, with `Y_false = Unit` and `Y_true = Bool`.
The domain remains `E = {[(j,x)] | j,x ∈ Bool}`, so the same request map is admissible. -/
def heterogeneousInside : Interface :=
  -- Each port uses the usual finite enumeration of its reply alphabet.
  letI (j : Bool) : Fintype (if j then Bool else Unit) := by
    cases j
    · exact inferInstanceAs (Fintype Unit)
    · exact inferInstanceAs (Fintype Bool)
  Interface.queryBudget Bool (fun _ => Bool) (fun j => if j then Bool else Unit) 1

/-- Reply law `f_false(x) = ⋆`, `f_true(x) = x`: only the true port returns a Boolean. -/
def heterogeneousOracle : ∀ j, heterogeneousInside.X j → heterogeneousInside.Y j
  | false, _ => ()
  | true, x => x

/-- `answer((⋆,(b,x)),(false,⋆)) = x` and `answer((⋆,(b,x)),(true,y)) = !y`.
The Unit reply carries no data, so the false branch uses the retained outside payload. -/
def heterogeneousAnswer (u : Σ o, outside.X o)
    (r : Σ j, heterogeneousInside.Y j) : outside.Y u.1 :=
  match r with
  | ⟨false, _⟩ => u.2.2
  | ⟨true, y⟩ => !y

/-- Changing only reply alphabets leaves `F(us) → E(map request us)` unchanged. -/
lemma heterogeneous_certified : IsDDCFrom heterogeneousInside.domain outside.domain 1
    (routingConverter request heterogeneousAnswer outside.domain) :=
  routingConverter_isDDCFrom request heterogeneousAnswer outside.nonempty_prefix request_domain

/-- The translated outside law is `g(false,x) = x`, `g(true,x) = !x`.
It observes both the selected port and the translation of its differently typed reply. -/
example : TypedConverter.ofDDC (A := outside) (B := heterogeneousInside)
    (routingConverter request heterogeneousAnswer outside.domain) heterogeneous_certified •
    TypedSystem.ofFunction (A := heterogeneousInside) heterogeneousOracle =
    TypedSystem.ofFunction (A := outside)
      (fun (_ : Unit) (u : Bool × Bool) => if u.1 then !u.2 else u.2) := by
  -- First expose the query, fixed-function reply and answer translation.
  refine (TypedConverter.ofDDC_routingConverter_smul_ofFunction
    (A := outside) (B := heterogeneousInside)
    request heterogeneousAnswer heterogeneous_certified heterogeneousOracle).trans ?_
  congr 1
  funext o u
  -- The selected port determines the reply alphabet and the corresponding translation.
  obtain ⟨b, x⟩ := u
  cases b <;> rfl

end SystemAlgebra.Tests.QueryRouting
