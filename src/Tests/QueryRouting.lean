import RandomSystems.Typed.QueryRouting

/-!
# Input-dependent routing regression

Routing on one outside port `⋆` with queries `(b,x) ∈ Bool²` to two inside ports `j ∈ Bool`.
The value `b` selects the inside port and `x` becomes the inside query, a value-dependent choice
that no renaming of labels expresses.

```text
                ┌──────────────────────┐
  ⋆((b,x))  ──► │ (j,x) = (b,x)        │ ──► b(x)
  ⋆ ⇒ y'    ◄── │ y' = answer u (b,y)  │ ◄── b ⇒ y
                └──────────────────────┘
```

* The identity oracle `f_j(x) = x` checks that the payload `x` is forwarded.
* The port-returning oracle `f_j(x) = j` checks that the selected label is `b`.
* Reply alphabets `Y_false = Unit`, `Y_true = Bool` check heterogeneous replies, with an answer
  map that uses the retained outside input on the `Unit` port.
* The unrestricted domains `F = E = True`, which contain `[]`, check the domain theorem under
  nonempty-prefix closure alone.
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

/-- The map-domain condition `F us → E (us.map request)`: the value-dependent request sends the
one-query outside domain into the one-query inside domain. -/
lemma request_domain (us : List (Σ o, outside.X o)) (hu : outside.domain us) :
    inside.domain (us.map request) := by
  -- Mapping preserves both nonemptiness and the one-query bound.
  exact ⟨fun he => hu.1 (List.map_eq_nil_iff.mp he),
    (List.length_map request).trans_le hu.2⟩

/-- The router is a DDC from `E` to `F` with one inside query per invocation. -/
lemma certified : IsDDCFrom inside.domain outside.domain 1
    (routingConverter request answer outside.domain) :=
  routingConverter_isDDCFrom request answer outside.nonempty_prefix.2 request_domain

/-- With `f_j(x) = x`, routing returns `g(b,x) = x` at the outside port `⋆`. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (_ : Bool) (x : Bool) => x) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.2) := by
  -- Substituting f_j(x) = x in the routing equation gives g(b,x) = x.
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (_ : Bool) (x : Bool) => x)

/-- With `f_j(x) = j`, routing returns `g(b,x) = b`. A router querying a constant port `j₀`
would return `j₀` and fail this law. -/
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

/-- `f_false(x) = ()` and `f_true(x) = x`: only port `true` returns a Boolean. -/
def heterogeneousOracle : ∀ j, heterogeneousInside.X j → heterogeneousInside.Y j
  | false, _ => ()
  | true, x => x

/-- `answer((⋆,(b,x)),(false,())) = x` and `answer((⋆,(b,x)),(true,y)) = !y`.
The `Unit` reply carries no data, so on port `false` the answer reads the retained input. -/
def heterogeneousAnswer (u : Σ o, outside.X o)
    (r : Σ j, heterogeneousInside.Y j) : outside.Y u.1 :=
  match r with
  | ⟨false, _⟩ => u.2.2
  | ⟨true, y⟩ => !y

/-- The domains do not involve reply alphabets, so `request_domain` certifies this router too. -/
lemma heterogeneous_certified : IsDDCFrom heterogeneousInside.domain outside.domain 1
    (routingConverter request heterogeneousAnswer outside.domain) :=
  routingConverter_isDDCFrom request heterogeneousAnswer outside.nonempty_prefix.2 request_domain

/-- The outside function is `g(false,x) = x` and `g(true,x) = !x`. It depends on the selected
port, on the reply of its alphabet, and on the retained input. -/
example : TypedConverter.ofDDC (A := outside) (B := heterogeneousInside)
    (routingConverter request heterogeneousAnswer outside.domain) heterogeneous_certified •
    TypedSystem.ofFunction (A := heterogeneousInside) heterogeneousOracle =
    TypedSystem.ofFunction (A := outside)
      (fun (_ : Unit) (u : Bool × Bool) => if u.1 then !u.2 else u.2) := by
  -- The routing law gives `g(b,x) = heterogeneousAnswer (⋆,(b,x)) (b, f_b(x))`.
  refine (TypedConverter.ofDDC_routingConverter_smul_ofFunction
    (A := outside) (B := heterogeneousInside)
    request heterogeneousAnswer heterogeneous_certified heterogeneousOracle).trans ?_
  congr 1
  funext o u
  -- Case on the selected port `b`; each case is the corresponding equation.
  obtain ⟨b, x⟩ := u
  cases b <;> rfl

/-- With `F = E = True`, which contains `[]`, the router is a DDC from `E` to `F`: the domain
theorem needs only closure of `F` under nonempty prefixes. -/
example : IsDDCFrom (fun _ => True) (fun _ => True) 1
    (routingConverter request answer (fun _ => True)) := by
  apply routingConverter_isDDCFrom request answer
  -- `F = True` is closed under nonempty prefixes.
  · intro p h _ _ _
    trivial
  -- `E = True` holds at every request image `us.map request`.
  · intro us _
    trivial

end SystemAlgebra.Tests.QueryRouting
