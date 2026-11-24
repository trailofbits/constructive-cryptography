module

public import RandomSystems.Typed.DSL.Converters
public import RandomSystems.Typed.ParallelAll
public import ConstructiveCryptography.Notation

/-!
# Tests for named program converter certificates

Verifies the acceptance criteria of issue #398:
* A family of forwarding programs equals the converter of their joint forwarding program as an
  equation at the named certificates (`TypedConverter.ofProgram_isDDCFrom`,
  `TypedConverter.ofProgram_eq_ofDDC`, `TypedConverter.ofPreservingProgram_eq_ofDDC`).
* Rewriting `TypedConverter.ofProgram` into `TypedConverter.ofDDC` via `ofProgram_eq_ofDDC`
  directly applies `TypedConverter.ofDDC_ofProgramOn_smul_ofPDS`.
* `cc_normalize` composes cleanly with `ofProgram` under `⨂ₘ`, `∥`, `•`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.ProgramConverterCertificate

open CategoryTheory CategoryTheory.MonoidalCategory
open Probability SystemAlgebra
open scoped SystemAlgebra

/-- Forwarding program on an arbitrary interface `A`: forward every query `i(x)` and return its
reply unchanged. -/
noncomputable def forwardProgram (A : Interface) :
    Program Unit A.I A.I A.X A.Y A.X A.Y :=
  fun _ i x => DSL.callProg i x fun y => DSL.returnProg ((), y)

lemma forwardProgram_bounded (A : Interface) : (forwardProgram A).Bounded 1 :=
  fun _ i x => DSL.callBound_call i x _ fun y => DSL.callBound_return 0 ((), y)

lemma forwardProgram_portPreserving (A : Interface) :
    (forwardProgram A).PortPreserving (fun o => some o) := by
  intro _ i x
  apply DSL.preservesAt_call_self
  · intro y; exact DSL.avoids_return (fun o => some o) ((), y)
  · intro o' h; exact Option.some.inj h

/-- Every transcript of `DDC.ofProgram () (forwardProgram A)` is a transcript of `forwardAll`. -/
lemma replies_forwardProgram_le_forwardAll (A : Interface) :
    ∀ xs ys, Replies (DDC.ofProgram () (forwardProgram A)) xs ys →
      Replies (forwardAll A.I A.X A.Y) xs ys := by
  suffices key : ∀ t : List ((Σ l, twoFam A.X A.Y l) × (Σ l, twoFam A.Y A.X l)),
      Replies (DDC.ofProgram () (forwardProgram A)) (t.map Prod.fst) (t.map Prod.snd) →
        Replies (forwardAll A.I A.X A.Y) (t.map Prod.fst) (t.map Prod.snd) ∧
        ∃ m, (forwardProgram A).after () (t.map Prod.fst) = some m ∧
          match m with
          | .idle () => True
          | .busy i () x [] ⟨i', x'⟩ => i' = i ∧ HEq x' x
          | _ => False by
    intro xs ys hr
    have hlen := hr.length
    have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip hlen.ge
    have hy : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip hlen.le
    have h := (key (xs.zip ys) (by rwa [hx, hy])).1
    rwa [hx, hy] at h
  intro t hr
  induction t using List.reverseRecOn with
  | nil => exact ⟨replies_nil _, .idle (), rfl, trivial⟩
  | append_singleton t z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨hf₀, m₀, hm₀, hmode⟩ := ih hr₀
    have hmem : y ∈ DDC.ofProgram () (forwardProgram A) (t.map Prod.fst ++ [x]) := by
      rw [hy]; exact Part.mem_some y
    obtain ⟨m₁, m', h₁, hstep⟩ := (DDC.mem_ofProgram_snoc () _ _ x y).mp hmem
    rw [hm₀] at h₁
    obtain rfl := Option.some.inj h₁
    have hm' : (forwardProgram A).after () (t.map Prod.fst ++ [x]) = some m' :=
      (Program.after_snoc_eq_some _ () _ x m').mpr ⟨m₀, y, hm₀, hstep⟩
    rcases Program.step_cases _ hstep with
        ⟨⟨⟩, o, u, rfl, rfl, he⟩ | ⟨o, ⟨⟩, u, hs, q, v, rfl, rfl, he⟩
    · simp only [Program.emit, forwardProgram, DSL.callProg] at he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      refine ⟨replies_snoc.mpr ⟨hf₀, by rw [forwardAll_snoc_outer]⟩,
        _, hm', rfl, HEq.rfl⟩
    · rcases hs with _ | _
      · obtain ⟨hi, hx'⟩ := hmode
        rcases q with ⟨i', qx⟩
        dsimp only at hi hx'
        subst i'
        have hx : qx = u := eq_of_heq hx'
        subst qx
        simp only [Program.emit, forwardProgram, DSL.callProg, List.nil_append,
          ↓reduceDIte, DSL.returnProg] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ⟨replies_snoc.mpr ⟨hf₀, by rw [forwardAll_snoc_inner]⟩, _, hm', trivial⟩
      · simp at hmode

/-- One-port Boolean interface with budget `q`. -/
abbrev BudgetPort (q : ℕ) : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) q

lemma budgetPort_admits (q : ℕ) :
    ∀ xs : List (Σ _ : (BudgetPort q).I, (BudgetPort q).X ()),
      xs ≠ [] → xs.length ≤ 1 * (BudgetPort q).bound → (BudgetPort q).domain xs := by
  intro xs hne hl
  exact ⟨hne, by simpa using hl⟩

/-- On a family of one-port interfaces, restricting to port `⟨k, ()⟩` has the same length as
restricting the regrouped history to coordinate `k`. -/
lemma length_restrict_eq_sigmaAssoc {K : Type} [Fintype K] (q : K → ℕ) (k : K)
    (xs : List (Σ o : (⨂ k, BudgetPort (q k)).I, (⨂ k, BudgetPort (q k)).X o)) :
    (restrict (⟨k, ()⟩ : (⨂ k, BudgetPort (q k)).I) xs).length =
      (restrict k (xs.map (Equiv.sigmaAssoc fun k i => (BudgetPort (q k)).X i))).length := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨k', ⟨⟩⟩, b⟩
    by_cases hk : k' = k
    · subst hk
      simp [restrict, Equiv.sigmaAssoc, ih]
    · have hne : (⟨k', ()⟩ : (⨂ k, BudgetPort (q k)).I) ≠ ⟨k, ()⟩ := fun h =>
        hk (congrArg Sigma.fst h)
      simp [restrict, Equiv.sigmaAssoc, hk, hne, ih]

/-- The parallel family of `forwardAll` converters is `forwardAll` on the joint interface. -/
lemma tensorAllRaw_forwardAll {K : Type} [Fintype K] (A : K → Interface) :
    tensorAllRaw (O := fun k => (A k).I) (J := fun k => (A k).I)
      (U := fun k => (A k).X) (V := fun k => (A k).Y)
      (X := fun k => (A k).X) (Y := fun k => (A k).Y)
      (fun k => forwardAll (A k).I (A k).X (A k).Y) =
      forwardAll (⨂ k, A k).I (⨂ k, A k).X (⨂ k, A k).Y := by
  classical
  funext xs
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs, x, rfl⟩
  · simp [tensorAllRaw, relabel, parAll, forwardAll]
  · rw [List.concat_eq_append]
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k, i⟩⟩, v⟩
    · simp only [tensorAllRaw, relabel, parAll, List.map_append, List.map_singleton,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, restrict_append,
        tensorAllInputs, Equiv.coe_fn_mk, restrict_cons_self, restrict_nil,
        forwardAll_snoc_outer, Part.map_some]
      rfl
    · simp only [tensorAllRaw, relabel, parAll, List.map_append, List.map_singleton,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, restrict_append,
        tensorAllInputs, Equiv.coe_fn_mk, restrict_cons_self, restrict_nil,
        forwardAll_snoc_inner, Part.map_some]
      rfl

/-- Acceptance criterion 1: a family of forwarding programs equals the converter of their joint
forwarding program as an equation at the named certificates (`ofProgram_isDDCFrom` and
`ofPreservingProgram_isDDCFrom`). -/
lemma parallelAll_forwardProgram_eq_joint {K : Type} [Fintype K] (q : K → ℕ) :
    (⨂ₘ k, TypedConverter.ofProgram () (forwardProgram (BudgetPort (q k)))
        (forwardProgram_bounded (BudgetPort (q k))) (budgetPort_admits (q k))) =
      TypedConverter.ofPreservingProgram (A := ⨂ k, BudgetPort (q k))
        (B := ⨂ k, BudgetPort (q k)) () (forwardProgram (⨂ k, BudgetPort (q k)))
        (forwardProgram_bounded _) (fun o => some o) (forwardProgram_portPreserving _)
        (fun o => q o.1)
        (fun xs hxs o => by
          rcases o with ⟨k, ⟨⟩⟩
          rw [length_restrict_eq_sigmaAssoc q k xs]
          rcases hxs.2 k with he | hd
          · simp [he]
          · exact hd.2)
        (fun ys hne _ hport => by
          refine ⟨hne, fun k => ?_⟩
          by_cases he :
              restrict k (ys.map (Equiv.sigmaAssoc fun k i => (BudgetPort (q k)).X i)) = []
          · exact Or.inl he
          · refine Or.inr ⟨he, ?_⟩
            rw [← length_restrict_eq_sigmaAssoc q k ys]
            exact hport ⟨k, ()⟩ ⟨k, ()⟩ rfl) := by
  classical
  simp_rw [TypedConverter.ofProgram_eq_ofDDC, TypedConverter.ofPreservingProgram_eq_ofDDC]
  change PDCBehavior.tensorAll (fun k => PDCBehavior.ofDDC _ _) = PDCBehavior.ofDDC _ _
  rw [PDCBehavior.tensorAll_ofDDC]
  refine PDCBehavior.ofDDC_eq_of_le _ _
    (W := forwardAll (⨂ k, BudgetPort (q k)).I (⨂ k, BudgetPort (q k)).X
      (⨂ k, BudgetPort (q k)).Y) ?_ ?_
  · intro xs ys hr
    have hlen := hr.length
    let t := xs.zip ys
    have hx : t.map Prod.fst = xs := List.map_fst_zip hlen.ge
    have hy : t.map Prod.snd = ys := List.map_snd_zip hlen.le
    rw [← hx, ← hy] at hr ⊢
    rw [tensorAllL, replies_canon_iff _ tensorAllRaw_silentAtEmpty, replies_tensorAllRaw_iff] at hr
    rw [← tensorAllRaw_forwardAll (fun k => BudgetPort (q k)), replies_tensorAllRaw_iff]
    refine ⟨hr.2.1, fun k => ?_⟩
    exact replies_forwardProgram_le_forwardAll (BudgetPort (q k)) _ _
      ((hr.2.2 k).mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2)
  · intro xs ys hr
    exact replies_forwardProgram_le_forwardAll _ xs ys
      (hr.mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2)

/-- Acceptance criterion 2: rewrite an `ofProgram` converter into `ofDDC` form via
`ofProgram_eq_ofDDC` and apply `TypedConverter.ofDDC_ofProgramOn_smul_ofPDS` directly. -/
example {A B : Interface} {S : Type} (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ}
    (hb : P.Bounded b) (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    (Q : Distribution.ProbDist {r : InterfaceSystem B.I B.X B.Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ B.domain h})
    (t : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (TypedConverter.ofProgram s P hb hB • TypedSystem.ofPDS Q).1 t =
      Q.1.mass fun r =>
        Replies (filterDom A.domain (P.inline r.1 b s)) (t.map Prod.fst) (t.map Prod.snd) := by
  rw [TypedConverter.ofProgram_eq_ofDDC]
  exact TypedConverter.ofDDC_ofProgramOn_smul_ofPDS s P hb
    (TypedConverter.ofProgram_isDDCFrom s P hb hB) Q t

/-- `cc_normalize` distributes a parallel family of `ofProgram` converters across `∥ k, R k`. -/
example {K : Type} [Fintype K] [DecidableEq K] (q : K → ℕ)
    (R : ∀ k, TypedSystem (BudgetPort (q k))) :
    (⨂ₘ k, TypedConverter.ofProgram () (forwardProgram (BudgetPort (q k)))
        (forwardProgram_bounded (BudgetPort (q k))) (budgetPort_admits (q k))) • (∥ k, R k) =
      ∥ k, (TypedConverter.ofProgram () (forwardProgram (BudgetPort (q k)))
        (forwardProgram_bounded (BudgetPort (q k))) (budgetPort_admits (q k)) • R k) := by
  cc_normalize

#print axioms TypedConverter.ofProgram_isDDCFrom
#print axioms TypedConverter.ofProgram_eq_ofDDC
#print axioms TypedConverter.ofCostedProgram_isDDCFrom
#print axioms TypedConverter.ofCostedProgram_eq_ofDDC
#print axioms TypedConverter.ofPreservingProgram_isDDCFrom
#print axioms TypedConverter.ofPreservingProgram_eq_ofDDC

end Tests.ProgramConverterCertificate
