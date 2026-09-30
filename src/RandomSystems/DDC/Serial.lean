import RandomSystems.DDC.DDC

/-!
# Serial composition of converters

The serial composition `β ⊙ α` connects the inside interfaces of `β` to the
outside interfaces of `α`. Its reachable part is again a converter, and
attaching it is attaching `α`, then `β`. Source: Jost, printed p. 18; MR16
Section 3.3, printed p. 7.

## Main definitions

* `serialM β α`: the serial composition `β ⊙ α`
* `SerialState`: the state of `β ⊙ α` after an external history
* `DDC.comp β α`: the reachable part of `β ⊙ α`, as a converter

## Main results

* `IsDDC.comp`: the reachable part of `β ⊙ α` is a converter, with at most
  `b_α · b_β` consecutive inside queries
* `IsDDC.serialM_assoc`, `IsDDC.trim_serialM_assoc`: associativity
* `attachAlong_comp`, `attachAlong_comp_behEq`: attaching `β ⊙ α` is
  attaching `α`, then `β`
* `eq_of_behEq_total`: a system behaviourally equal to a total system is equal
  to it
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

section SerialDef

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {Xi Yi : J → Type}

/-- The routing table of `β ⊙ α` on `[β, α]`: queries of `β` go to the outside of `α`,
outside replies of `α` go back to `β`; outside replies of `β` and inside queries of `α`
are exposed. -/
def serialRouteM : Two (Σ l, twoFam V Xm l) (Σ l, twoFam Ym Xi l) →
    (Σ l : Two O J, twoFam V Xi l) ⊕ Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l)
  | ⟨none, ⟨⟨none, o⟩, v⟩⟩ => .inl ⟨⟨none, o⟩, v⟩
  | ⟨none, ⟨⟨some (), m⟩, x⟩⟩ => .inr ⟨some (), ⟨⟨none, m⟩, x⟩⟩
  | ⟨some (), ⟨⟨none, m⟩, y⟩⟩ => .inr ⟨none, ⟨⟨some (), m⟩, y⟩⟩
  | ⟨some (), ⟨⟨some (), j⟩, x⟩⟩ => .inl ⟨⟨some (), j⟩, x⟩

/-- External inputs of `β ⊙ α`: outside to `β`, inside to `α`. -/
def serialInjM : (Σ l : Two O J, twoFam U Yi l) → Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l)
  | ⟨⟨none, o⟩, u⟩ => ⟨none, ⟨⟨none, o⟩, u⟩⟩
  | ⟨⟨some (), j⟩, y⟩ => ⟨some (), ⟨⟨some (), j⟩, y⟩⟩

/-- **Serial composition** `β ⊙ α` (spec §5.3, Jost p. 18): the inside of `β` connected to the
outside of `α`. -/
noncomputable def serialM (β : InsideOutsideSystem O M U V Xm Ym) (α : InsideOutsideSystem M J Xm Ym Xi Yi) :
    InsideOutsideSystem O J U V Xi Yi :=
  interconnect (pair β α) serialRouteM serialInjM

/-- Every internal cycle of `β ⊙ α` passes through `β`, continuing only after a query of `β`. -/
theorem cyclesThrough_serial :
    CyclesThrough (IsInside (F := twoFam V Xm))
      (serialRouteM (U := U) (Ym := Ym) (Xi := Xi) (Yi := Yi)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ hy
    · exact ⟨_, rfl⟩
    · exact absurd rfl hy
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, m⟩, x⟩ hy
    · exact absurd hy (by simp [IsInside])
    · exact Or.inr ⟨_, rfl⟩
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, m⟩, y⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩

theorem IsDDC.converges_serial {b : ℕ} {β : InsideOutsideSystem O M U V Xm Ym} (hβ : IsDDC b β)
    (α : InsideOutsideSystem M J Xm Ym Xi Yi) : Converges (pair β α) serialRouteM serialInjM :=
  converges_pair cyclesThrough_serial hβ.bound

theorem IsResponsiveDDC.converges_serial {b : ℕ} {β : InsideOutsideSystem O M U V Xm Ym} (hβ : IsResponsiveDDC b β)
    (α : InsideOutsideSystem M J Xm Ym Xi Yi) : Converges (pair β α) serialRouteM serialInjM :=
  hβ.isDDC.converges_serial α

end SerialDef

section SerialAssociativity

variable {O L M J : Type} {U V : O → Type} {XL YL : L → Type}
  {XM YM : M → Type} {X Y : J → Type}

/-- Both bracketings connect the same three component histories. Flattening
their existing connections leaves identical routing and exposed inputs. -/
theorem IsDDC.serialM_assoc {bγ bβ : ℕ} {γ : InsideOutsideSystem O L U V XL YL}
    {β : InsideOutsideSystem L M XL YL XM YM} (α : InsideOutsideSystem M J XM YM X Y)
    (hγ : IsDDC bγ γ) (hβ : IsDDC bβ β) :
    serialM (serialM γ β) α = serialM γ (serialM β α) := by
  unfold serialM
  rw [pair_interconnect_left (hγ.converges_serial β), interconnect_interconnect,
    pair_interconnect_right γ (hβ.converges_serial α), interconnect_interconnect,
    pair_assoc', interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩ <;>
        rcases y with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩ <;> rfl
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩ <;> rfl
  · funext x
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩ <;> rfl

theorem serialM_assoc {bγ bβ : ℕ} {γ : InsideOutsideSystem O L U V XL YL}
    {β : InsideOutsideSystem L M XL YL XM YM} (α : InsideOutsideSystem M J XM YM X Y)
    (hγ : IsResponsiveDDC bγ γ) (hβ : IsResponsiveDDC bβ β) :
    serialM (serialM γ β) α = serialM γ (serialM β α) :=
  IsDDC.serialM_assoc α hγ.isDDC hβ.isDDC

end SerialAssociativity

/-! ## One exchange of `β ⊙ α` -/

section SerialExchange

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {Xi Yi : J → Type}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym Xi Yi} {bβ bα : ℕ}

/-- A converter waits for an outside input. -/
def Idle {O J : Type} {U V : O → Type} {Xi Yi : J → Type} (γ : InsideOutsideSystem O J U V Xi Yi)
    (h : List (Σ l, twoFam U Yi l)) : Prop :=
  Admissible γ h ∧ (h ≠ [] → (γ h).Dom) ∧ ∀ j, replyLabel γ h ≠ some ⟨some (), j⟩

/-- A converter, called at outside label `o`, waits for the reply to its query at `j`. -/
def Waits {O J : Type} {U V : O → Type} {Xi Yi : J → Type} (γ : InsideOutsideSystem O J U V Xi Yi)
    (h : List (Σ l, twoFam U Yi l)) (j : J) (o : O) : Prop :=
  Admissible γ h ∧ (γ h).Dom ∧ replyLabel γ h = some ⟨some (), j⟩ ∧ lastOuter h = some o

/-- `β` is about to reply in a call at `o`; `c` inside queries of `α` were exposed so far. -/
def SerialAtB (β : InsideOutsideSystem O M U V Xm Ym) (α : InsideOutsideSystem M J Xm Ym Xi Yi) (bα : ℕ) (o : O) (c : ℕ)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l))) : Prop :=
  ∃ G₁ z, G = G₁ ++ [⟨none, z⟩] ∧ Admissible β (restrict none G₁ ++ [z]) ∧
    lastOuter (restrict none G₁ ++ [z]) = some o ∧ Idle α (restrict (some ()) G₁) ∧
    c ≤ bα * insideRun β (restrict none G₁)

/-- `α` is about to reply in a call from `β` at `m`, while `β` is called at `o`. -/
def SerialAtA (β : InsideOutsideSystem O M U V Xm Ym) (α : InsideOutsideSystem M J Xm Ym Xi Yi) (bα : ℕ) (o : O) (c : ℕ)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l))) : Prop :=
  ∃ G₁ z m, G = G₁ ++ [⟨some (), z⟩] ∧ Admissible α (restrict (some ()) G₁ ++ [z]) ∧
    lastOuter (restrict (some ()) G₁ ++ [z]) = some m ∧ Waits β (restrict none G₁) m o ∧
    1 ≤ insideRun β (restrict none G₁) ∧
    c ≤ bα * (insideRun β (restrict none G₁) - 1) + insideRun α (restrict (some ()) G₁)

/-- The state after an exchange of `β ⊙ α` exposed `w`. -/
def SerialPostM (β : InsideOutsideSystem O M U V Xm Ym) (α : InsideOutsideSystem M J Xm Ym Xi Yi) (bα : ℕ) (o : O) (c : ℕ)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l))) (w : Σ l : Two O J, twoFam V Xi l) :
    Prop :=
  (∀ o', w.1 = ⟨none, o'⟩ → o' = o ∧ Idle β (restrict none G) ∧ Idle α (restrict (some ()) G) ∧
    lastOuter (restrict none G) = some o) ∧
  (∀ j, w.1 = ⟨some (), j⟩ → ∃ m, Waits α (restrict (some ()) G) j m ∧
    Waits β (restrict none G) m o ∧ 1 ≤ insideRun β (restrict none G) ∧
    c + 1 ≤ bα * (insideRun β (restrict none G) - 1) + insideRun α (restrict (some ()) G))

theorem insideRun_snoc_of_mem {O J : Type} {U V : O → Type} {Xi Yi : J → Type}
    {γ : InsideOutsideSystem O J U V Xi Yi} {h z} {y : Σ l, twoFam V Xi l} (hy : y ∈ γ (h ++ [z])) :
    insideRun γ (h ++ [z]) = if IsInside y then insideRun γ h + 1 else 0 := by
  rw [insideRun, run_snoc]
  by_cases hi : IsInside y
  · rw [if_pos ⟨y, hy, hi⟩, if_pos hi]; rfl
  · rw [if_neg hi, if_neg]
    rintro ⟨y', hy', hi'⟩
    exact hi (Part.mem_unique hy hy' ▸ hi')

theorem insideRun_le_of_admissible {O J : Type} {U V : O → Type} {Xi Yi : J → Type}
    {γ : InsideOutsideSystem O J U V Xi Yi} {b : ℕ} (hγ : IsDDC b γ) {h z}
    (ha : Admissible γ (h ++ [z])) : insideRun γ h ≤ b := by
  rcases eq_or_ne h [] with rfl | hne
  · simp [insideRun]
  · exact hγ.bound _ ((admissible_snoc.mp ha).2.1 hne)

theorem serialM_exchange_partial (hβ : IsDDC bβ β) (hα : IsDDC bα α) {G o' G'}
    (l : Exchange (pair β α) serialRouteM G o' G') :
    ∀ o c, SerialAtB β α bα o c G ∨ SerialAtA β α bα o c G →
      (o' = none ∧ ¬ (pair β α G').Dom ∧
        (SerialAtB β α bα o c G' ∨ SerialAtA β α bα o c G')) ∨
        ∃ w, o' = some w ∧ SerialPostM β α bα o c G' w := by
  induction l with
  | silent G hd =>
    intro o c hG
    exact Or.inl ⟨rfl, hd, hG⟩
  | out G y w hy hr =>
    intro o c hG
    apply Or.inr
    rcases hG with ⟨G₁, z, rfl, ha, hlo, hid, -⟩ | ⟨G₁, z, m, rfl, ha, hlo, hwb, h1, hc⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, o''⟩, v⟩
      · simp only [serialRouteM, Sum.inl.injEq] at hr
        subst hr
        have := hβ.replies _ _ o'' hy' rfl
        rw [hlo] at this
        obtain rfl := Option.some_inj.mp this.symm
        refine ⟨_, rfl, fun o' e => ?_, fun j e => by simp at e⟩
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e
        subst e
        refine ⟨rfl, ⟨by simpa using ha, fun _ => by simpa using Part.dom_iff_mem.mpr ⟨_, hy'⟩,
          fun j => by simp [replyLabel_of_mem _ hy']⟩, by simpa using hid, by simpa using hlo⟩
      · simp [serialRouteM] at hr

    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩
      · simp [serialRouteM] at hr
      · simp only [serialRouteM, Sum.inl.injEq] at hr
        subst hr
        refine ⟨_, rfl, fun o' e => by simp at e, fun j' e => ?_⟩
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e
        subst e
        have hrun : insideRun α (restrict (some ()) G₁ ++ [z]) =
            insideRun α (restrict (some ()) G₁) + 1 := by
          rw [insideRun_snoc_of_mem hy']; exact if_pos rfl
        refine ⟨m, ⟨by simpa using ha, by simpa using Part.dom_iff_mem.mpr ⟨_, hy'⟩,
          by simpa using replyLabel_of_mem _ hy', by simpa using hlo⟩, by simpa using hwb,
          by simpa using h1, ?_⟩
        simp only [restrict_none_snoc_right, restrict_some_snoc_right]
        rw [hrun]
        omega
  | feed G y x' o' G'' hy hr l ih =>
    intro o c hG
    rcases hG with ⟨G₁, z, rfl, ha, hlo, hid, hc⟩ | ⟨G₁, z, m, rfl, ha, hlo, hwb, h1, hc⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, m⟩, x⟩
      · simp [serialRouteM] at hr
      · simp only [serialRouteM, Sum.inr.injEq] at hr
        subst hr
        have hrun : insideRun β (restrict none G₁ ++ [z]) = insideRun β (restrict none G₁) + 1 := by
          rw [insideRun_snoc_of_mem hy']; exact if_pos rfl
        refine ih o c (Or.inr ⟨_, _, m, rfl, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [restrict_some_snoc_left]
          exact admissible_snoc.mpr ⟨hid.1, hid.2.1, (admitAfter_of_ne hid.2.2).mpr rfl⟩
        · rw [restrict_some_snoc_left, lastOuter_snoc]; rfl
        · refine ⟨by simpa using ha, by simpa using Part.dom_iff_mem.mpr ⟨_, hy'⟩,
            by simpa using replyLabel_of_mem _ hy', by simpa using hlo⟩
        · simp only [restrict_none_snoc_left]; omega
        · simp only [restrict_none_snoc_left]
          rw [hrun]
          simp only [Nat.add_sub_cancel]
          exact le_trans hc (Nat.le_add_right _ _)
    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, m'⟩, v⟩
      · simp only [serialRouteM, Sum.inr.injEq] at hr
        subst hr
        have := hα.replies _ _ m' hy' rfl
        rw [hlo] at this
        obtain rfl := Option.some_inj.mp this.symm
        obtain ⟨hba, hbd, hbr, hbo⟩ := hwb
        have hαb := insideRun_le_of_admissible hα ha
        refine ih o c (Or.inl ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩)
        · rw [restrict_none_snoc_right]
          refine admissible_snoc.mpr ⟨hba, fun _ => hbd, ?_⟩
          simp [Admits, hbr, admitAfter]
        · rw [restrict_none_snoc_right, lastOuter_snoc]
          simpa [outerOf] using hbo
        · refine ⟨by simpa using ha, fun _ => by simpa using Part.dom_iff_mem.mpr ⟨_, hy'⟩,
            fun j => by simp [replyLabel_of_mem _ hy']⟩
        · simp only [restrict_none_snoc_right]
          calc c ≤ bα * (insideRun β (restrict none G₁) - 1) + insideRun α (restrict (some ()) G₁) := hc
            _ ≤ bα * (insideRun β (restrict none G₁) - 1) + bα := by omega
            _ = bα * insideRun β (restrict none G₁) := by
              obtain ⟨k, hk⟩ : ∃ k, insideRun β (restrict none G₁) = k + 1 := ⟨_, (Nat.sub_add_cancel h1).symm⟩
              rw [hk]; simp [Nat.mul_succ]
      · simp [serialRouteM] at hr

end SerialExchange

/-! ## The reachable part of `β ⊙ α` is a converter -/

section SerialClosure

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {Xi Yi : J → Type}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym Xi Yi} {bβ bα : ℕ}

theorem exchange_silent_of_not_dom {X Y B : Type} {s : System X Y} {route : Y → B ⊕ X} {G o G'}
    (l : Exchange s route G o G') (hd : ¬ (s G).Dom) : o = none := by
  cases l with
  | silent => rfl
  | out _ y _ hy => exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩) hd
  | feed _ y _ _ _ hy => exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩) hd

theorem run_trim {X Y : Type} (P : Y → Prop) (s : System X Y) {h : List X} (hr : Reach s h) :
    run P (trim s) h = run P s h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih =>
    rw [run_snoc, run_snoc, ih (reach_snoc_iff.mp hr).1]
    simp [trim, hr]

variable (β α bα) in
/-- The state of `β ⊙ α` after the external history `u`, with last reply `o`. -/
def SerialState (u : List (Σ l : Two O J, twoFam U Yi l)) (o : Option (Σ l : Two O J, twoFam V Xi l))
    (H : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l))) : Prop :=
  lastOuter (restrict none H) = lastOuter u ∧
  ((u = [] ∧ o = none ∧ H = []) ∨
   (∃ w, o = some w ∧ (∃ o', w.1 = ⟨none, o'⟩) ∧ Idle β (restrict none H) ∧
      Idle α (restrict (some ()) H)) ∨
   (∃ w j m o', o = some w ∧ w.1 = ⟨some (), j⟩ ∧ lastOuter u = some o' ∧
      Waits α (restrict (some ()) H) j m ∧ Waits β (restrict none H) m o' ∧
      1 ≤ insideRun β (restrict none H) ∧
      insideRun (serialM β α) u ≤
        bα * (insideRun β (restrict none H) - 1) + insideRun α (restrict (some ()) H)))

theorem serialM_next_partial (hβ : IsDDC bβ β) (hα : IsDDC bα α) {u o H}
    (r : Induces (pair β α) serialRouteM serialInjM u o H) (hs : SerialState β α bα u o H)
    (a : Σ l : Two O J, twoFam U Yi l) :
    (admitAfter (o.map (·.1)) a.1 →
      (¬ (serialM β α (u ++ [a])).Dom ∧ (¬ Responsive β ∨ ¬ Responsive α) ∧
        ∃ H', Induces (pair β α) serialRouteM serialInjM (u ++ [a]) none H' ∧
          Admissible β (restrict none H') ∧ Admissible α (restrict (some ()) H')) ∨
      ∃ w H', Induces (pair β α) serialRouteM serialInjM (u ++ [a])
        (some w) H' ∧ SerialState β α bα (u ++ [a]) (some w) H' ∧
        ∀ o', w.1 = ⟨none, o'⟩ → lastOuter (u ++ [a]) = some o') ∧
      (¬ admitAfter (o.map (·.1)) a.1 → ∀ o' H',
        Induces (pair β α) serialRouteM serialInjM (u ++ [a]) o' H' → o' = none) := by
  obtain ⟨hlo, hs⟩ := hs
  have hsnoc : ∀ o' H', Induces (pair β α) serialRouteM serialInjM (u ++ [a]) o' H' →
      Exchange (pair β α) serialRouteM (H ++ [serialInjM a]) o' H' := by
    intro o' H' r'
    obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
    obtain ⟨-, rfl⟩ := r.det r₀
    exact l
  -- the exchange started by an admitted input
  have finish : ∀ o₁ c, (SerialAtB β α bα o₁ c (H ++ [serialInjM a]) ∨
      SerialAtA β α bα o₁ c (H ++ [serialInjM a])) → lastOuter (u ++ [a]) = some o₁ →
      insideRun (serialM β α) u = c →
      (¬ (serialM β α (u ++ [a])).Dom ∧ (¬ Responsive β ∨ ¬ Responsive α) ∧
        ∃ H', Induces (pair β α) serialRouteM serialInjM (u ++ [a]) none H' ∧
          Admissible β (restrict none H') ∧ Admissible α (restrict (some ()) H')) ∨
      ∃ w H', Induces (pair β α) serialRouteM serialInjM (u ++ [a]) (some w) H' ∧
        SerialState β α bα (u ++ [a]) (some w) H' ∧
        ∀ o', w.1 = ⟨none, o'⟩ → lastOuter (u ++ [a]) = some o' := by
    intro o₁ c hst hlo₁ hcu
    obtain ⟨o', H', r'⟩ := (hβ.converges_serial α) (u ++ [a])
    rcases serialM_exchange_partial hβ hα (hsnoc _ _ r') o₁ c hst with
      ⟨rfl, hsil, hst'⟩ | ⟨w, rfl, hpo, hpi⟩
    · refine Or.inl ⟨not_dom_of_induces_none r', ?_, H', r', ?_⟩
      · rcases hst' with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, z, m, rfl, ha, -⟩
        · rw [pair_left] at hsil
          exact Or.inl (fun hr => hsil (hr _ ha (by simp)))
        · rw [pair_right] at hsil
          exact Or.inr (fun hr => hsil (hr _ ha (by simp)))
      · rcases hst' with ⟨G₁, z, rfl, ha, -, hid, -⟩ | ⟨G₁, z, m, rfl, ha, -, hwb, -⟩
        · exact ⟨by rw [restrict_none_snoc_left]; exact ha,
            by rw [restrict_some_snoc_left]; exact hid.1⟩
        · exact ⟨by rw [restrict_none_snoc_right]; exact hwb.1,
            by rw [restrict_some_snoc_right]; exact ha⟩
    apply Or.inr
    have hw' : w ∈ serialM β α (u ++ [a]) := by rw [serialM]; exact mem_of_induces_some r'
    refine ⟨w, H', r', ?_, fun o' e => by rw [(hpo o' e).1]; exact hlo₁⟩
    rcases w with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    · obtain ⟨rfl, hib, hia, hlb⟩ := hpo l rfl
      exact ⟨hlb.trans hlo₁.symm, Or.inr (Or.inl ⟨_, rfl, ⟨l, rfl⟩, hib, hia⟩)⟩
    · obtain ⟨m, hwa, hwb, h1, hc⟩ := hpi l rfl
      refine ⟨hwb.2.2.2.trans hlo₁.symm, Or.inr (Or.inr ⟨_, l, m, o₁, rfl, rfl, hlo₁, hwa, hwb, h1, ?_⟩)⟩
      rw [insideRun_snoc_of_mem hw', if_pos (show IsInside (⟨⟨some (), l⟩, v⟩ : Σ l, twoFam V Xi l)
        from rfl), hcu]
      exact hc
  -- an input that is not admitted reaches a silent component
  have silent : ¬ (pair β α (H ++ [serialInjM a])).Dom → ∀ o' H',
      Induces (pair β α) serialRouteM serialInjM (u ++ [a]) o' H' → o' = none :=
    fun hd o' H' r' => exchange_silent_of_not_dom (hsnoc _ _ r') hd
  have hmem : ∀ w, o = some w → w ∈ serialM β α u := fun w e => by
    subst e; rw [serialM]; exact mem_of_induces_some r
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨w, rfl, ⟨o₀, hw⟩, hib, hia⟩ |
      ⟨w, j, m, o₀, rfl, hw, hlu, hwa, hwb, h1, hc⟩
  · -- the first input
    have hia : Idle α (restrict (some ()) ([] : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Yi l)))) :=
      ⟨admissible_nil, fun h => absurd rfl h, fun j => by
        rw [restrict_nil, replyLabel, dif_neg hα.dds.1]; simp⟩
    rcases a with ⟨⟨_ | ⟨⟨⟩⟩, o₁⟩, v⟩
    · refine ⟨fun _ => finish o₁ 0 (Or.inl ⟨[], _, rfl, ?_, ?_, hia, by simp⟩) ?_ (by simp [insideRun]),
        fun hna => absurd rfl hna⟩
      · refine admissible_snoc.mpr ⟨admissible_nil, fun h => absurd rfl h, ?_⟩
        rw [restrict_nil, Admits, replyLabel, dif_neg hβ.dds.1]; rfl
      · simp [lastOuter, outerOf]
      · simp [lastOuter, outerOf]
    · refine ⟨fun had => absurd had (by simp [admitAfter]), fun _ => silent ?_⟩
      show ¬ (pair β α ([] ++ [⟨some (), ⟨⟨some (), o₁⟩, v⟩⟩])).Dom
      rw [pair_right]
      intro hd
      have := hα.admits _ _ hd
      rw [Admits, admitAfter_of_ne hia.2.2] at this
      exact absurd this (by simp)
  · -- after an outside reply: only outside inputs are admitted
    have hwu := hmem w rfl
    have hrun0 : insideRun (serialM β α) u = 0 := by
      rcases List.eq_nil_or_concat u with rfl | ⟨u', a', rfl⟩
      · exact rfl
      · rw [List.concat_eq_append] at hwu ⊢
        rw [insideRun_snoc_of_mem hwu, if_neg (by simp [IsInside, hw])]
    rcases a with ⟨⟨_ | ⟨⟨⟩⟩, o₁⟩, v⟩
    · refine ⟨fun _ => finish o₁ 0 (Or.inl ⟨H, _, rfl, admissible_snoc.mpr ⟨hib.1, hib.2.1,
        (admitAfter_of_ne hib.2.2).mpr rfl⟩, by simp [lastOuter_snoc, outerOf], hia, by simp⟩)
        (by simp [lastOuter_snoc, outerOf]) hrun0, fun hna => absurd (by simp [hw, admitAfter]) hna⟩
    · refine ⟨fun had => absurd had (by simp [admitAfter, hw]), fun _ => silent ?_⟩
      show ¬ (pair β α (H ++ [⟨some (), ⟨⟨some (), o₁⟩, v⟩⟩])).Dom
      rw [pair_right]
      intro hd
      have := hα.admits _ _ hd
      rw [Admits, admitAfter_of_ne hia.2.2] at this
      exact absurd this (by simp)
  · -- after an inside query at `j`: only the reply at `j` is admitted
    have hlab : ∀ l : Two O J, admitAfter ((some w).map (·.1)) l ↔ l = ⟨some (), j⟩ := by
      intro l; simp [hw, admitAfter]
    rcases a with ⟨⟨_ | ⟨⟨⟩⟩, j'⟩, v⟩
    · refine ⟨fun had => absurd ((hlab _).mp had) (by simp), fun _ => silent ?_⟩
      show ¬ (pair β α (H ++ [⟨none, ⟨⟨none, j'⟩, v⟩⟩])).Dom
      rw [pair_left]
      intro hd
      have := hβ.admits _ _ hd
      rw [Admits, hwb.2.2.1] at this
      exact absurd this (by simp [admitAfter])
    · by_cases e : j' = j
      · subst e
        refine ⟨fun _ => finish o₀ (insideRun (serialM β α) u)
          (Or.inr ⟨H, _, m, rfl, ?_, ?_, hwb, h1, hc⟩) (by simpa [lastOuter_snoc, outerOf] using hlu) rfl,
          fun hna => absurd ((hlab _).mpr rfl) hna⟩
        · refine admissible_snoc.mpr ⟨hwa.1, fun _ => hwa.2.1, ?_⟩
          simp [Admits, hwa.2.2.1, admitAfter]
        · rw [lastOuter_snoc]; simpa [outerOf] using hwa.2.2.2
      · refine ⟨fun had => absurd ((hlab _).mp had) (by simp [e]), fun _ => silent ?_⟩
        show ¬ (pair β α (H ++ [⟨some (), ⟨⟨some (), j'⟩, v⟩⟩])).Dom
        rw [pair_right]
        intro hd
        have := hα.admits _ _ hd
        rw [Admits, hwa.2.2.1] at this
        exact absurd this (by simp [admitAfter, e])

/-- The responsive case follows by excluding a stopped component. -/
theorem serialM_next (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α) {u o H}
    (r : Induces (pair β α) serialRouteM serialInjM u o H) (hs : SerialState β α bα u o H)
    (a : Σ l : Two O J, twoFam U Yi l) :
    (admitAfter (o.map (·.1)) a.1 → ∃ w H', Induces (pair β α) serialRouteM serialInjM (u ++ [a])
        (some w) H' ∧ SerialState β α bα (u ++ [a]) (some w) H' ∧
        ∀ o', w.1 = ⟨none, o'⟩ → lastOuter (u ++ [a]) = some o') ∧
      (¬ admitAfter (o.map (·.1)) a.1 → ∀ o' H',
        Induces (pair β α) serialRouteM serialInjM (u ++ [a]) o' H' → o' = none) := by
  have hn := serialM_next_partial hβ.isDDC hα.isDDC r hs a
  refine ⟨fun ha => ?_, hn.2⟩
  rcases hn.1 ha with ⟨_, hf, -⟩ | hr
  · exact (hf.elim (fun h => h hβ.responsive) (fun h => h hα.responsive)).elim
  · exact hr

theorem replyLabel_serialM {u o H} (r : Induces (pair β α) serialRouteM serialInjM u o H) :
    replyLabel (serialM β α) u = o.map (·.1) := by
  rcases o with _ | w
  · have hd : ¬ (serialM β α u).Dom := by rw [serialM]; exact not_dom_of_induces_none r
    simp [replyLabel, hd]
  · have hw : w ∈ serialM β α u := by rw [serialM]; exact mem_of_induces_some r
    simp [replyLabel_of_mem _ hw]

theorem serialM_reach_partial (hβ : IsDDC bβ β) (hα : IsDDC bα α) :
    ∀ u, Reach (serialM β α) u → ∃ o H, Induces (pair β α) serialRouteM serialInjM u o H ∧
      SerialState β α bα u o H ∧
      ∀ u' a w, u = u' ++ [a] → o = some w → ∀ o', w.1 = ⟨none, o'⟩ → lastOuter u = some o' := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨none, [], Induces.nil, ⟨by simp [lastOuter], Or.inl ⟨rfl, rfl, rfl⟩⟩,
      fun u' a w e => by simp at e⟩
  | append_singleton u a ih =>
    intro hr
    obtain ⟨hr₀, hd⟩ := reach_snoc_iff.mp hr
    obtain ⟨o, H, r, hs, -⟩ := ih hr₀
    obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.get_mem hd)
    have hnext := serialM_next_partial hβ hα r hs a
    by_cases had : admitAfter (o.map (·.1)) a.1
    · rcases hnext.1 had with ⟨hf, -, -⟩ | ⟨w, H'', r'', hs'', hlast⟩
      · exact (hf hd).elim
      refine ⟨some w, H'', r'', hs'', fun u' a' w' e ew o' ho => ?_⟩
      obtain ⟨-, e'⟩ := List.append_inj' e rfl
      obtain rfl : a = a' := by simpa using e'
      cases ew
      exact hlast o' ho
    · exact absurd (hnext.2 had _ _ r') (by simp)

theorem serialM_reach (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α) :
    ∀ u, Reach (serialM β α) u → ∃ o H, Induces (pair β α) serialRouteM serialInjM u o H ∧
      SerialState β α bα u o H ∧
      ∀ u' a w, u = u' ++ [a] → o = some w → ∀ o', w.1 = ⟨none, o'⟩ → lastOuter u = some o' :=
  serialM_reach_partial hβ.isDDC hα.isDDC

theorem reach_of_trim {X Y : Type} {s : System X Y} {h : List X} (hd : (trim s h).Dom) : Reach s h := by
  by_contra hr
  simp [trim, hr] at hd

theorem serialM_reach_of_admissible (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α) :
    ∀ h, Admissible (trim (serialM β α)) h → Reach (serialM β α) h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; exact reach_nil _
  | append_singleton h z ih =>
    intro ha
    obtain ⟨ha₀, -, hz⟩ := admissible_snoc.mp ha
    have hr₀ := ih ha₀
    obtain ⟨o, H, r, hs, -⟩ := serialM_reach hβ hα h hr₀
    have had : admitAfter (o.map (·.1)) z.1 := by
      have := hz
      rw [Admits, replyLabel_trim _ hr₀, replyLabel_serialM r] at this
      exact this
    obtain ⟨w, H', r', -, -⟩ := (serialM_next hβ hα r hs z).1 had
    refine reach_snoc_iff.mpr ⟨hr₀, Part.dom_iff_mem.mpr ⟨w, ?_⟩⟩
    rw [serialM]
    exact mem_of_induces_some r'

/-- **Serial composition preserves converters** (spec §5.3): the reachable part of `β ⊙ α` is a
converter with at most `b_α · b_β` consecutive inside queries. -/
theorem IsDDC.comp (hβ : IsDDC bβ β) (hα : IsDDC bα α) :
    IsDDC (bα * bβ) (trim (serialM β α)) := by
  have hrl : ∀ {u}, Reach (serialM β α) u → replyLabel (trim (serialM β α)) u =
      replyLabel (serialM β α) u := fun hr => replyLabel_trim _ hr
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hd
    have := reach_of_trim hd
    simp only [trim, reach_nil, if_true] at hd
    rw [serialM] at hd
    exact not_dom_of_induces_none Induces.nil hd
  · rintro l₁ l₂ ⟨e, rfl⟩ hne hd
    exact trim_prefix_closed _ hd hne
  · intro h z hd
    have hr := reach_of_trim hd
    obtain ⟨o, H, r, hs, -⟩ := serialM_reach_partial hβ hα h (reach_snoc_iff.mp hr).1
    have hd' := (reach_snoc_iff.mp hr).2
    obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.get_mem hd')
    have hnext := serialM_next_partial hβ hα r hs z
    by_cases had : admitAfter (o.map (·.1)) z.1
    · rw [Admits, hrl (reach_snoc_iff.mp hr).1, replyLabel_serialM r]
      exact had
    · exact absurd (hnext.2 had _ _ r') (by simp)
  · intro h hd
    have hr := reach_of_trim hd
    rw [insideRun, run_trim _ _ hr]
    obtain ⟨o, H, r, ⟨-, hs⟩, -⟩ := serialM_reach_partial hβ hα h hr
    rcases hs with ⟨rfl, -, -⟩ | ⟨w, rfl, ⟨o₀, hw⟩, -, -⟩ |
        ⟨w, j, m, o₀, rfl, -, -, hwa, hwb, h1, hc⟩
    · simp
    · have hwu : w ∈ serialM β α h := by rw [serialM]; exact mem_of_induces_some r
      rcases List.eq_nil_or_concat h with rfl | ⟨h', a', rfl⟩
      · simp
      · rw [List.concat_eq_append] at hwu ⊢
        rw [run_snoc, if_neg]
        · exact Nat.zero_le _
        · rintro ⟨w', hw', hi⟩
          rw [Part.mem_unique hwu hw'] at hw
          simp [IsInside, hw] at hi
    · have hkb := hβ.bound _ hwb.2.1
      have hrb := hα.bound _ hwa.2.1
      calc insideRun (serialM β α) h
          ≤ bα * (insideRun β (restrict none H) - 1) + insideRun α (restrict (some ()) H) := hc
        _ ≤ bα * (bβ - 1) + bα := by
          have := Nat.mul_le_mul_left bα (Nat.sub_le_sub_right hkb 1)
          omega
        _ = bα * bβ := by
          obtain ⟨k, hk⟩ : ∃ k, bβ = k + 1 := ⟨bβ - 1, by omega⟩
          rw [hk]; simp [Nat.mul_succ]
  · intro h y o' hy ho'
    have hr := reach_of_trim (Part.dom_iff_mem.mpr ⟨y, hy⟩)
    obtain ⟨o, H, r, -, hlast⟩ := serialM_reach_partial hβ hα h hr
    simp only [trim, hr, if_true] at hy
    have hne : h ≠ [] := by
      rintro rfl
      rw [serialM] at hy
      exact not_dom_of_induces_none Induces.nil (Part.dom_iff_mem.mpr ⟨y, hy⟩)
    obtain ⟨h', a, rfl⟩ := List.eq_nil_or_concat h |>.resolve_left hne
    rw [List.concat_eq_append] at *
    have hwu : ∀ w, o = some w → w = y := fun w e => by
      subst e
      have : w ∈ serialM β α (h' ++ [a]) := by rw [serialM]; exact mem_of_induces_some r
      exact Part.mem_unique this hy
    rcases o with _ | w
    · rw [serialM] at hy
      exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩) (not_dom_of_induces_none r)
    · obtain rfl := hwu w rfl
      exact hlast h' a w rfl rfl o' ho'

theorem IsResponsiveDDC.comp (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α) :
    IsResponsiveDDC (bα * bβ) (trim (serialM β α)) := by
  apply isResponsiveDDC_iff.mpr
  refine ⟨hβ.isDDC.comp hα.isDDC, fun h ha hne => ?_⟩
  have hr := serialM_reach_of_admissible hβ hα h ha
  simp only [trim, hr, if_true]
  exact hr h [] (by simp) hne

end SerialClosure

/-! ## Attaching `β ⊙ α` is attaching `α`, then `β` -/

section SerialLaw

variable {I O M J : Type} {X Y : I → Type} {U V : O → Type} {Xm Ym : M → Type} (ι : J → I)

/-- The outside labels of `α^ι R`. -/
abbrev outerOfAlong : M → Free (alongSet (O := M) ι) :=
  fun m => ⟨⟨none, ⟨none, m⟩⟩, outside_not_mem_alongSet ι m⟩

theorem outerOfAlong_injective : Function.Injective (outerOfAlong (J := J) (M := M) ι) := by
  intro a b h
  simpa [outerOfAlong] using congrArg Subtype.val h

theorem free_not_mem_outerOfAlong {i : I} (h : (⟨some (), i⟩ : Two (Two M J) I) ∉ alongSet ι) :
    (⟨some (), ⟨⟨some (), i⟩, h⟩⟩ : Two (Two O M) (Free (alongSet (O := M) ι))) ∉
      alongSet (O := O) (outerOfAlong (M := M) ι) := by
  rintro ⟨m, hm⟩
  simp [outerOfAlong] at hm

/-- Inputs of `(β ⊙ α)^ι R`, read as inputs of `β^(α^ι R)`. -/
def serialAppIn : (Σ l : Free (alongSet (O := O) ι), twoFam (twoFam U ((Y ∘ ι))) X l.1) →
    Σ l : Free (alongSet (O := O) (outerOfAlong (M := M) ι)),
      twoFam (twoFam U ((fun l : Free (alongSet (O := M) ι) => twoFam (twoFam Ym (X ∘ ι)) Y l.1) ∘
        outerOfAlong ι)) (fun l : Free (alongSet (O := M) ι) => twoFam (twoFam Xm (Y ∘ ι)) X l.1) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, u⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩, u⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨⟨⟨some (), i⟩, h⟩, x⟩ => ⟨⟨⟨some (), ⟨⟨some (), i⟩, h⟩⟩, free_not_mem_outerOfAlong (O := O) (M := M) ι h⟩, x⟩

/-- Outputs of `β^(α^ι R)`, read as outputs of `(β ⊙ α)^ι R`. -/
def serialAppOut : (Σ l : Free (alongSet (O := O) (outerOfAlong (M := M) ι)),
      twoFam (twoFam V ((fun l : Free (alongSet (O := M) ι) => twoFam (twoFam Xm (Y ∘ ι)) X l.1) ∘
        outerOfAlong ι)) (fun l : Free (alongSet (O := M) ι) => twoFam (twoFam Ym (X ∘ ι)) Y l.1) l.1) →
    Σ l : Free (alongSet (O := O) ι), twoFam (twoFam V (X ∘ ι)) Y l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, v⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩, v⟩
  | ⟨⟨⟨none, ⟨some (), m⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ m) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, m⟩⟩, _⟩⟩, h⟩, _⟩ => absurd ⟨m, rfl⟩ h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h'⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet ι j) h'
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, _⟩, y⟩ => ⟨⟨⟨some (), i⟩, h'⟩, y⟩

variable {ι}

theorem attachAlong_serialM (hι : Function.Injective ι) (β : InsideOutsideSystem O M U V Xm Ym)
    (α : InsideOutsideSystem M J Xm Ym (X ∘ ι) (Y ∘ ι)) (R : InterfaceSystem I X Y)
    (hβα : Converges (pair β α) serialRouteM serialInjM)
    (hαR : Converges (pair α R) (alongRoute ι) (alongInj ι)) :
    attachAlong ι (serialM β α) R =
      relabel (attachAlong (outerOfAlong ι) β (attachAlong ι α R)) (serialAppIn ι) (serialAppOut ι) := by
  unfold attachAlong connect pairI serialM
  simp only [interconnect_relabel]
  rw [pair_interconnect_left hβα, interconnect_interconnect, pair_interconnect_right β hαR,
    interconnect_interconnect, pair_assoc', interconnect_relabel, relabel_interconnect]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
      · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
        · simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong]
        · simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong]
      · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
        · simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong]
          rw [liftC_alongRouting_image (outerOfAlong ι) (outerOfAlong_injective ι) l]
        · simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong]
    · rcases y with ⟨i, w⟩
      by_cases hi : i ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := hi
        simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong]
      · simp only [alongRoute, alongInj, routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, joinOut, splitIn, Function.comp_def]
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image ι hι, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), serialRouteM, serialInjM, serialAppOut, serialAppIn, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeOpt, routeRight, injOpt, alongRoute, alongInj, Set.mem_range, Subtype.ext_iff, outerOfAlong, hi, free_not_mem_outerOfAlong (O := O) (M := M) ι (sys_not_mem_alongSet ι hi)]
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, z⟩, hz⟩, v⟩
    · rcases z with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet ι o) hz
    · rfl

end SerialLaw

/-! ## Behavioural equality and attachment; the serial law for converters -/

section SerialComp

theorem EqOnReachable.rfl' {X Y : Type} (s : System X Y) : s ≈ₛ s := ⟨fun _ => Iff.rfl, fun _ _ _ => rfl⟩

theorem EqOnReachable.pair_left {A₁ B₁ A₂ B₂ : Type} {a a' : System A₁ B₁} (ha : a ≈ₛ a') (b : System A₂ B₂) :
    pair a b ≈ₛ pair a' b :=
  EqOnReachable.parAll fun o => by cases o with
    | none => exact ha
    | some _ => exact EqOnReachable.rfl' b

theorem EqOnReachable.serialM {O M J : Type} {U V : O → Type} {Xm Ym : M → Type}
    {X Y : J → Type} {β β' : InsideOutsideSystem O M U V Xm Ym} {α α' : InsideOutsideSystem M J Xm Ym X Y}
    (hβ : β ≈ₛ β') (hα : α ≈ₛ α') : serialM β α ≈ₛ serialM β' α' := by
  apply EqOnReachable.interconnect
  exact EqOnReachable.parAll (fun i => by cases i with
    | none => exact hβ
    | some _ => exact hα)

/-- Associativity also holds after restricting each intermediate converter to
its reachable histories. -/
theorem IsDDC.trim_serialM_assoc {O L M J : Type} {U V : O → Type} {XL YL : L → Type}
    {XM YM : M → Type} {X Y : J → Type} {bγ bβ : ℕ}
    {γ : InsideOutsideSystem O L U V XL YL} {β : InsideOutsideSystem L M XL YL XM YM}
    (α : InsideOutsideSystem M J XM YM X Y) (hγ : IsDDC bγ γ) (hβ : IsDDC bβ β) :
    trim (serialM (trim (serialM γ β)) α) = trim (serialM γ (trim (serialM β α))) := by
  have hl := (trim_behEq (serialM γ β)).serialM (EqOnReachable.rfl' α)
  have hr := (EqOnReachable.rfl' γ).serialM (trim_behEq (serialM β α))
  rw [IsDDC.serialM_assoc α hγ hβ] at hl
  exact (hl.trans hr.symm).trim_eq (by simp [SilentAtEmpty, serialM]) (by simp [SilentAtEmpty, serialM])

theorem trim_serialM_assoc {O L M J : Type} {U V : O → Type} {XL YL : L → Type}
    {XM YM : M → Type} {X Y : J → Type} {bγ bβ : ℕ}
    {γ : InsideOutsideSystem O L U V XL YL} {β : InsideOutsideSystem L M XL YL XM YM}
    (α : InsideOutsideSystem M J XM YM X Y) (hγ : IsResponsiveDDC bγ γ) (hβ : IsResponsiveDDC bβ β) :
    trim (serialM (trim (serialM γ β)) α) = trim (serialM γ (trim (serialM β α))) :=
  IsDDC.trim_serialM_assoc α hγ.isDDC hβ.isDDC

namespace DDC

/-- Serial composition is the reachable part of the existing system attachment. -/
noncomputable def comp {O M J : Type} {U V : O → Type} {Xm Ym : M → Type}
    {X Y : J → Type} (β : DDC O M U V Xm Ym) (α : DDC M J Xm Ym X Y) :
    DDC O J U V X Y :=
  ⟨trim (serialM β.1 α.1), by
    obtain ⟨bβ, hβ⟩ := β.2
    obtain ⟨bα, hα⟩ := α.2
    exact ⟨bα * bβ, hβ.comp hα⟩⟩

theorem comp_assoc {O L M J : Type} {U V : O → Type} {XL YL : L → Type}
    {XM YM : M → Type} {X Y : J → Type}
    (γ : DDC O L U V XL YL) (β : DDC L M XL YL XM YM) (α : DDC M J XM YM X Y) :
    comp (comp γ β) α = comp γ (comp β α) := by
  apply Subtype.ext
  obtain ⟨bγ, hγ⟩ := γ.2
  obtain ⟨bβ, hβ⟩ := β.2
  exact IsDDC.trim_serialM_assoc α.1 hγ hβ

end DDC

variable {I O J : Type} {X Y : I → Type} {U V : O → Type}

theorem EqOnReachable.attachAlong {ι : J → I} {α α' : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)} (hα : α ≈ₛ α')
    (R : InterfaceSystem I X Y) : SystemAlgebra.attachAlong ι α R ≈ₛ SystemAlgebra.attachAlong ι α' R := by
  unfold SystemAlgebra.attachAlong connect pairI
  exact EqOnReachable.interconnect (EqOnReachable.relabel (EqOnReachable.pair_left hα R) _ _) _ _

/-- A system behaviourally equal to a total system, and silent before the first input, is it. -/
theorem eq_of_behEq_total {A B : Type} {s t : System A B} (hst : s ≈ₛ t)
    (ht : ∀ h, (t h).Dom ↔ h ≠ []) (hs : SilentAtEmpty s) (ht₀ : SilentAtEmpty t) : s = t := by
  funext h
  rcases eq_or_ne h [] with rfl | hne
  · exact Part.ext fun b => ⟨fun hb => absurd (Part.dom_iff_mem.mpr ⟨b, hb⟩) hs,
      fun hb => absurd (Part.dom_iff_mem.mpr ⟨b, hb⟩) ht₀⟩
  · have hr : Reach t h := fun h' e he hne' => (ht h').mpr hne'
    exact hst.2 h ((hst.1 h).mpr hr) hne

theorem silentAtEmpty_attachAlong {ι : J → I} (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (R : InterfaceSystem I X Y) :
    SilentAtEmpty (attachAlong ι α R) := by
  rw [attachAlong_eq]
  exact not_dom_of_induces_none Induces.nil

theorem TotalResource.relabel {R : InterfaceSystem I X Y} (hR : TotalResource R)
    {L : Type} {F G : L → Type} (f : (Σ l, F l) → Σ i, X i) (g : (Σ i, Y i) → Σ l, G l)
    (hfg : ∀ h a y, y ∈ R ((h ++ [a]).map f) → (g y).1 = a.1) :
    TotalResource (SystemAlgebra.relabel R f g) := by
  refine ⟨fun h => ?_, fun h a y hy => ?_⟩
  · simp only [SystemAlgebra.relabel, Part.map_Dom]
    rw [hR.1]
    simp
  · obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
    exact hfg h a y' hy'

end SerialComp

section SerialCompLaw

variable {I O M J : Type} {X Y : I → Type} {U V : O → Type} {Xm Ym : M → Type} {ι : J → I}
  {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym (X ∘ ι) (Y ∘ ι)} {R : InterfaceSystem I X Y}

/-- Serial attachment preserves behavior for arbitrary partial systems, with heterogeneous
interfaces. Only the converters' internal-query bounds are needed for regrouping. -/
theorem attachAlong_comp_behEq (hι : Function.Injective ι) (hβ : IsResponsiveDDC bβ β)
    (hα : IsResponsiveDDC bα α) :
    attachAlong ι (trim (serialM β α)) R ≈ₛ
      relabel (attachAlong (outerOfAlong ι) β (attachAlong ι α R))
        (serialAppIn ι) (serialAppOut ι) := by
  rw [← attachAlong_serialM hι β α R (hβ.converges_serial α) (hα.converges_along R)]
  exact EqOnReachable.attachAlong (trim_behEq _) R

/-- **Serial attachment** (MR16 §3.3, printed p. 7: “(β ◦ α)ⁱR = βⁱ(αⁱR)”): attaching the
composite converter is attaching `α`, then `β`. -/
theorem attachAlong_comp (hι : Function.Injective ι) (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α)
    (hR : TotalResource R) :
    attachAlong ι (trim (serialM β α)) R =
      relabel (attachAlong (outerOfAlong ι) β (attachAlong ι α R)) (serialAppIn ι) (serialAppOut ι) := by
  have hraw := attachAlong_serialM hι β α R (hβ.converges_serial α) (hα.converges_along R)
  rw [← hraw]
  have hαR := hα.totalResource_along hι hR
  have hβαR := hβ.totalResource_along (outerOfAlong_injective ι) hαR
  refine eq_of_behEq_total (EqOnReachable.attachAlong (trim_behEq _) R) ?_ (silentAtEmpty_attachAlong _ _)
    (silentAtEmpty_attachAlong _ _)
  intro h
  rw [hraw]
  simp only [relabel, Part.map_Dom]
  rw [hβαR.1]
  simp

end SerialCompLaw

end SystemAlgebra
