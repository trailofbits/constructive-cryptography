module

public import RandomSystems.Converter.QueryRouting
public import RandomSystems.Converter.Program

/-!
# Program presentation of one-query routing

`routingProgram` presents `routingCall` with no state between invocations.
`routingConverter_eq_ofProgramOn` identifies its complete-history converter with the existing
router, including the canonical schedule and outside-domain filter. This equation transports
program attachment laws to routing without changing the converter or its domain guarantee.

`routingProgram_pending` recovers the retained outside input before the first inside reply.
It gives the common output rule in `routingProgram_mem_callRule`; responsiveness then upgrades
reply inclusion to complete-history equality in `routingProgram_eq_canon_callRule`.
-/

@[expose] public section

namespace SystemAlgebra

-- `O`, `J` are the outside and inside ports, with query families `U`, `X` and replies `V`, `Y`.
variable {O J : Type} {U V : O → Type} {X Y : J → Type}
    -- `request u` is the one inside query; `answer u r` translates its reply at outside port `u.1`.
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)

/-- The stateless program presentation of `routingCall`: pass it the current inside replies
and pair its outside answer with the unique state `()`. -/
def routingProgram : Program Unit O J U V X Y :=
  fun _ o u h => (routingCall request answer ⟨o, u⟩ (h.map Prod.snd)).map ((), ·) id

/-- The routing program makes at most one inside query, for arbitrary inside replies. -/
lemma routingProgram_bounded : (routingProgram request answer).Bounded 1 := by
  intro s o u h q _ hq
  cases h with
  | nil => exact Nat.zero_lt_one
  | cons z h => cases hq

/-- A pending routing invocation retains its outside input and has not received a reply.
The stored query is `request ⟨o,u⟩`; `currentCall` recovers the same input with no replies. -/
lemma routingProgram_pending
    -- `xs` is the complete input history; `o`, `u` are the pending outside port and input.
    -- `s` is the unique program state.
    (xs : List (Σ l, twoFam U Y l)) {o : O} {s : Unit} {u : U o}
    -- `h` records inside exchanges; `q` is the pending query.
    {h : List ((Σ j, X j) × (Σ j, Y j))} {q : Σ j, X j}
    -- `hm` identifies the program mode reached after `xs`.
    (hm : (routingProgram request answer).after () xs = some (.busy o s u h q)) :
    h = [] ∧ q = request ⟨o, u⟩ ∧ currentCall xs.reverse [] = some (⟨o, u⟩, []) := by
  induction xs using List.reverseRecOn generalizing o s u h q with
  | nil => cases hm
  | append_singleton xs x ih =>
    obtain ⟨m, y, hm₀, hs⟩ := (Program.after_snoc_eq_some _ _ _ _ _).mp hm
    rcases Program.step_cases _ hs with ⟨s', o', u', rfl, rfl, he⟩ |
      ⟨o', s', u', h', q', v, rfl, rfl, he⟩
    · -- A new outside input stores that input and issues its request with no earlier reply.
      simp only [Program.emit, routingProgram, List.map_nil, routingCall, Sum.map_inr,
        id_eq] at he
      cases he
      exact ⟨rfl, rfl, by simp only [List.reverse_append, List.reverse_singleton,
        List.singleton_append, currentCall]⟩
    · -- The first inside reply finishes the invocation, so it cannot leave a pending call.
      obtain ⟨rfl, -, -⟩ := ih hm₀
      simp only [List.nil_append, Program.emit, routingProgram, List.map_cons,
        List.map_nil, routingCall, Sum.map_inl] at he
      cases he

/-- Every reply of the routing program is a reply of the original complete-history rule.
Only the pending-mode invariant is needed to recover the retained outside input. -/
lemma routingProgram_mem_callRule
    -- `xs` is the complete history and `hy` asserts that the program emits `y` there.
    (xs : List (Σ l, twoFam U Y l)) (y : Σ l, twoFam V X l)
    (hy : y ∈ DDC.ofProgram () (routingProgram request answer) xs) :
    y ∈ callRule (routingCall request answer) xs := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs, x, rfl⟩
  · exact False.elim (Part.notMem_none _ hy)
  rw [List.concat_eq_append] at hy ⊢
  obtain ⟨m, m', hm, hs⟩ := (DDC.mem_ofProgram_snoc _ _ _ _ _).mp hy
  rcases Program.step_cases _ hs with ⟨s, o, u, rfl, rfl, he⟩ |
    ⟨o, s, u, h, q, v, rfl, rfl, he⟩
  · -- On an outside input, both presentations issue the request immediately.
    simp only [Program.emit, routingProgram, List.map_nil, routingCall, Sum.map_inr,
      id_eq] at he
    cases he
    simp only [callRule, List.reverse_append, List.reverse_singleton,
      List.singleton_append, currentCall, routingCall, Part.mem_some_iff]
  · -- On its inside reply, both recover the same retained input and translate the answer.
    obtain ⟨rfl, rfl, hc⟩ := routingProgram_pending request answer xs hm
    simp only [List.nil_append, Program.emit, routingProgram, List.map_cons,
      List.map_nil, routingCall, Sum.map_inl] at he
    cases he
    simp only [callRule, List.reverse_append, List.reverse_singleton,
      List.singleton_append, currentCall, currentCall_acc _ [⟨_, v⟩], hc,
      Option.map_some, List.nil_append, routingCall, Part.mem_some_iff]

/-- The program and canonical direct-call presentations are equal as complete-history DDCs. -/
lemma routingProgram_eq_canon_callRule :
    DDC.ofProgram () (routingProgram request answer) =
      canon (callRule (routingCall request answer)) := by
  have hp := DDC.ofProgram_isResponsiveDDC (s := ()) (routingProgram_bounded request answer)
  -- Responsive canonical DDCs are determined by inclusion of their complete replies.
  apply hp.eq_of_replies_imp (routingCall_isResponsiveDDC request answer)
  intro xs ys hr
  have hl := hr.length
  have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by omega)
  have hy : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by omega)
  have hr' : Replies (DDC.ofProgram () (routingProgram request answer))
      ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) := by
    simpa only [hx, hy] using hr
  -- Program transcripts obey the converter schedule, so canonicalization retains them.
  have hc := (replies_canon_iff _ (by intro h; exact h) (xs.zip ys)).mpr
    ⟨hp.isDDC.admitted_of_replies hr',
      hr'.mono (routingProgram_mem_callRule request answer)⟩
  simpa only [hx, hy] using hc

/-- The same outside-history filter on the equal presentations gives the existing router. -/
lemma routingConverter_eq_ofProgramOn
    -- `F` selects outside input histories in both presentations.
    (F : List (Σ o, U o) → Prop) :
    routingConverter request answer F = DDC.ofProgramOn () (routingProgram request answer) F := by
  unfold routingConverter callConverter DDC.ofProgramOn
  rw [routingProgram_eq_canon_callRule]

end SystemAlgebra
