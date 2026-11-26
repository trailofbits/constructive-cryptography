module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Binomial counts of finite occupancies

For a count map `c : B →₀ ℕ` and `m > 0`, `c.chooseSum m` counts subsets of size `m`
contained in a single bin. `chooseSum_add_single` expresses one increment by Pascal's identity.
A bin with at least `m` entries contributes at least one, by `one_le_chooseSum_of_le`.

These laws supply the deterministic counting steps in adaptive occupancy bounds.
-/

@[expose] public section

namespace Finsupp

/-- `chooseSum c m = ∑ b ∈ c.support, choose(c b,m)` sums the within-bin coefficients. -/
noncomputable def chooseSum
    -- `B` is the bin carrier; `c b` counts entries in bin `b`, with only finitely many nonzero.
    {B : Type*} (c : B →₀ ℕ) (m : ℕ) : ℕ :=
  c.sum (fun _ n => n.choose m)

/-- Empty counts contain no subsets in any occupied bin. -/
@[simp] lemma chooseSum_zero {B : Type*} (m : ℕ) : (0 : B →₀ ℕ).chooseSum m = 0 :=
  rfl

/-- Adding one entry to bin `b` creates exactly `choose(c b,k)` new subsets of size `k+1`. -/
theorem chooseSum_add_single
    -- `c` is the finite count map; `b` receives the new entry and `k+1` is the subset size.
    {B : Type*} (c : B →₀ ℕ) (b : B) (k : ℕ) :
    (c + single b 1).chooseSum (k + 1) = c.chooseSum (k + 1) + (c b).choose k := by
  classical
  -- Split off bin `b`; erasing it leaves the same counts before and after the increment.
  unfold chooseSum
  rw [← add_sum_erase' (c + single b 1) b _ (fun _ => Nat.choose_zero_succ k),
    ← add_sum_erase' c b _ (fun _ => Nat.choose_zero_succ k),
    add_apply, single_eq_same, erase_add, erase_single, add_zero, Nat.choose_succ_succ]
  ac_rfl

/-- A bin with at least `m > 0` entries witnesses one within-bin subset of size `m`. -/
lemma one_le_chooseSum_of_le
    -- `c b` is the count in the witnessing bin; `m` is the positive subset size.
    {B : Type*} (c : B →₀ ℕ) {b : B} {m : ℕ} (positive : 0 < m) (occupied : m ≤ c b) :
    1 ≤ c.chooseSum m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  calc
    1 ≤ (c b).choose (k + 1) := Nat.choose_pos occupied
    _ ≤ (c b).choose (k + 1) + (c.erase b).chooseSum (k + 1) := Nat.le_add_right _ _
    _ = c.chooseSum (k + 1) :=
      add_sum_erase' c b (fun _ n => n.choose (k + 1)) (fun _ => Nat.choose_zero_succ k)

end Finsupp
