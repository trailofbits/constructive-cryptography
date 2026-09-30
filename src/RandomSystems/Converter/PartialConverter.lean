import RandomSystems.DDC.DDC
import RandomSystems.PDS.Filter

/-!
# Partial converters and filters

A DDC may have a restricted domain (CR18, Definition 3.8 and §3.4.3, printed
pp. 61–62); restricting it to a prefix-closed set of histories keeps it a DDC. A filter
is the identity restricted to a set of outside-query histories.

## Main definitions

* `outsideInputs h`: the outside queries among a converter's inputs
* `DDC.filter D`, `DDC.filterQueries q`, `DDC.filterCost cost q`: filters

## Main results

* `IsDDC.filterDom`: restriction keeps a DDC
* `IsDDC.converges_along`: attaching a DDC converges
-/

namespace SystemAlgebra

open Classical

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- A prefix-closed restriction changes no replies or query bound. -/
theorem IsDDC.filterDom {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsDDC b α) (D : List (Σ l, twoFam U Y l) → Prop)
    (hD : ∀ {p h}, p <+: h → p ≠ [] → D h → D p) :
    IsDDC b (filterDom D α) := by
  refine ⟨hα.dds.filterDom D hD, ?_, ?_, ?_⟩
  · intro h z hd
    obtain ⟨hd, ha⟩ := (filterDom_dom D α _).mp hd
    have he : SystemAlgebra.filterDom D α h = α h := by
      by_cases hn : h = []
      · subst hn
        exact (Part.eq_none_iff.mpr (fun _ hy => (hα.dds.filterDom D hD).1 hy.1)).trans
          (Part.eq_none_iff.mpr (fun _ hy => hα.dds.1 hy.1)).symm
      · exact if_pos (hD (List.prefix_append _ _) hn hd)
    simpa only [Admits, replyLabel, he] using hα.admits h z ha
  · intro h hd
    obtain ⟨hd, ha⟩ := (filterDom_dom D α h).mp hd
    exact (run_filterDom IsInside D hD α hd).le.trans (hα.bound h ha)
  · intro h y o hy ho
    exact hα.replies h y o ((filterDom_mem_iff D α h y).mp hy).2 ho

/-- Only the finite internal-query bound is needed for attachment to converge. -/
theorem IsDDC.converges_along {I : Type} {Xi Yi : I → Type}
    {ι : J → I} {α : InsideOutsideSystem O J U V (Xi ∘ ι) (Yi ∘ ι)} {b : ℕ}
    (hα : IsDDC b α) (R : InterfaceSystem I Xi Yi) :
    Converges (pair α R) (alongRoute ι) (alongInj ι) :=
  converges_pair (cyclesThrough_along ι) hα.bound

/-- Project a converter's input history to the outside queries. -/
noncomputable def outsideInputs (h : List (Σ l, twoFam U Y l)) : List (Σ o, U o) :=
  restrict none (h.map splitIn)

theorem outsideInputs_append (h e : List (Σ l, twoFam U Y l)) :
    outsideInputs (h ++ e) = outsideInputs h ++ outsideInputs e := by
  simp only [outsideInputs, List.map_append, restrict_append]

namespace DDC

/-- Forward admitted outside queries and their replies. Rejected histories
remain undefined; they are not answered with an error value. -/
noncomputable def filter (D : List (Σ j, X j) → Prop)
    (hD : ∀ {p h}, p <+: h → D h → D p) : DDC J J X Y X Y :=
  ⟨filterDom (fun h => D (outsideInputs h)) (idConverter J X Y), 1,
    (idConverter_isResponsiveDDC (J := J) (X := X) (Y := Y)).isDDC.filterDom _
      (fun {p h} hp _ hd => hD (by
        obtain ⟨e, rfl⟩ := hp
        exact ⟨outsideInputs e, (outsideInputs_append p e).symm⟩) hd)⟩

/-- The query filter is the one-query forwarding converter restricted by `q`. -/
noncomputable def filterQueries (q : ℕ) : DDC J J X Y X Y :=
  filter (fun h => h.length ≤ q) (fun hp hd => hp.length_le.trans hd)

/-- Input-dependent budgets include the total encoded-block budget used by CBC. -/
noncomputable def filterCost (cost : (Σ j, X j) → ℕ) (q : ℕ) : DDC J J X Y X Y :=
  filter (fun h => (h.map cost).sum ≤ q) (by
    rintro p h ⟨e, rfl⟩ hd
    simp only [List.map_append, List.sum_append] at hd
    omega)

end DDC

end SystemAlgebra
