import ConstructiveCryptography.InterfaceCoherence
import RandomSystems.Converter.ParallelPDS

/-!
# Presentations of parallel resources

The parallel composition of two resources presented by PDSs is presented by their parallel
composition `parallelPDS`. Attaching a renaming relabels a resource.

## Main results

* `Interface.parallel_mass_of_presentations`, `Interface.parallel_ofPDS`: parallel
  composition of presentations
* `Interface.rename_mass`: attaching a renaming relabels the transcripts
-/

namespace SystemAlgebra.Interface

open Classical Probability CategoryTheory

theorem parallel_mass_of_presentations {A B : Interface} {ι κ : Type}
    (R : Resource A) (S : Resource B) (P : Distribution ι) (Q : Distribution κ)
    (s : ι → InterfaceSystem A.I A.X A.Y) (t : κ → InterfaceSystem B.I B.X B.Y)
    (hR : ∀ h, R.1 h = P.mass (fun i => Replies (s i) (h.map Prod.fst) (h.map Prod.snd)))
    (hS : ∀ h, S.1 h = Q.mass (fun i => Replies (t i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ i, (tensor A B).X i) × (Σ i, (tensor A B).Y i))) :
    (parallel R S).1 h = (Distribution.prod P Q).mass (fun st =>
      Replies (relabel (trim (pair (s st.1) (t st.2)))
        (sumAlphabet (Sum.rec A.X B.X)).symm (sumAlphabet (Sum.rec A.Y B.Y)))
        (h.map Prod.fst) (h.map Prod.snd)) := by
  rw [parallel_mass, RandomSystem.parallel_mass_of_presentations _ _ P Q s t hR hS]
  apply Distribution.mass_congr
  intro st
  rw [replies_relabel_iff, replies_trim_iff]

theorem parallel_ofPDS {A B : Interface}
    (P : Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h})
    (Q : Distribution.ProbDist {t : InterfaceSystem B.I B.X B.Y //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ B.domain h}) :
    parallel (Resource.ofPDS P) (Resource.ofPDS Q) = Resource.ofPDS (parallelPDS P Q) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [parallel_mass_of_presentations _ _ P.1 Q.1 Subtype.val Subtype.val (fun _ => rfl)
    (fun _ => rfl)]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, parallelPDS, Distribution.mass_fTransform]

/-- A forwarding converter only renames the cumulative transcript. -/
theorem rename_mass {A B : Interface} (e : A.I ≃ B.I)
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h) (R : Resource B)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    ((rename e f g hf hg hd) • R : Resource A).1 h = R.1 (h.map (f.prodCongr g)) := by
  obtain ⟨r, hr, hre, hrle⟩ := exists_rename_eq_ofDDC e f g hf hg hd
  obtain ⟨Q, rfl⟩ := R.exists_ofPDS
  rw [hre, smul_val, PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix _ _ _
    ⟨Finsupp.single ⟨r, hr⟩ 1, Distribution.isProbDist_single _⟩ Q (fun _ => rfl) (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_left, Distribution.mass_fTransform]
  change _ = behaviorMass Q.1 _ _
  apply Distribution.mass_congr
  intro s
  refine (replies_iff_of_dom_iff (t := relabel s.1 f g.symm) (fun k => ?_) (fun xs ys hrr => ?_)
    _ _).trans ?_
  · rw [((hr.mapsDomain A.nonempty_prefix) s.1 s.2.1 s.2.2.1 s.2.2.2).2 k]
    exact ((s.2.2.2 _).trans (hd k)).symm
  · rw [← trim_apply_renameConverter e f g.symm hf (alphabet_symm_label e g hg) s.2.1 s.2.2.1,
      replies_trim_iff, apply_eq]
    rw [replies_trim_iff, apply_eq] at hrr
    exact hrr.interconnect_mono (pair_mono hrle (fun _ _ hy => hy))
  · rw [replies_relabel_iff]
    rfl

end SystemAlgebra.Interface
