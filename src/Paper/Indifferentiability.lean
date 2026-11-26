/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Paper.Register
import Informalization.Paper.Archetypes
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import Commons.Definitions.Indifferentiability

/-!
# Benchmark B4: Indifferentiability Composition (Register B: `constructive`)

Formalizes Maurer--Renner 2016 (Lemma 5 and composition Theorems 1--2 / Jost §4.2):
* `constructs_of_simulator_witness`: simulator witness lemma
  $(\exists \sigma \in \Sigma : \pi \mathbf{R} \approx^{\varepsilon} \mathbf{S}\sigma)
  \implies \mathbf{R} \xrightarrow{\pi} (\mathbf{S}^*)^{\varepsilon}$;
* `serial_indifferentiability_composition`: composing an indifferentiable realization with an
  honest-interface step and composite $P$-interface simulator $\sigma = \sigma_1 \circ \sigma_2$;
* `mixed_honest_application`: keyed/mixed honest applications sharing a single $P$-interface
  simulator, defining the intermediate hybrid system $\mathbf{M}$ explicitly.
-/

namespace Paper.Indifferentiability

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped VerboseCC SystemAlgebra

noncomputable section

/-- Predicate recording that a composite simulator class $\Sigma$ contains all sequential
composites of simulators from $\Sigma_1$ and $\Sigma_2$. -/
def SimCompClosed {C : Type*} [Category C] {P Q Q' : C}
    (Sims₁ : Set (P ⟶ Q)) (Sims₂ : Set (Q ⟶ Q')) (Sims : Set (P ⟶ Q')) : Prop :=
  ∀ σ₁ ∈ Sims₁, ∀ σ₂ ∈ Sims₂, σ₁ ≫ σ₂ ∈ Sims

/-- Predicate recording that simulator attachment commutes with a family-mixing operator and
that the outer mixer preserves pointwise distinguishing bounds. -/
def KeyedMixerLaws {C : Type*} [Category C] [MonoidalCategory C]
    {Phi : C → Type*} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    {H' P Q : C} {K : Type*}
    (M_out : (K → Phi (H' ⊗ P)) → Phi (H' ⊗ P))
    (M_id : (K → Phi (H' ⊗ Q)) → Phi (H' ⊗ Q))
    (σ : P ⟶ Q) (ε₁ : ENNReal) : Prop :=
  (∀ f : K → Phi (H' ⊗ Q),
    (H' ◁ σ) • M_id f = M_out (fun k => (H' ◁ σ) • f k)) ∧
  (∀ a b : K → Phi (H' ⊗ P),
    (∀ k, Δ (a k) (b k) ≤ ε₁) → Δ (M_out a) (M_out b) ≤ ε₁)

/-- **Simulator Witness Lemma** (Maurer--Renner 2016, Lemma 5):
if an admitted simulator $\sigma \in \Sigma$ attached at the $P$-interface satisfies
$\Delta(\pi \mathbf{R}, (H \triangleleft \sigma)\mathbf{S}) \le \varepsilon$, then
$\pi$ constructs the relaxed simulator specification $(\mathbf{S}^*)^\varepsilon$ from $\mathbf{R}$. -/
lemma constructs_of_simulator_witness
    {C : Type*} [Category C] [MonoidalCategory C]
    {Phi : C → Type*} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    {H P Q B : C} {Sims : Set (P ⟶ Q)} {R : Phi B} {S : Phi (H ⊗ Q)}
    (π : H ⊗ P ⟶ B) (σ : P ⟶ Q) (ε : ENNReal)
    (hσ : σ ∈ Sims)
    (hClose : Δ (π • R) ((H ◁ σ) • S) ≤ ε) :
    ({R} : Specification (Phi B)) —[π]→
      Specification.epsilonRelaxation ε
        (Specification.simulatorImage Sims ({S} : Specification (Phi (H ⊗ Q)))) := by
  proof_idea "Since $\\sigma \\in \\Sigma$, the simulated system $(H \\triangleleft \\sigma)\\mathbf{S}$ belongs to $\\mathbf{S}^*$, and the assumed $\\Delta$-bound places $\\pi \\mathbf{R}$ in $(\\mathbf{S}^*)^{\\varepsilon}$."
  We claim hInStar :
      ((H ◁ σ) • S) ∈ Specification.simulatorImage Sims ({S} : Specification (Phi (H ⊗ Q)))
      explaining "since $\\sigma \\in \\Sigma$ attaches at the $P$-interface" by
    by_leaf "Because $\\sigma \\in \\Sigma$ is an admitted simulator and $\\mathbf{S}$ belongs to the singleton ideal specification $\\{\\mathbf{S}\\}$, attaching $\\sigma$ at the adversarial $P$-interface via $H \\triangleleft \\sigma$ places $(H \\triangleleft \\sigma)\\mathbf{S}$ inside the simulator image $\\mathbf{S}^*$." {
      rw [Specification.simulatorImage_eq_image2]
      exact ⟨σ, hσ, S, Set.mem_singleton S, rfl⟩
    }
  by_leaf "Combining $(H \\triangleleft \\sigma)\\mathbf{S} \\in \\mathbf{S}^*$ with the distance bound $\\Delta(\\pi\\mathbf{R}, (H \\triangleleft \\sigma)\\mathbf{S}) \\le \\varepsilon$ places $\\pi\\mathbf{R}$ in the $\\varepsilon$-relaxation ball $(\\mathbf{S}^*)^{\\varepsilon}$, establishing $\\mathbf{R} \\xrightarrow{\\pi} (\\mathbf{S}^*)^{\\varepsilon}$." {
    let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) (H ⊗ P)
    rintro _ rfl
    exact ConstructiveCryptography.CryptographicAlgebra.Specification.mem_epsilonRelaxation_iff.mpr
      ⟨(H ◁ σ) • S, hInStar, hClose⟩
  }

/-- **Serial Composition under Indifferentiability** (Maurer--Renner 2016, Theorem 2 / Lemmas 1--3):
composing an indifferentiable realization $\pi_1$ (with simulator $\sigma_1 \in \Sigma_1$) and an
honest-interface step $\pi_2$ (with simulator $\sigma_2 \in \Sigma_2$) yields a construction of
$(\mathbf{T}^*)^{\varepsilon_1 + \varepsilon_2}$ witnessed by the composite simulator
$\sigma = \sigma_1 \circ \sigma_2$ attached at the $P$-interface. -/
theorem serial_indifferentiability_composition
    {C : Type*} [Category C] [MonoidalCategory C]
    {Phi : C → Type*} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    {H H' P Q Q' B : C}
    {Sims₁ : Set (P ⟶ Q)} {Sims₂ : Set (Q ⟶ Q')} {Sims : Set (P ⟶ Q')}
    {R : Phi B} {S : Phi (H ⊗ Q)} {T : Phi (H' ⊗ Q')}
    (π₁ : H ⊗ P ⟶ B) (π₂ : H' ⟶ H)
    (σ₁ : P ⟶ Q) (σ₂ : Q ⟶ Q')
    {ε₁ ε₂ : ENNReal}
    (hClosed : SimCompClosed Sims₁ Sims₂ Sims)
    (hσ₁ : σ₁ ∈ Sims₁) (hσ₂ : σ₂ ∈ Sims₂)
    (h₁ : Δ (π₁ • R) ((H ◁ σ₁) • S) ≤ ε₁)
    (h₂ : Δ ((π₂ ▷ Q) • S) ((H' ◁ σ₂) • T) ≤ ε₂) :
    ({R} : Specification (Phi B)) —[(π₂ ▷ P) ≫ π₁]→
      Specification.epsilonRelaxation (ε₁ + ε₂)
        (Specification.simulatorImage Sims ({T} : Specification (Phi (H' ⊗ Q')))) := by
  proof_idea "We exhibit the composite simulator $\\sigma = \\sigma_1 \\circ \\sigma_2 \\in \\Sigma$ on the adversarial $P$-interface, commute the honest application $\\pi_2$ past $\\sigma_1$ on disjoint ports, and invoke the simulator witness lemma with additive error $\\varepsilon_1 + \\varepsilon_2$."
  We claim hMem : σ₁ ≫ σ₂ ∈ Sims
      explaining "for the composite $P$-interface simulator $\\sigma = \\sigma_1 \\circ \\sigma_2$" by
    by_leaf "Closure of $\\Sigma$ under sequential composition places $\\sigma = \\sigma_1 \\circ \\sigma_2$ in $\\Sigma$." {
      exact hClosed σ₁ hσ₁ σ₂ hσ₂
    }
  We claim hDist :
      Δ (((π₂ ▷ P) ≫ π₁) • R) ((H' ◁ (σ₁ ≫ σ₂)) • T) ≤ ε₁ + ε₂
      explaining "by commuting $\\pi_2$ past $\\sigma_1$ on disjoint ports and applying non-expansion" by
    by_leaf "Monoidal interchange $(\\pi_2 \\triangleright P) \\circ (H \\triangleleft \\sigma_1) = (H' \\triangleleft \\sigma_1) \\circ (\\pi_2 \\triangleright Q)$ on disjoint ports, non-expansion under $\\pi_2 \\triangleright P$ and $H' \\triangleleft \\sigma_1$, and the triangle inequality yield distance at most $\\varepsilon_1 + \\varepsilon_2$." {
      have hComm1 : ((π₂ ▷ P) ≫ π₁) • R = (π₂ ▷ P) • (π₁ • R) :=
        attach_serial (π₂ ▷ P) π₁ R
      have hComm2 : (π₂ ▷ P) • ((H ◁ σ₁) • S) = (H' ◁ σ₁) • ((π₂ ▷ Q) • S) := by
        change attach (π₂ ▷ P) (attach (H ◁ σ₁) S) = attach (H' ◁ σ₁) (attach (π₂ ▷ Q) S)
        simp only [← attach_serial, whisker_exchange]
      have hComm3 : (H' ◁ (σ₁ ≫ σ₂)) • T = (H' ◁ σ₁) • ((H' ◁ σ₂) • T) := by
        change attach (H' ◁ (σ₁ ≫ σ₂)) T = attach (H' ◁ σ₁) (attach (H' ◁ σ₂) T)
        rw [whiskerLeft_comp, attach_serial]
      have hA : Δ ((π₂ ▷ P) • (π₁ • R)) ((π₂ ▷ P) • ((H ◁ σ₁) • S)) ≤ ε₁ :=
        (distance_attach_le (π₂ ▷ P) _ _).trans h₁
      have hB : Δ ((H' ◁ σ₁) • ((π₂ ▷ Q) • S)) ((H' ◁ σ₁) • ((H' ◁ σ₂) • T)) ≤ ε₂ :=
        (distance_attach_le (H' ◁ σ₁) _ _).trans h₂
      rw [hComm1, hComm3]
      refine (distance_triangle _ ((π₂ ▷ P) • ((H ◁ σ₁) • S)) _).trans (add_le_add hA ?_)
      rw [hComm2]
      exact hB
    }
  by_leaf "Applying the simulator witness lemma to $\\sigma = \\sigma_1 \\circ \\sigma_2$ on the $P$-interface concludes the serial composition." {
    exact constructs_of_simulator_witness ((π₂ ▷ P) ≫ π₁) (σ₁ ≫ σ₂) (ε₁ + ε₂)
      hMem hDist
  }

/-- **Mixed Honest Applications with a Common Simulator** (Maurer–Renner 2016 / §4.2):
a family of honest-port protocols $\kappa_k : H \to H'$ composed with an indifferentiable realization
$\pi_0$ under a commuting, advantage-preserving mixer admits a single shared $P$-interface simulator
$\sigma \in \Sigma$ across all family members within error $\varepsilon_1 + \varepsilon_2$. -/
theorem mixed_honest_application
    {C : Type*} [Category C] [MonoidalCategory C]
    {Phi : C → Type*} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    {H H' P Q B : C} {K : Type*}
    {Sims : Set (P ⟶ Q)} {R : Phi B} {S : Phi (H ⊗ Q)} {T : Phi (H' ⊗ Q)}
    {π₀ : H ⊗ P ⟶ B} {κ : K → (H' ⟶ H)}
    (M_out : (K → Phi (H' ⊗ P)) → Phi (H' ⊗ P))
    (M_id : (K → Phi (H' ⊗ Q)) → Phi (H' ⊗ Q))
    (σ : P ⟶ Q) (ε₁ ε₂ : ENNReal)
    (hσ : σ ∈ Sims)
    (hMix : KeyedMixerLaws M_out M_id σ ε₁)
    (hIndiff : Δ (π₀ • R) ((H ◁ σ) • S) ≤ ε₁)
    (hApp : Δ (M_id (fun k => (κ k ▷ Q) • S)) T ≤ ε₂) :
    M_out (fun k => ((κ k ▷ P) ≫ π₀) • R) ∈
      Specification.epsilonRelaxation (ε₁ + ε₂)
        (Specification.simulatorImage Sims ({T} : Specification (Phi (H' ⊗ Q)))) := by
  With notation (M_out (fun k => ((κ k ▷ P) ≫ π₀) • R))
    as "\\mathrm{Mix}_{\\mathrm{real}}(\\{\\kappa_k\\})"
    explaining "the mixed real system applying $\\kappa_k \\circ \\pi_0$ to $\\mathbf{R}$"
  With notation (M_id (fun k => (κ k ▷ Q) • S))
    as "\\mathrm{Mix}_{\\mathrm{id}}(\\{\\kappa_k\\})"
    explaining "the mixed ideal system applying $\\kappa_k$ to $\\mathbf{S}$"
  proof_idea "We introduce the intermediate mixed system $M$ applying each $\\kappa_k$ to the simulated ideal system $\\mathbf{S}\\sigma$, commute the fixed $P$-interface simulator $\\sigma$ past the mixer, and bound both hops by $\\varepsilon_1$ and $\\varepsilon_2$."
  Define_hybrid M :=
    M_out (fun k => (κ k ▷ P) • ((H ◁ σ) • S))
    because "which mixes the honest-port applications $\\kappa_k$ evaluated on the simulated ideal resource $\\mathbf{S}\\sigma = (H \\triangleleft \\sigma)\\mathbf{S}$"
  We claim hFirst :
      Δ (M_out (fun k => ((κ k ▷ P) ≫ π₀) • R)) M ≤ ε₁
      explaining "by factoring out each $\\kappa_k$, applying non-expansion, and preserving the uniform error across the mixer" by
    by_leaf "Each branch $((\\kappa_k \\triangleright P) \\circ \\pi_0)\\mathbf{R} = (\\kappa_k \\triangleright P)(\\pi_0\\mathbf{R})$ stays within $\\varepsilon_1$ of $(\\kappa_k \\triangleright P)(\\mathbf{S}\\sigma)$ by non-expansion of $\\kappa_k \\triangleright P$, and advantage preservation of the outer mixer preserves this bound." {
      have hSplit :
          (fun k => ((κ k ▷ P) ≫ π₀) • R) = fun k => (κ k ▷ P) • (π₀ • R) := by
        funext k
        exact attach_serial (κ k ▷ P) π₀ R
      rw [hSplit]
      exact hMix.2 _ _ fun k => (distance_attach_le (κ k ▷ P) _ _).trans hIndiff
    }
  We claim hSecond :
      Δ M ((H' ◁ σ) • T) ≤ ε₂
      explaining "by commuting the shared $P$-interface simulator $\\sigma$ outside the mixer and applying non-expansion" by
    We note hCommMix :
        M = (H' ◁ σ) • M_id (fun k => (κ k ▷ Q) • S) by
      by_leaf "Commuting $\\sigma$ past each disjoint honest-port converter $\\kappa_k$ and then outside the mixer identifies $M = \\mathrm{Mix}_{\\mathrm{id}}(\\{\\kappa_k\\})\\,\\sigma$." {
        dsimp only [M]
        rw [hMix.1]
        congr 1
        funext k
        change attach (κ k ▷ P) (attach (H ◁ σ) S) = attach (H' ◁ σ) (attach (κ k ▷ Q) S)
        simp only [← attach_serial, whisker_exchange]
      }
    by_leaf "Non-expansion of attaching $H' \\triangleleft \\sigma$ reduces the distance to the ideal mixed application bound $\\varepsilon_2$." {
      rw [hCommMix]
      exact (distance_attach_le (H' ◁ σ) _ _).trans hApp
    }
  by_leaf "Combining both bounds via the triangle inequality places the mixed real system within $\\varepsilon_1 + \\varepsilon_2$ of $\\mathbf{T}\\sigma \\in \\mathbf{T}^*$." {
    let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) (H' ⊗ P)
    refine ConstructiveCryptography.CryptographicAlgebra.Specification.mem_epsilonRelaxation_iff.mpr
      ⟨(H' ◁ σ) • T, ?_, ?_⟩
    · rw [Specification.simulatorImage_eq_image2]
      exact ⟨σ, hσ, T, Set.mem_singleton T, rfl⟩
    · exact (distance_triangle _ M _).trans (add_le_add hFirst hSecond)
  }

end

paper_register_ns Paper.Indifferentiability constructive

paper_motivation Paper.Indifferentiability
  "We formalize Maurer and Renner's constructive treatment of indifferentiability (TCC 2016, Lemma 5 and composition Theorems 1–2), showing how simulator witnesses lift to relaxed specifications and compose serially across honest-port applications and keyed families with all simulators attached at the adversarial $P$-interface."
  (title := "Indifferentiability and Serial Simulator Composition")

paper_setting_ns Paper.Indifferentiability
  "Fix a symmetric monoidal resource theory $(\\Phi, \\bullet, \\parallel)$ over interfaces $H, H', H'', P, Q, Q', B$ with compatible distance $\\Delta$, simulator classes $\\Sigma_1 \\subseteq (P \\to Q)$, $\\Sigma_2 \\subseteq (Q \\to Q')$, and composite class $\\Sigma \\subseteq (P \\to Q')$ closed under sequential composition, resources $\\mathbf{R}, \\mathbf{S}, \\mathbf{T}$, an inner protocol $\\pi_0 : B \\to H \\otimes P$, an indexed family of honest converters $\\{\\kappa_k : H \\to H'\\}_{k \\in K}$, and a commuting advantage-preserving mixer pair $(\\mathrm{Mix}_{\\mathrm{real}}, \\mathrm{Mix}_{\\mathrm{id}})$ over index domain $K$, writing $\\mathrm{Mix}_{\\mathrm{real}}(\\{\\kappa_k\\}) := \\mathrm{Mix}_{\\mathrm{real}}(k \\mapsto (\\kappa_k \\triangleright P)\\pi_0 \\mathbf{R})$, $\\mathrm{Mix}_{\\mathrm{id}}(\\{\\kappa_k\\}) := \\mathrm{Mix}_{\\mathrm{id}}(k \\mapsto (\\kappa_k \\triangleright Q)\\mathbf{S})$, and $\\mathrm{Mix}_{\\mathrm{real}}(\\{\\kappa_k\\,\\mathbf{S}\\sigma\\}) := \\mathrm{Mix}_{\\mathrm{real}}(k \\mapsto (\\kappa_k \\triangleright P)(\\mathbf{S}\\sigma))$. For any ideal resource $\\mathbf{S}$, simulator $\\sigma \\in \\Sigma$, and tolerance $\\varepsilon \\ge 0$, write $\\mathbf{S}\\sigma := (H \\triangleleft \\sigma)\\mathbf{S}$ for right-port simulator attachment, $\\mathbf{S}^* = \\{\\mathbf{S}\\sigma : \\sigma \\in \\Sigma\\}$ for the simulator image, and $\\mathcal{S}^{\\varepsilon}$ for the $\\Delta$-ball of radius $\\varepsilon$ around $\\mathcal{S}$."
  (suppress := ["C", "Phi", "H", "H'", "H''", "P", "Q", "Q'", "B", "K", "Sims", "Sims₁", "Sims₂", "R", "S", "T", "M_out", "M_id", "κ", "π₀"])
  (suppress_preds := [Paper.Indifferentiability.SimCompClosed, Paper.Indifferentiability.KeyedMixerLaws])
  (anchor := constructs_of_simulator_witness)
  (title := "Indifferentiability and Serial Simulator Composition")
  (register := constructive)

paper_construction constructs_of_simulator_witness "Definition" "Simulator Image and Statistical Relaxation"
  "Maurer–Renner (2016, §4.2) characterizes indifferentiability via right-port simulator attachment on the public/adversarial interface $P$."
  (lines := [
    "Simulator image specification: $\\mathbf{S}^* := \\{(H \\triangleleft \\sigma)\\mathbf{S} : \\sigma \\in \\Sigma\\}$",
    "Statistical $\\varepsilon$-relaxation: $\\mathcal{S}^{\\varepsilon} := \\{ \\mathbf{R} : \\exists \\mathbf{S}' \\in \\mathcal{S},\\; \\Delta(\\mathbf{R}, \\mathbf{S}') \\le \\varepsilon \\}$",
    "Composite $P$-interface simulator: $\\sigma := \\sigma_1 \\circ \\sigma_2 : P \\to Q'$ when $\\sigma_1 : P \\to Q$ and $\\sigma_2 : Q \\to Q'$"
  ])

informal_title constructs_of_simulator_witness "Construction from an Admitted Simulator Witness"
informal_kind constructs_of_simulator_witness "Lemma"
informal_binder constructs_of_simulator_witness "Sims" "\\Sigma"
informal_binder constructs_of_simulator_witness "π" "\\pi"
informal_binder constructs_of_simulator_witness "σ" "\\sigma"
informal_binder constructs_of_simulator_witness "ε" "\\varepsilon"
informal_binder constructs_of_simulator_witness "R" "\\mathbf{R}"
informal_binder constructs_of_simulator_witness "S" "\\mathbf{S}"

informal_title serial_indifferentiability_composition "Serial Composition under Indifferentiability"
informal_kind serial_indifferentiability_composition "Theorem"
informal_binder serial_indifferentiability_composition "Sims" "\\Sigma"
informal_binder serial_indifferentiability_composition "Sims₁" "\\Sigma_1"
informal_binder serial_indifferentiability_composition "Sims₂" "\\Sigma_2"
informal_binder serial_indifferentiability_composition "π₁" "\\pi_1"
informal_binder serial_indifferentiability_composition "π₂" "\\pi_2"
informal_binder serial_indifferentiability_composition "σ₁" "\\sigma_1"
informal_binder serial_indifferentiability_composition "σ₂" "\\sigma_2"
informal_binder serial_indifferentiability_composition "ε₁" "\\varepsilon_1"
informal_binder serial_indifferentiability_composition "ε₂" "\\varepsilon_2"
informal_binder serial_indifferentiability_composition "R" "\\mathbf{R}"
informal_binder serial_indifferentiability_composition "S" "\\mathbf{S}"
informal_binder serial_indifferentiability_composition "T" "\\mathbf{T}"

informal_title mixed_honest_application "Mixed Honest Applications with a Common Simulator"
informal_kind mixed_honest_application "Theorem"
informal_binder mixed_honest_application "Sims" "\\Sigma"
informal_binder mixed_honest_application "M_out" "\\mathrm{Mix}_{\\mathrm{real}}"
informal_binder mixed_honest_application "M_id" "\\mathrm{Mix}_{\\mathrm{id}}"
informal_binder mixed_honest_application "π₀" "\\pi_0"
informal_binder mixed_honest_application "κ" "\\kappa"
informal_binder mixed_honest_application "σ" "\\sigma"
informal_binder mixed_honest_application "ε₁" "\\varepsilon_1"
informal_binder mixed_honest_application "ε₂" "\\varepsilon_2"
informal_binder mixed_honest_application "R" "\\mathbf{R}"
informal_binder mixed_honest_application "S" "\\mathbf{S}"
informal_binder mixed_honest_application "T" "\\mathbf{T}"
informal_theorem_notation mixed_honest_application
  (M_out (fun k => ((κ k ▷ P) ≫ π₀) • R)) "\\mathrm{Mix}_{\\mathrm{real}}(\\{\\kappa_k\\})"
informal_theorem_notation mixed_honest_application
  (M_id (fun k => (κ k ▷ Q) • S)) "\\mathrm{Mix}_{\\mathrm{id}}(\\{\\kappa_k\\})"
informal_theorem_notation mixed_honest_application
  (M_out (fun k => (κ k ▷ P) • ((H ◁ σ) • S))) "\\mathrm{Mix}_{\\mathrm{real}}(\\{\\kappa_k\\,\\mathbf{S}\\sigma\\})"

end Paper.Indifferentiability
