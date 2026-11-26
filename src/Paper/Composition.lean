/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Paper.Register
import Informalization.Paper.Archetypes
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.Notation.Basic

/-!
# Benchmark B2: Serial-Parallel Composition (Register B: `constructive`)

Formalizes the Constructive Cryptography serial-parallel composition theorem
(Maurer 2011, Theorem 1; Jost 2020, Corollary 2.2.13) in clean abstract single-letter
notation without ambient-category clutter.
-/

namespace Paper.Composition

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped VerboseCC SystemAlgebra

noncomputable section

/-- **Serial-Parallel Composition** (Maurer 2011, Theorem 1; Jost 2020, Corollary 2.2.13):
if converter $\pi'$ constructs $\mathbf{S}$ from $\mathbf{R}$ within error $\varepsilon_1$ and
outer protocol $\pi$ constructs $\mathbf{T}$ from $\mathbf{S} \parallel \mathbf{K}$ within error
$\varepsilon_2$, then $\pi \circ (\pi' \parallel \mathbf{1}_E)$ constructs $\mathbf{T}$ from
$\mathbf{R} \parallel \mathbf{K}$ within error $\varepsilon_1 + \varepsilon_2$. -/
theorem serial_parallel_composition
    {C : Type*} [Category C] [MonoidalCategory C]
    {Phi : C → Type*} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    {A B D E : C}
    {R : Phi D} {S : Phi B} {T : Phi A} {K : Phi E}
    (π' : B ⟶ D) (π : A ⟶ B ⊗ E) (ε₁ ε₂ : ENNReal)
    (h₁ : ({R} : Specification (Phi D)) —[π'; ε₁]→ ({S} : Specification (Phi B)))
    (h₂ : ({S ∥ K} : Specification (Phi (B ⊗ E))) —[π; ε₂]→ ({T} : Specification (Phi A))) :
    ({R ∥ K} : Specification (Phi (D ⊗ E))) —[π ≫ (π' ▷ E); ε₁ + ε₂]→
      ({T} : Specification (Phi A)) := by
  proof_idea "We first transport the inner construction $\\pi'$ past the independent parallel context $\\mathbf{K}$ by context-insensitivity, and then compose serially with the outer construction $\\pi$, adding the two error bounds."
  We claim hCtx :
      ({R ∥ K} : Specification (Phi (D ⊗ E))) —[π' ▷ E; ε₁]→
        ({S ∥ K} : Specification (Phi (B ⊗ E)))
      explaining "by parallel context-insensitivity with respect to $\\mathbf{K}$" by
    by_leaf "By parallel context-insensitivity, running the independent context resource $\\mathbf{K}$ alongside $\\pi'$ preserves the construction error $\\varepsilon_1$; identifying the singleton parallel specifications $\\{\\mathbf{R}\\} \\parallel \\{\\mathbf{K}\\} = \\{\\mathbf{R} \\parallel \\mathbf{K}\\}$ and $\\{\\mathbf{S}\\} \\parallel \\{\\mathbf{K}\\} = \\{\\mathbf{S} \\parallel \\mathbf{K}\\}$ together with $\\pi' \\otimes \\mathbf{1}_E = \\pi' \\triangleright E$ yields $\\{\\mathbf{R} \\parallel \\mathbf{K}\\} \\xrightarrow{\\pi' \\triangleright E,\\, \\varepsilon_1} \\{\\mathbf{S} \\parallel \\mathbf{K}\\}$." {
      have hPar :=
        ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context
          h₁ ({K} : Specification (Phi E))
      simpa only [ConstructiveCryptography.CryptographicAlgebra.Specification.parallel_singleton,
        CategoryTheory.MonoidalCategory.tensorHom_id] using hPar
    }
  cc_compose_step hCtx , h₂
    because "sequential composition with the outer converter $\\pi$, adding the two error bounds $\\varepsilon_1 + \\varepsilon_2$"

end

paper_register_ns Paper.Composition constructive

paper_motivation Paper.Composition
  "We establish the fundamental serial-parallel composition theorem of Constructive Cryptography (Maurer 2011, Theorem 1; Jost 2020, Corollary 2.2.13): constructions remain valid in parallel with an arbitrary context resource and compose sequentially with additive error."
  (title := "Serial-Parallel Composition of Constructions")

paper_setting_ns Paper.Composition
  "Fix a symmetric monoidal resource theory $(\\Phi, \\bullet, \\parallel)$ over interfaces $A, B, D, E$ equipped with a compatible pseudometric advantage $\\Delta$, together with resources $\\mathbf{R} \\in \\Phi(D)$, $\\mathbf{S} \\in \\Phi(B)$, $\\mathbf{T} \\in \\Phi(A)$, and an independent parallel context resource $\\mathbf{K} \\in \\Phi(E)$. Write $\\pi' \\triangleright E := \\pi' \\parallel \\mathbf{1}_E$ for extending a converter $\\pi'$ past the idle wire on interface $E$."
  (suppress := ["C", "Phi", "A", "B", "D", "E", "R", "S", "T", "K"])
  (anchor := serial_parallel_composition)
  (title := "Serial-Parallel Composition")
  (register := constructive)

paper_construction serial_parallel_composition "Axioms" "Context-Insensitivity and Serial Composition"
  "Composition combines two primitive closure principles of the constructive resource calculus."
  (lines := [
    "Parallel context-insensitivity: $\\{\\mathbf{R}\\} \\xrightarrow{\\pi',\\, \\varepsilon_1} \\{\\mathbf{S}\\} \\implies \\{\\mathbf{R} \\parallel \\mathbf{K}\\} \\xrightarrow{\\pi' \\triangleright E,\\, \\varepsilon_1} \\{\\mathbf{S} \\parallel \\mathbf{K}\\}$",
    "Serial transitivity: $\\{\\mathbf{X}\\} \\xrightarrow{\\alpha,\\, \\varepsilon_1} \\{\\mathbf{Y}\\}$ and $\\{\\mathbf{Y}\\} \\xrightarrow{\\beta,\\, \\varepsilon_2} \\{\\mathbf{Z}\\} \\implies \\{\\mathbf{X}\\} \\xrightarrow{\\beta \\circ \\alpha,\\, \\varepsilon_1 + \\varepsilon_2} \\{\\mathbf{Z}\\}$"
  ])

informal_title serial_parallel_composition "Serial-Parallel Composition Theorem"
informal_kind serial_parallel_composition "Theorem"
informal_binder serial_parallel_composition "π'" "\\pi'"
informal_binder serial_parallel_composition "π" "\\pi"
informal_binder serial_parallel_composition "ε₁" "\\varepsilon_1"
informal_binder serial_parallel_composition "ε₂" "\\varepsilon_2"
informal_binder serial_parallel_composition "R" "\\mathbf{R}"
informal_binder serial_parallel_composition "S" "\\mathbf{S}"
informal_binder serial_parallel_composition "T" "\\mathbf{T}"
informal_binder serial_parallel_composition "K" "\\mathbf{K}"

end Paper.Composition
