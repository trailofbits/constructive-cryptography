/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Paper.Register
import Informalization.Paper.Archetypes
import Examples.PRGLengthExtension

/-!
# Benchmark B1: PRG Length Extension (Register B: `constructive`)

Formalizes the 2-wise sequential length extension of a pseudorandom generator
$G : S \to S \times S$ (Boneh--Shoup §3.4.2) in Constructive Cryptography (Register B),
deriving $\Delta(\mathbf{G}^{\mathrm{ext}}, \mathbf{U}_{S^3}) \le 2\varepsilon$ from a
single-call PRG bound $\Delta(\mathbf{G}_{q_1}, \mathbf{U}_{S^2}) \le \varepsilon$.
-/

namespace Paper.PRGLengthExtension

open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open Commons Probability SystemAlgebra SystemAlgebra.Interface Examples.PRGLengthExtension
open scoped VerboseCC SystemAlgebra NNReal

noncomputable section

/-- **PRG Length Extension** (Boneh--Shoup, Theorem 3.3 / §3.4.2):
iterating a length-doubling PRG $G : S \to S \times S$ twice produces a length-tripling
PRG $H(G)$ whose distinguishing advantage from uniform samples over $S^3$ is at most $2\varepsilon$. -/
theorem prg_length_extension
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (G : S → S × S) (q : Commons.Evaluation.Port → ℕ) (ε : ENNReal)
    (hG : Δ (PRGReal.perPort G (budget := 𝓡₁.insideBudget G q))
            (MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₁.insideBudget G q)) ≤ ε) :
    Δ (PRGReal.perPort (H G) (budget := q))
      (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q)) ≤ 2 * ε := by
  With notation (PRGReal.perPort (H G) (budget := q)) as "\\mathbf{G}^{\\mathrm{ext}}"
    explaining "the extended PRG system evaluating $H(G)$ on fresh uniform seeds"
  With notation (PRGReal.perPort G (budget := 𝓡₁.insideBudget G q)) as "\\mathbf{G}_{q_1}"
    explaining "the base PRG system under the first-call inner query budget $q_1$"
  With notation (PRGReal.perPort G (budget := 𝓡₂.insideBudget S q)) as "\\mathbf{G}_{q_2}"
    explaining "the base PRG system under the second-call inner query budget $q_2$"
  With notation (MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₁.insideBudget G q)) as "\\mathbf{U}_{S^2, q_1}"
    explaining "the uniform pair beacon over $S^2$ under budget $q_1$"
  With notation (MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₂.insideBudget S q)) as "\\mathbf{U}_{S^2, q_2}"
    explaining "the uniform pair beacon over $S^2$ under budget $q_2$"
  With notation (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q)) as "\\mathbf{U}_{S^3}"
    explaining "the uniform triple beacon over $S^3$ under query budget $q$"
  With notation (𝓡₁.perPort G (budget := q)) as "\\rho_1"
    explaining "the converter answering $\\mathrm{eval}()$ with $(a, G(b))$ from an inner pair $(a, b)$"
  With notation (𝓡₂.perPort S (budget := q)) as "\\rho_2"
    explaining "the converter sampling uniform $a \\leftarrow \\mathcal{U}(S)$ beside an inner pair $(c, d)$"
  proof_idea "We interpolate between $\\mathbf{G}^{\\mathrm{ext}}$ and $\\mathbf{U}_{S^3}$ via an intermediate hybrid $M_1 = \\rho_1 \\mathbf{U}_{S^2, q_1} = \\rho_2 \\mathbf{G}_{q_2}$, factor out each call of $G$ through $\\rho_1$ and $\\rho_2$ using converter non-expansion, and conclude by the triangle inequality."
  Define_hybrid M₁ :=
    𝓡₁.perPort G (budget := q) •
      MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₁.insideBudget G q)
    because "which simulates the outer call of $H(G)$ using uniform pairs $(a, b) \\leftarrow \\mathcal{U}(S^2)$ while evaluating $G(b)$ on the second coordinate"
  We claim hHop1 :
      Δ (PRGReal.perPort (H G) (budget := q)) M₁ ≤ ε
      explaining "by factoring out the first call of $G$ through $\\rho_1$ and applying converter non-expansion" by
    We note hFactor1 :
        PRGReal.perPort (H G) (budget := q) =
          𝓡₁.perPort G (budget := q) • PRGReal.perPort G (budget := 𝓡₁.insideBudget G q) by
      by_leaf "Each query to $\\mathbf{G}^{\\mathrm{ext}}$ draws a fresh seed $s$, computes $(a, b) \\leftarrow G(s)$, and feeds $b$ to a second call $G(b)$, giving $\\mathbf{G}^{\\mathrm{ext}} = \\rho_1 \\mathbf{G}_{q_1}$." {
        exact prgReal_H_eq G q
      }
    by_leaf "Since attaching converter $\\rho_1$ is non-expanding with respect to $\\Delta$, we obtain $\\Delta(\\rho_1 \\mathbf{G}_{q_1}, \\rho_1 \\mathbf{U}_{S^2, q_1}) \\le \\Delta(\\mathbf{G}_{q_1}, \\mathbf{U}_{S^2, q_1}) \\le \\varepsilon$; rewriting the left system via $\\mathbf{G}^{\\mathrm{ext}} = \\rho_1 \\mathbf{G}_{q_1}$ yields $\\Delta(\\mathbf{G}^{\\mathrm{ext}}, M_1) \\le \\varepsilon$." {
      have hAttach1 :
          Δ (𝓡₁.perPort G (budget := q) • PRGReal.perPort G (budget := 𝓡₁.insideBudget G q)) M₁ ≤ ε :=
        (distance_attach_le (𝓡₁.perPort G (budget := q)) _ _).trans hG
      simpa only [hFactor1] using hAttach1
    }
  We claim hHop2 :
      Δ M₁ (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q)) ≤ ε
      explaining "by re-factoring $M_1 = \\rho_2 \\mathbf{G}_{q_2}$, replacing the second call by $\\mathbf{U}_{S^2, q_2}$, and lifting to $\\mathbf{U}_{S^3}$" by
    We note hMidEq :
        M₁ = 𝓡₂.perPort S (budget := q) • PRGReal.perPort G (budget := 𝓡₂.insideBudget S q) by
      by_leaf "Drawing uniform $(a, b)$ and applying $(a, G(b))$ coincides with drawing independent uniform $a$ alongside a single call to $G$, so $M_1 = \\rho_2 \\mathbf{G}_{q_2}$." {
        exact 𝓡₁_smul_prgRand G q
      }
    We note hTargetEq :
        𝓡₂.perPort S (budget := q) •
            MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₂.insideBudget S q) =
          MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q) by
      by_leaf "Prepending an independent uniform sample $a \\leftarrow \\mathcal{U}(S)$ to a uniform pair $(c, d) \\leftarrow \\mathcal{U}(S^2)$ via $\\rho_2$ yields the uniform triple beacon $\\rho_2 \\mathbf{U}_{S^2, q_2} = \\mathbf{U}_{S^3}$." {
        exact 𝓡₂_smul_prgRand q
      }
    by_leaf "Both inner query budgets agree ($q_2 = q_1$); by non-expansion of $\\rho_2$ and the base PRG assumption, $\\Delta(\\rho_2 \\mathbf{G}_{q_2}, \\rho_2 \\mathbf{U}_{S^2, q_2}) \\le \\Delta(\\mathbf{G}_{q_2}, \\mathbf{U}_{S^2, q_2}) \\le \\varepsilon$, and substituting the middle and target identities yields $\\Delta(M_1, \\mathbf{U}_{S^3}) \\le \\varepsilon$." {
      have hAttach2 :
          Δ (𝓡₂.perPort S (budget := q) • PRGReal.perPort G (budget := 𝓡₂.insideBudget S q))
            (𝓡₂.perPort S (budget := q) •
              MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := 𝓡₂.insideBudget S q)) ≤ ε :=
        (distance_attach_le (𝓡₂.perPort S (budget := q)) _ _).trans hG
      simpa only [hMidEq, hTargetEq] using hAttach2
    }
  Conclude_triangle using [hHop1, hHop2] by
    exact (distance_triangle _ M₁ _).trans ((add_le_add hHop1 hHop2).trans_eq (two_mul ε).symm)

end

paper_register_ns Paper.PRGLengthExtension constructive

paper_motivation Paper.PRGLengthExtension
  "We prove Boneh–Shoup's sequential length-extension theorem in the constructive framework: iterating a length-doubling generator $G : S \\to S \\times S$ twice yields a length-tripling generator $H(G)$ whose distinguishing advantage from uniform samples on $S^3$ is at most $2\\varepsilon$."
  (title := "Length Extension of a Pseudorandom Generator")

paper_setting_ns Paper.PRGLengthExtension
  "Fix a finite nonempty seed alphabet $S$ and an evaluation query budget $q$. Write $\\mathbf{G}^{\\mathrm{ext}}$ for the extended generator $H(G)$ under budget $q$, $\\mathbf{U}_{S^3}$ for the uniform triple beacon over $S^3$ under budget $q$, and $\\mathbf{G}_{q_i}$ and $\\mathbf{U}_{S^2, q_i}$ ($i \\in \\{1, 2\\}$) for the single-call PRG system and uniform pair beacon over $S^2$ under the first- and second-call inner budgets, which satisfy $q_1 = q_2$."
  (suppress := ["S", "q"])
  (anchor := prg_length_extension)
  (title := "PRG Length Extension")
  (register := constructive)

paper_construction prg_length_extension "Construction" "Extended Generator H(G) and Factoring Converters"
  "The length-tripling map $H(G)$ chains two calls to $G$, while converters $\\rho_1$ and $\\rho_2$ isolate the first and second calls respectively."
  (lines := [
    "$H(G)(s) : (a, b) \\leftarrow G(s);\\; (c, d) \\leftarrow G(b);\\; \\mathrm{return}\\;(a, c, d)$",
    "$\\rho_1$: given inner pair $(a, b)$, return $(a, G(b))$",
    "$\\rho_2$: sample fresh $a \\leftarrow \\mathcal{U}(S)$, query inner pair $(c, d)$, and return $(a, c, d)$"
  ])

informal_title prg_length_extension "Length Extension of a Pseudorandom Generator"
informal_kind prg_length_extension "Theorem"
informal_binder prg_length_extension "G" "G"
informal_binder prg_length_extension "ε" "\\varepsilon"

end Paper.PRGLengthExtension
