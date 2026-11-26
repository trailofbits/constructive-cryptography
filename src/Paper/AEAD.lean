/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Paper.Register
import Informalization.Paper.Archetypes
import Examples.AuthenticatedEncryption.Security
import Examples.Games

/-!
# Benchmark B3: Authenticated Encryption from IND-CCA and INT-PTXT (Register B: `constructive`)

Formalizes Banfi's Constructive Cryptography treatment of authenticated encryption
(Banfi 2023, §2.3.4, Lemma 2.3.9 and corrected Theorem 2.3.10):
* `aead_hybrid_distance_le`: explicitly simplified distance bound
  $2(\Delta(\mathbf{E}_{\mathsf{AE}}, \mathsf{PTXT}\,\mathbf{E}_{\mathsf{AE}}) +
  \Delta(\mathbf{E}_{\mathsf{AE}}, \mathsf{CCA}\,\mathbf{E}_{\mathsf{AE}})) +
  q(\mathrm{enc})^2 / |\mathcal{M}|$, proved via a two-round filter substitution chain and
  Banfi's four-case plaintext-collision birthday bound;
* `aead_of_ind_cca_int_ptxt`: deriving $\mathsf{AE}\text{-}\mathsf{Sec}$ within
  $2(\varepsilon_{\mathsf{ptxt}} + \varepsilon_{\mathsf{cca}}) + q(\mathrm{enc})^2 / |\mathcal{M}|$
  from $\mathsf{INT}\text{-}\mathsf{PTXT}$ and $\mathsf{IND}\text{-}\mathsf{CCA}$.
-/

namespace Paper.AEAD

open CategoryTheory
open Commons ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra SystemAlgebra.Interface AuthenticatedEncryption
open scoped VerboseCC SystemAlgebra NNReal

noncomputable section

section

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
  [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]

/-- **AEAD Hybrid Distance Bound** (Banfi, Lemma 2.3.9, §2.3.4):
the real authenticated-encryption system $\mathbf{E}_{\mathsf{AE}}$ lies within
$2(\Delta(\mathbf{E}_{\mathsf{AE}}, \mathsf{PTXT}\,\mathbf{E}_{\mathsf{AE}}) +
\Delta(\mathbf{E}_{\mathsf{AE}}, \mathsf{CCA}\,\mathbf{E}_{\mathsf{AE}})) +
q(\mathrm{enc})^2 / |\mathcal{M}|$ of the ideal system $\mathsf{Ideal}\,\mathbf{E}_{\mathsf{enc}}$. -/
lemma aead_hybrid_distance_le
    (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    Δ (AE.system.perPort scheme (budget := q))
      (AE.Ideal.perPort M C (budget := q) •
        Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) ≤
      2 * (Δ (AE.system.perPort scheme (budget := q)) (ρ^ptxt • AE.system.perPort scheme) +
           Δ (AE.system.perPort scheme (budget := q)) (ρ^cca • AE.system.perPort scheme)) +
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  With notation (AuthenticatedEncryption.Hybrid scheme q) as "\\mathbf{E}_{\\mathsf{hyb}}"
    explaining "the doubly filtered hybrid $\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}$"
  With notation (AE.Ideal.perPort M C (budget := q) •
    Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) as "\\mathbf{E}_{\\mathsf{ideal}}"
    explaining "the ideal authenticated-encryption system $\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}$"
  With notation (GameExamples.collision scheme q) as "\\hat{\\mathbf{G}}_{\\mathsf{coll}}"
    explaining "the AEAD plaintext-collision MBO game"
  proof_idea "We first pass from $\\mathbf{E}_{\\mathsf{AE}}$ to the doubly filtered hybrid $\\mathbf{E}_{\\mathsf{hyb}} = \\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}$ in two $\\mathsf{PTXT}$–$\\mathsf{CCA}$ rounds, and then apply Banfi's four-case plaintext-collision birthday bound against $\\mathbf{E}_{\\mathsf{ideal}}$."
  We claim hFilters :
      Δ (AE.system.perPort scheme (budget := q)) (AuthenticatedEncryption.Hybrid scheme q) ≤
        2 * (Δ (AE.system.perPort scheme (budget := q)) (ρ^ptxt • AE.system.perPort scheme) +
             Δ (AE.system.perPort scheme (budget := q)) (ρ^cca • AE.system.perPort scheme)) by
    We note hRound1 :
        Δ (AE.system.perPort scheme (budget := q))
          (ρ^ptxt • ρ^cca • AE.system.perPort scheme (budget := q)) ≤
          Δ (AE.system.perPort scheme (budget := q)) (ρ^ptxt • AE.system.perPort scheme) +
            Δ (AE.system.perPort scheme (budget := q)) (ρ^cca • AE.system.perPort scheme) by
      by_leaf "By the triangle inequality through $\\mathsf{PTXT}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)$ and non-expansion under $\\mathsf{PTXT}$, round one incurs loss at most $\\Delta(\\mathbf{E}_{\\mathsf{AE}}(\\Pi), \\mathsf{PTXT}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)) + \\Delta(\\mathbf{E}_{\\mathsf{AE}}(\\Pi), \\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi))$." {
        exact (distance_triangle _ (ρ^ptxt • AE.system.perPort scheme (budget := q)) _).trans
          (add_le_add le_rfl (distance_attach_le (ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q) _ _))
      }
    We note hRound2 :
        Δ (ρ^ptxt • ρ^cca • AE.system.perPort scheme (budget := q))
          (AuthenticatedEncryption.Hybrid scheme q) ≤
          Δ (AE.system.perPort scheme (budget := q)) (ρ^ptxt • AE.system.perPort scheme) +
            Δ (AE.system.perPort scheme (budget := q)) (ρ^cca • AE.system.perPort scheme) by
      by_leaf "Applying converter non-expansion through $\\mathsf{PTXT} \\circ \\mathsf{CCA}$ to round one yields the matching second-round bound." {
        exact ((distance_attach_le (ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q) _ _).trans
          (distance_attach_le (ρ^cca : AE.perPort M C q ⟶ AE.perPort M C q) _ _)).trans hRound1
      }
    by_leaf "Summing both filter rounds via the triangle inequality gives $2(\\Delta(\\mathbf{E}_{\\mathsf{AE}}(\\Pi), \\mathsf{PTXT}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)) + \\Delta(\\mathbf{E}_{\\mathsf{AE}}(\\Pi), \\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)))$." {
      exact (distance_triangle _ _ _).trans ((add_le_add hRound1 hRound2).trans_eq (two_mul _).symm)
    }
  We claim hBirthday :
      Δ (AuthenticatedEncryption.Hybrid scheme q)
        (AE.Ideal.perPort M C (budget := q) •
          Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) ≤
        ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) by
    We note hEquiv :
        DistinctionGames.ConditionallyEquivalent (GameExamples.collision scheme q)
          (AE.Ideal.perPort M C (budget := q) •
            Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) by
      by_leaf "Following Banfi's four-case query-equivalence analysis (2.4) until a plaintext collision occurs: (i) on an encryption query $m$, both $\\mathbf{E}_{\\mathsf{hyb}}$ and $\\mathbf{E}_{\\mathsf{ideal}}$ return the encryption of a fresh uniform dummy plaintext and log $(m, c)$; (ii) on a fresh decryption query $c$ absent from the log, $\\mathsf{Ideal}$ returns $\\bot$, and the outer $\\mathsf{PTXT}$ filter in $\\mathbf{E}_{\\mathsf{hyb}}$ likewise rejects unless inner decryption recovers a logged plaintext; (iii) on a replayed ciphertext $c$ from a logged pair $(m, c)$ with unique plaintext preimage $m$, both $\\mathsf{Ideal}$ and the outer $\\mathsf{PTXT}$ filter return $m$; and (iv) any discrepancy on fresh decryption forces a plaintext collision between the $q(\\mathrm{enc})$ original messages and the outer replacement plaintexts." {
        exact GameExamples.collision_conditionallyEquivalent scheme q
      }
    by_leaf "Each of the $q(\\mathrm{enc})$ encryption queries tests against at most $q(\\mathrm{enc})$ independent uniform replacement plaintexts in $\\mathcal{M}$, bounding the collision probability by $q(\\mathrm{enc})^2 / |\\mathcal{M}|$; by the MBO Difference Lemma, $\\Delta(\\mathbf{E}_{\\mathsf{hyb}}, \\mathbf{E}_{\\mathsf{ideal}}) \\le q(\\mathrm{enc})^2 / |\\mathcal{M}|$." {
      exact AuthenticatedEncryption.hybrid_ideal_distance_le scheme q
    }
  Conclude_triangle using [hFilters, hBirthday] by
    exact (distance_triangle _ (AuthenticatedEncryption.Hybrid scheme q) _).trans
      (add_le_add hFilters hBirthday)

/-- **Authenticated Encryption from IND-CCA and INT-PTXT** (Banfi, corrected Theorem 2.3.10):
if $\Pi$ satisfies $\mathsf{INT}\text{-}\mathsf{PTXT}$ within $\varepsilon_{\mathsf{ptxt}}$ and
$\mathsf{IND}\text{-}\mathsf{CCA}$ within $\varepsilon_{\mathsf{cca}}$, then $\Pi$ achieves
$\mathsf{AE}\text{-}\mathsf{Sec}$ within
$2(\varepsilon_{\mathsf{ptxt}} + \varepsilon_{\mathsf{cca}}) + q(\mathrm{enc})^2 / |\mathcal{M}|$. -/
theorem aead_of_ind_cca_int_ptxt
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ)
    (εptxt εcca : ENNReal)
    (ptxt : AE.INTPTXT scheme (q := q) (fun _ => εptxt))
    (cca : AE.INDCCA scheme (q := q) (fun _ => εcca))
    (closedPtxt : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher)
      (ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q))
    (closedCca : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher)
      (ρ^cca : AE.perPort M C q ⟶ AE.perPort M C q)) :
    AE.Secure scheme (q := q) fun _ =>
      2 * (εptxt + εcca) + ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) => εptxt) as "\\varepsilon_{\\mathsf{ptxt}}"
    explaining "the plaintext-integrity advantage bound"
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) => εcca) as "\\varepsilon_{\\mathsf{cca}}"
    explaining "the chosen-ciphertext advantage bound"
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) => εptxt + εcca)
    as "\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}}"
    explaining "the single-round filter substitution loss"
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) => 2 * (εptxt + εcca))
    as "2(\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}})"
    explaining "the two-round computational substitution loss"
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) =>
      ((q .enc) ^ 2 / Fintype.card M : ℝ≥0))
    as "q(\\mathrm{enc})^2 / |\\mathcal{M}|"
    explaining "the statistical plaintext-collision loss"
  With notation (fun _ : TypedDistinguisher (AE.perPort M C q) =>
      2 * (εptxt + εcca) + ((q .enc) ^ 2 / Fintype.card M : ℝ≥0))
    as "2(\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}}) + q(\\mathrm{enc})^2 / |\\mathcal{M}|"
    explaining "the total authenticated-encryption security error"
  With notation (AuthenticatedEncryption.Hybrid scheme q) as "\\mathbf{E}_{\\mathsf{hyb}}"
    explaining "the doubly filtered hybrid $\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}$"
  With notation (AE.Ideal.perPort M C (budget := q) •
    Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) as "\\mathbf{E}_{\\mathsf{ideal}}"
    explaining "the ideal authenticated-encryption system $\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}$"
  proof_idea "We replace $\\mathbf{E}_{\\mathsf{AE}}$ with the doubly filtered hybrid $\\mathbf{E}_{\\mathsf{hyb}}$ by applying $\\mathsf{INT}\\text{-}\\mathsf{PTXT}$ and $\\mathsf{IND}\\text{-}\\mathsf{CCA}$ twice under converter closure of $\\mathcal{D}$, and then replace $\\mathbf{E}_{\\mathsf{hyb}}$ with $\\mathbf{E}_{\\mathsf{ideal}}$ via the statistical collision bound."
  We claim hCompChain :
      (AE.system.perPort scheme (budget := q))
        ≃[fun _ => 2 * (εptxt + εcca)]
      (AuthenticatedEncryption.Hybrid scheme q) by {
    We note hRound1 :
        (AE.system.perPort scheme (budget := q))
          ≃[fun _ => εptxt + εcca]
        (ρ^ptxt • ρ^cca • AE.system.perPort scheme (budget := q)) by {
      by_leaf "Applying $\\mathsf{INT}\\text{-}\\mathsf{PTXT}$ directly and $\\mathsf{IND}\\text{-}\\mathsf{CCA}$ inside the closed filter $\\mathsf{PTXT}$ incurs loss $\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}}$." {
        have hPtxt :
            (AE.system.perPort scheme (budget := q))
              ≃[fun _ => εptxt]
            (ρ^ptxt • AE.system.perPort scheme (budget := q)) := ptxt
        exact DistinguisherAdvantage.SubstitutesWithin.trans _ hPtxt
          (AdmissibleDistinguishers.substitutesWithin_context
            (ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q) closedPtxt cca)
      }
    }
    We note hRound2 :
        (ρ^ptxt • ρ^cca • AE.system.perPort scheme (budget := q))
          ≃[fun _ => εptxt + εcca]
        (AuthenticatedEncryption.Hybrid scheme q) by {
      by_leaf "Repeating $\\mathsf{INT}\\text{-}\\mathsf{PTXT}$ inside $\\mathsf{PTXT} \\circ \\mathsf{CCA}$ and $\\mathsf{IND}\\text{-}\\mathsf{CCA}$ inside $\\mathsf{PTXT} \\circ \\mathsf{CCA} \\circ \\mathsf{PTXT}$ reaches $\\mathbf{E}_{\\mathsf{hyb}}$ with another $\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}}$." {
        have hPtxt :
            (AE.system.perPort scheme (budget := q))
              ≃[fun _ => εptxt]
            (ρ^ptxt • AE.system.perPort scheme (budget := q)) := ptxt
        have hCca :
            (AE.system.perPort scheme (budget := q))
              ≃[fun _ => εcca]
            (ρ^cca • AE.system.perPort scheme (budget := q)) := cca
        have h3 :
            (ρ^ptxt • ρ^cca • AE.system.perPort scheme (budget := q))
              ≃[fun _ => εptxt]
            (ρ^ptxt • ρ^cca • ρ^ptxt • AE.system.perPort scheme (budget := q)) := by
          simpa only [comp_smul] using AdmissibleDistinguishers.substitutesWithin_context
            (ρ^ptxt ≫ ρ^cca : AE.perPort M C q ⟶ AE.perPort M C q)
            (closedPtxt.comp closedCca) hPtxt
        have h4 :
            (ρ^ptxt • ρ^cca • ρ^ptxt • AE.system.perPort scheme (budget := q))
              ≃[fun _ => εcca]
            (AuthenticatedEncryption.Hybrid scheme q) := by
          simpa only [comp_smul, AuthenticatedEncryption.Hybrid] using
            AdmissibleDistinguishers.substitutesWithin_context
              (ρ^ptxt ≫ ρ^cca ≫ ρ^ptxt : AE.perPort M C q ⟶ AE.perPort M C q)
              (closedPtxt.comp (closedCca.comp closedPtxt)) hCca
        exact DistinguisherAdvantage.SubstitutesWithin.trans _ h3 h4
      }
    }
    by_leaf "Chaining both filter-substitution rounds yields a total computational error of $2(\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}})$." {
      have hBoth := DistinguisherAdvantage.SubstitutesWithin.trans _ hRound1 hRound2
      intro D hD
      exact (hBoth D hD).trans_eq (by rw [two_mul])
    }
  }
  We claim hStatStep :
      (AuthenticatedEncryption.Hybrid scheme q)
        ≃[fun _ => ((q .enc) ^ 2 / Fintype.card M : ℝ≥0)]
      (AE.Ideal.perPort M C (budget := q) •
        Encryption.system.perPort scheme (budget := AE.Ideal.insideBudget M C q)) by {
    by_leaf "Every admissible distinguisher's advantage between $\\mathbf{E}_{\\mathsf{hyb}}$ and $\\mathbf{E}_{\\mathsf{ideal}}$ is bounded by the statistical distance $\\Delta(\\mathbf{E}_{\\mathsf{hyb}}, \\mathbf{E}_{\\mathsf{ideal}}) \\le q(\\mathrm{enc})^2 / |\\mathcal{M}|$." {
      intro D _
      change D.advantage _ _ ≤ _
      exact (D.advantage_le_transcriptDistance _ _).trans
        ((SystemAlgebra.Interface.cc_distance_eq _ _).symm.le.trans
          (AuthenticatedEncryption.hybrid_ideal_distance_le scheme q))
    }
  }
  cc_substitute_step "composing the two-round filter substitutions with the statistical collision bound establishes $\\mathsf{AE}\\text{-}\\mathsf{Sec}$ within $2(\\varepsilon_{\\mathsf{ptxt}} + \\varepsilon_{\\mathsf{cca}}) + q(\\mathrm{enc})^2 / |\\mathcal{M}|$" {
    exact DistinguisherAdvantage.SubstitutesWithin.trans _ hCompChain hStatStep
  }

end

end

paper_register_ns Paper.AEAD constructive

paper_motivation Paper.AEAD
  "Following Banfi (§2.3.4), we derive authenticated encryption ($\\mathsf{AE}\\text{-}\\mathsf{Sec}$) from plaintext integrity ($\\mathsf{INT}\\text{-}\\mathsf{PTXT}$) and chosen-ciphertext security ($\\mathsf{IND}\\text{-}\\mathsf{CCA}$) via a corrected four-step filter hybrid and a plaintext-collision birthday bound."
  (title := "Authenticated Encryption from IND-CCA and INT-PTXT")

paper_setting_ns Paper.AEAD
  "Fix a symmetric-key encryption scheme $\\Pi$ over finite key space $\\mathcal{K}$, nonempty message space $\\mathcal{M}$, and ciphertext space $\\mathcal{C}$, together with a query budget $q$ allowing $q(\\mathrm{enc})$ encryption queries on the $\\mathsf{AE}(\\mathcal{M}, \\mathcal{C}, q)$ interface, and an admissible distinguisher class $\\mathcal{D}$ closed under composition with the $\\mathsf{PTXT}$ and $\\mathsf{CCA}$ filters."
  (suppress := ["K", "M", "C", "scheme", "q"])
  (suppress_preds := [ConstructiveCryptography.AdmissibleDistinguishers.ClosedUnder])
  (anchor := aead_hybrid_distance_le)
  (title := "Authenticated Encryption from IND-CCA and INT-PTXT")
  (register := constructive)

paper_construction aead_hybrid_distance_le "Filters" "AEAD Security Filter and Wrapper Converters"
  "The filters $\\mathsf{PTXT}$ and $\\mathsf{CCA}$ modify decryption and encryption independently, whereas $\\mathsf{Ideal}$ implements an ideal authenticated channel atop encryption alone."
  (lines := [
    "$\\mathsf{PTXT}$: records encrypted plaintexts $m$ and rejects any decryption whose recovered plaintext was never queried",
    "$\\mathsf{CCA}$: replaces real encryption plaintexts with fresh uniform dummy messages and decrypts recorded ciphertexts by table lookup",
    "$\\mathsf{Ideal}$: delegates encryption to $\\mathbf{E}_{\\mathsf{enc}}(\\Pi)$ on fresh dummy messages and answers decryption strictly from the recorded encryption log"
  ])

informal_symbol Commons.AE.Port "\\mathsf{Port}_{\\mathrm{AE}}"
informal_symbol Commons.AE.perPort "\\mathsf{AE}"
informal_symbol Commons.AE.system.perPort "\\mathbf{E}_{\\mathsf{AE}}"
informal_symbol Commons.Encryption.system.perPort "\\mathbf{E}_{\\mathsf{enc}}"
informal_symbol Commons.AE.PTXT.perPort "\\mathsf{PTXT}"
informal_hide_args Commons.AE.PTXT.perPort 0 1
informal_symbol Commons.AE.CCA.perPort "\\mathsf{CCA}"
informal_hide_args Commons.AE.CCA.perPort 0 1
informal_symbol Commons.AE.Ideal.perPort "\\mathsf{Ideal}"
informal_hide_args Commons.AE.Ideal.perPort 0 1
informal_symbol Commons.AE.Secure "\\mathsf{AE}\\text{-}\\mathsf{Sec}"
informal_symbol Commons.AE.INTPTXT "\\mathsf{INT}\\text{-}\\mathsf{PTXT}"
informal_symbol Commons.AE.INDCCA "\\mathsf{IND}\\text{-}\\mathsf{CCA}"

informal_title aead_hybrid_distance_le "AEAD Hybrid Distance Bound"
informal_kind aead_hybrid_distance_le "Lemma"
informal_binder aead_hybrid_distance_le "M" "\\mathcal{M}"
informal_binder aead_hybrid_distance_le "C" "\\mathcal{C}"
informal_binder aead_hybrid_distance_le "scheme" "\\Pi"

informal_title aead_of_ind_cca_int_ptxt "Authenticated Encryption from IND-CCA and INT-PTXT"
informal_kind aead_of_ind_cca_int_ptxt "Theorem"
informal_binder aead_of_ind_cca_int_ptxt "M" "\\mathcal{M}"
informal_binder aead_of_ind_cca_int_ptxt "C" "\\mathcal{C}"
informal_binder aead_of_ind_cca_int_ptxt "scheme" "\\Pi"
informal_binder aead_of_ind_cca_int_ptxt "εptxt" "\\varepsilon_{\\mathsf{ptxt}}"
informal_binder aead_of_ind_cca_int_ptxt "εcca" "\\varepsilon_{\\mathsf{cca}}"

end Paper.AEAD
