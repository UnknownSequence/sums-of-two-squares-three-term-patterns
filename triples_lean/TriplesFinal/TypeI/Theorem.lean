import TriplesFinal.TypeI.Defs
import TriplesFinal.Assumptions.Assumptions
import TriplesFinal.TypeIProof.Theorem61

/-!
# Theorem 6.1: the Type I estimate

Assume (H). For every `η > 0` there is `C(η)` such that
(a) `Ξ ≪ Δ^C(η) (qXH)^η X^(1/2) H^(1/4) (1 + X/(d H^(1/2)))^θ`;
(b) `Ξ ≪ Δ^C(η) (qXH)^η X^(1/2) H^(1/4) (1 + K/(d H^(1/2)))^θ`.
The implied constants depend only on `η` and on the constants `C_ν` of (H).

Part (a) uses the spectral hypothesis with Pascadi's inequality, part (b) only the
Deshouillers–Iwaniec inequalities. Both use the Bessel facts and the convolution property of
Selberg transforms (for the pre-trace inequality, Lemma 10.7).

The proof occupies §§8–12 of the paper: Poisson summation (Lemma 9.1), the Heegner–Poincaré
identity (Lemma 9.2), the spectral expansion (Lemma 10.1), the large sieve inequalities
(Lemmas 10.2–10.5), partial summation (Lemma 10.6), the Heegner side (Lemma 10.7, with the
pair count of Lemma 8.4), the Bessel transform (Lemmas 11.1–11.3) and the optimisation of
Lemma 12.1. The proof is assembled in `TypeIProof/Theorem61.lean` (`typeI_a_proof`,
`typeI_b_proof`); the per-`M` bounds are in `TypeIProof/FinalBound.lean`.

Paper: §6, Theorem 6.1; proof in §§8–12.
-/

namespace Triples

/-- **Theorem 6.1(a).** -/
theorem typeI_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesis θ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤
        C * Δ ^ c * (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
          (1 + X / (d * Real.sqrt H)) ^ θ :=
  typeI_a_proof hθ0 hθ hB hSC hS hη

/-- **Theorem 6.1(b).** -/
theorem typeI_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesisDI θ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤
        C * Δ ^ c * (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
          (1 + K / (d * Real.sqrt H)) ^ θ :=
  typeI_b_proof hθ0 hθ hB hSC hS hη

end Triples
