import TriplesFinal.Assumptions.Assumptions

/-!
# Lemmas 10.2–10.4: the large sieve inequalities

Lemmas 10.2 ([DI, Theorem 2]), 10.3 ([DI, Theorem 5]) and 10.4 ([Pas, Theorem 2]) are part of
the spectral hypothesis (`SpectralData.LargeSieveDI2`, `LargeSieveDI5`, `LargeSievePascadi` in
`Assumptions.lean`). This file extracts them, with constants independent of the level.

Paper: §10.3, Lemmas 10.2, 10.3 and 10.4.
-/

namespace Triples

/-- **Lemmas 10.2–10.4** at every level, from `SpectralHypothesis θ`. -/
theorem large_sieve {θ : ℝ} (hS : SpectralHypothesis θ) :
    ∃ C : ℝ → ℝ, ∀ q : ℕ, 0 < q → ∃ D : SpectralData q, D.PoincareExpansion ∧ D.PreTrace ∧
      D.LargeSieveDI2 C ∧ D.LargeSieveDI5 C ∧ D.LargeSievePascadi C ∧ D.ExceptionalBound θ ∧
      D.EisensteinContinuous :=
  hS

/-- **Lemmas 10.2 and 10.3** at every level, from `SpectralHypothesisDI θ`. -/
theorem large_sieve_DI {θ : ℝ} (hS : SpectralHypothesisDI θ) :
    ∃ C : ℝ → ℝ, ∀ q : ℕ, 0 < q → ∃ D : SpectralData q, D.PoincareExpansion ∧ D.PreTrace ∧
      D.LargeSieveDI2 C ∧ D.LargeSieveDI5 C ∧ D.ExceptionalBound θ ∧ D.EisensteinContinuous :=
  hS

end Triples
