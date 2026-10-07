import TriplesFinal.TypeIProof.DiscreteFamily

/-!
# The discrete spectrum: the bound for `∑_j |B_j U_j|`

`spectral_side'` applied to the discrete family: `∑_j |B_j| |U_j|` converges and is bounded by
the explicit expression of `spectral_side'` with `P` the pair count of Lemma 10.7.

Paper: §§12.2–12.4 (the sums over `j`).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

/-- The index set of the discrete spectrum is countable. -/
theorem countable_ι : Countable D.ι := by
  have h : (Set.univ : Set D.ι) = ⋃ m : ℕ, {j | ‖D.t j‖ ≤ m} := by
    ext j
    simp only [mem_univ, mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨⌈‖D.t j‖⌉₊, Nat.le_ceil _⟩
  have hc : (Set.univ : Set D.ι).Countable := by
    rw [h]; exact Set.countable_iUnion fun m => (D.finite_le m).countable
  exact Set.countable_univ_iff.1 hc

/-- For the counting measure on the discrete spectrum, integrals are sums. -/
theorem integral_count_eq_tsum [MeasurableSpace D.ι] [DiscreteMeasurableSpace D.ι]
    (f : D.ι → ℝ) (hf : Integrable f Measure.count) :
    ∫ x, f x ∂Measure.count = ∑' j, f j := by
  have := D.countable_ι
  rw [integral_countable hf]
  congr 1
  funext j
  rw [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]

end SpectralData

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

set_option maxHeartbeats 1000000 in
/-- **The discrete spectrum**: `∑_j |B_j| |U_j|` converges and is bounded by the expression of
`spectral_side'` with `P = 𝒫` the pair count. -/
theorem discrete_side {q : ℕ} (D : SpectralData q) (hq : S.q = q) {n : ℕ} (z : Fin n → ℍ)
    (hB : BesselAssumptions) {Cls : ℝ → ℝ} (hDI2 : D.LargeSieveDI2 Cls) (hPT : D.PreTrace)
    (hSC : SelbergConvolution) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in (D.discFam z).exc,
      S.V ^ (2 * ((D.discFam z).t x).im) *
        ‖S.Ssum ψ₀ ((D.discFam z).ρ x) s σ‖ ^ 2 ∂(D.discFam z).ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck : ℝ} (hk : 3 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k)) :
    Summable (fun j => ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j)‖ * ‖∑ i, D.u j (z i)‖) ∧
      ∑' j, ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j)‖ * ‖∑ i, D.u j (z i)‖ ≤
        Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * (pairCountPts q z : ℝ)) +
        Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)) *
          Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * (pairCountPts q z : ℝ)) +
        Real.sqrt (S.Wtail Cls C6 CGt k Ck (pairCountPts q z : ℝ)) *
          (1 - Real.sqrt (1 / 2))⁻¹ := by
  have hLS : (D.discFam z).LS S.q Cls := by rw [hq]; exact D.discFam_LS z hDI2
  obtain ⟨hint, hle⟩ := S.spectral_side' ψ₀ (D.discFam z) hB hLS
    (P := (pairCountPts q z : ℝ)) (Nat.cast_nonneg _) (D.discFam_HS z hPT hSC) hE hCψ hψ hCd
    hMd hC6 hM6 hGt hk hCk hMk
  let _ : MeasurableSpace D.ι := ⊤
  have hint' : Integrable (fun j => ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j)‖ *
      ‖∑ i, D.u j (z i)‖) Measure.count := hint
  have hsum : Summable (fun j => ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j)‖ * ‖∑ i, D.u j (z i)‖) := by
    have := integrable_count_iff.1 hint'
    refine this.congr fun j => ?_
    exact Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨hsum, ?_⟩
  rw [← D.integral_count_eq_tsum _ hint']
  exact hle

end Setup

end Triples
