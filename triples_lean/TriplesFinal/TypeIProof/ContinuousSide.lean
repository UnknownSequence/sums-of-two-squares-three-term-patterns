import TriplesFinal.TypeIProof.ContinuousFamily

/-!
# The continuous spectrum: the bound for `(1/4π) ∑_𝔰 ∫ |B_𝔰(r) U_𝔰(r)| dr`

The hypotheses of the continuous family follow from Lemma 10.2 (`contFam_LS`) and Lemma 10.7
(`contFam_HS`), and `spectral_side'` gives the bound (`continuous_side`).

Paper: §12.5.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane

namespace SpectralData

variable {q : ℕ} (D : SpectralData q) (hEC : D.EisensteinContinuous) {n : ℕ} (z : Fin n → ℍ)

theorem cosh_ofReal_re (r : ℝ) :
    (Complex.cosh (Real.pi * (r : ℂ))).re = Real.cosh (Real.pi * r) := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_re]

/-- Integrals over a ball of the continuous family. -/
theorem contFam_setIntegral (T : ℝ) {g : D.κ → ℝ → ℝ} (hg : ∀ 𝔰, Continuous (g 𝔰)) :
    ∫ x in (D.contFam hEC z).ball T, g x.1 x.2 ∂(D.contFam hEC z).ν =
      1 / (4 * Real.pi) * ∑ 𝔰, ∫ r in Icc (-T) T, g 𝔰 r := by
  let _ : MeasurableSpace D.κ := ⊤
  show ∫ x in {p : D.κ × ℝ | ‖((p.2 : ℝ) : ℂ)‖ ≤ T}, g x.1 x.2
      ∂(ENNReal.ofReal (1 / (4 * Real.pi)) • (Measure.count.prod volume)) = _
  rw [D.ball_eq_prod T, Measure.restrict_smul, integral_smul_measure]
  have hi := integrableOn_prod_Icc hg T 1 ENNReal.one_ne_top
  rw [one_smul] at hi
  rw [integral_count_prod_restrict hi, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- **Lemma 10.2 for the continuous family.** -/
theorem contFam_LS {C : ℝ → ℝ} (hLS : D.LargeSieveDI2 C) : (D.contFam hEC z).LS q C := by
  intro η hη T hT M hM a ha
  have h := hLS η hη T hT M hM a ha
  have hdisc : 0 ≤ ∑ᶠ j ∈ {j | ‖D.t j‖ ≤ T},
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρ j m‖ ^ 2 / (Complex.cosh (Real.pi * D.t j)).re :=
    finsum_nonneg fun j => finsum_nonneg fun _ =>
      div_nonneg (sq_nonneg _) (D.cosh_re_pos j).le
  have hcont : 0 ≤ ∑ 𝔰, ∫ r in Set.Icc (-T) T,
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis 𝔰 r m‖ ^ 2 / Real.cosh (Real.pi * r) :=
    Finset.sum_nonneg fun 𝔰 _ =>
      integral_nonneg fun r => div_nonneg (sq_nonneg _) (Real.cosh_pos _).le
  have hg : ∀ 𝔰, Continuous fun r : ℝ =>
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis 𝔰 r m‖ ^ 2 / Real.cosh (Real.pi * r) := by
    intro 𝔰
    refine Continuous.div ?_ (by fun_prop) (fun r => (Real.cosh_pos _).ne')
    have hρc : ∀ m : ℕ, Continuous fun r : ℝ => D.ρEis 𝔰 r (m : ℤ) := fun m => hEC.1 𝔰 m
    have hs : Continuous fun r : ℝ => ∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis 𝔰 r m :=
      continuous_finsetSum _ fun m _ => continuous_const.mul (hρc m)
    exact (continuous_pow 2).comp hs.norm
  have e := D.contFam_setIntegral hEC z T hg
  have e' : ∫ x in (D.contFam hEC z).ball T,
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * (D.contFam hEC z).ρ x m‖ ^ 2 / (D.contFam hEC z).ch x
        ∂(D.contFam hEC z).ν =
      ∫ x in (D.contFam hEC z).ball T,
        ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis x.1 x.2 m‖ ^ 2 / Real.cosh (Real.pi * x.2)
        ∂(D.contFam hEC z).ν := by
    congr 1
    funext x
    show _ / (Complex.cosh (Real.pi * ((x.2 : ℝ) : ℂ))).re = _
    rw [cosh_ofReal_re]
    rfl
  rw [e', e]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hR : 0 ≤ C η * (T ^ 2 + M ^ (1 + η) / q) * ∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a m‖ ^ 2 := by
    linarith
  have h4 : 1 / (4 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  calc 1 / (4 * Real.pi) * ∑ 𝔰, ∫ r in Icc (-T) T,
        ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis 𝔰 r m‖ ^ 2 / Real.cosh (Real.pi * r)
      ≤ 1 * (C η * (T ^ 2 + M ^ (1 + η) / q) * ∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a m‖ ^ 2) := by
        apply mul_le_mul h4 (by linarith) hcont zero_le_one
    _ = _ := one_mul _

/-- **Lemma 10.7 for the continuous family.** -/
theorem contFam_HS (hPT : D.PreTrace) (hSC : SelbergConvolution) :
    (D.contFam hEC z).HS (pairCountPts q z) := by
  intro T hT
  have h := D.heegner_side hPT hSC hT z
  have hd1 : 0 ≤ ∑ᶠ j ∈ {j | (D.t j).im = 0 ∧ (D.t j).re ≤ T}, ‖∑ i, D.u j (z i)‖ ^ 2 :=
    finsum_nonneg fun j => finsum_nonneg fun _ => sq_nonneg _
  have hd2 : 0 ≤ ∑ᶠ j ∈ {j | D.IsExceptional j}, ‖∑ i, D.u j (z i)‖ ^ 2 :=
    finsum_nonneg fun j => finsum_nonneg fun _ => sq_nonneg _
  have hg : ∀ 𝔰, Continuous fun r : ℝ => ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 := fun 𝔰 =>
    (continuous_finsetSum _ fun i _ => hEC.2 𝔰 (z i)).norm.pow 2
  have e := D.contFam_setIntegral hEC z T hg
  show ∫ x in (D.contFam hEC z).ball T, ‖∑ i, D.Eis x.1 x.2 (z i)‖ ^ 2
    ∂(D.contFam hEC z).ν ≤ _
  rw [e]
  linarith

theorem contFam_exc : (D.contFam hEC z).exc = ∅ := by
  ext x
  simp only [SpecFam.exc, mem_empty_iff_false, iff_false, Set.mem_ofPred_eq, not_lt]
  show ((x.2 : ℝ) : ℂ).im ≤ 0
  simp

/-- Integrals over the whole continuous family. -/
theorem contFam_integral {f : D.κ × ℝ → ℝ} (hf : Integrable f (D.contFam hEC z).ν) :
    ∫ x, f x ∂(D.contFam hEC z).ν = 1 / (4 * Real.pi) * ∑ 𝔰, ∫ r, f (𝔰, r) := by
  let _ : MeasurableSpace D.κ := ⊤
  have hc0 : ENNReal.ofReal (1 / (4 * Real.pi)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hf' : Integrable f (Measure.count.prod volume) :=
    (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).1 hf
  show ∫ x, f x ∂(ENNReal.ofReal (1 / (4 * Real.pi)) • (Measure.count.prod volume)) = _
  rw [integral_smul_measure, integral_count_prod hf', ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

end SpectralData

end Triples
