import TriplesFinal.Spectral.LargeSieve
import TriplesFinal.Poisson.FourierBump
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lemma 10.5: Pascadi's inequality with smooth weights

Let `M ≥ 1/2`, `𝒴 ≥ 1`, `L_G ≥ 1`, `C_G > 0`, and let `G : ℝ → ℂ` be smooth, supported in
`[1, 2]`, with `‖G^(k)‖_∞ ≤ C_G L_G^k` for `0 ≤ k ≤ 3`. Then
`∑_{exc} 𝒴^(2θ_j) |∑_n G(n/M) ρ_j(n)|²
   ≪_η C_G² L_G³ (qM)^η (1 + 𝒴/max(M, q))^(2θ) (1 + M/q) M`,
with an implied constant depending only on `η` and the large sieve constants `C(η)`.

The proof writes `G(n/M) = ∫ Ĝ(ξ) e(nξ/M) dξ` (`fourier_inversion_weight`), applies
Cauchy–Schwarz with respect to `|Ĝ(ξ)| dξ` (`norm_integral_mul_sq_le`), and bounds the sum over
the exceptional spectrum for each `ξ` by Lemma 10.4 (or Lemma 10.2 when the range of Lemma 10.4
is empty) (`exc_phase_sum_le`). Finally `|Ĝ(ξ)| ≤ 8C_G (1 + |ξ|/L_G)^(-3)`, so
`∫ |Ĝ| ≪ C_G L_G` and `∫ |Ĝ(ξ)| (1 + |ξ|) dξ ≪ C_G L_G²`.

The statement is uniform in the level `q` (the paper's implied constant depends only on `η`).

Paper: §10.3, Lemma 10.5.
-/

namespace Triples

open MeasureTheory Filter
open scoped FourierTransform ContDiff Real

section Weight

variable {G : ℝ → ℂ} {CG LG : ℝ}

/-- For `G` supported in `[1, 2]` with `‖G^(k)‖ ≤ C_G L^k`: `‖Ĝ(ξ)‖ ≤ 8 C_G (1 + |ξ|/L)^(-3)`. -/
theorem norm_fourier_weight_le (hG : ContDiff ℝ ∞ G) (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2)
    (hL : 1 ≤ LG) (hCG : 0 < CG) (hd : ∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k)
    (ξ : ℝ) : ‖𝓕 G ξ‖ ≤ 8 * CG * (1 + |ξ| / LG) ^ (-(3 : ℝ)) := by
  have hL0 : 0 < LG := by linarith
  have h0 := norm_fourier_le_Icc hG (by norm_num) hs (hd 0 (by norm_num)) ξ
  have h3 := norm_fourier_le_Icc hG (by norm_num) hs (hd 3 (by norm_num)) ξ
  simp only [pow_zero, one_mul, mul_one] at h0
  norm_num at h0 h3
  have hu : 0 < 1 + |ξ| / LG := by positivity
  rw [Real.rpow_neg hu.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [le_mul_inv_iff₀ (by positivity)]
  by_cases hξ : |ξ| ≤ LG
  · have : (1 + |ξ| / LG) ^ 3 ≤ 8 := by
      have : |ξ| / LG ≤ 1 := by rw [div_le_one hL0]; exact hξ
      have h1 : 0 ≤ |ξ| / LG := by positivity
      nlinarith [pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + |ξ| / LG) (by linarith : 1 + |ξ| / LG ≤ 2) 3]
    calc ‖𝓕 G ξ‖ * (1 + |ξ| / LG) ^ 3 ≤ CG * 8 :=
          mul_le_mul h0 this (by positivity) hCG.le
      _ = 8 * CG := by ring
  · push Not at hξ
    have hξ0 : 0 < |ξ| := by linarith
    -- `(2π|ξ|)³ ‖Ĝ‖ ≤ C_G L³` and `(1 + |ξ|/L)³ ≤ 8 |ξ|³/L³`
    have h1 : (1 + |ξ| / LG) ^ 3 ≤ 8 * |ξ| ^ 3 / LG ^ 3 := by
      have : 1 + |ξ| / LG ≤ 2 * (|ξ| / LG) := by
        have : 1 ≤ |ξ| / LG := by rw [le_div_iff₀ hL0]; linarith
        linarith
      calc (1 + |ξ| / LG) ^ 3 ≤ (2 * (|ξ| / LG)) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
        _ = 8 * |ξ| ^ 3 / LG ^ 3 := by rw [mul_pow, div_pow]; ring
    have h2 : |ξ| ^ 3 * ‖𝓕 G ξ‖ ≤ CG * LG ^ 3 := by
      have hπ : 1 ≤ (2 * π) ^ 3 := by
        have := Real.two_le_pi
        nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ 2 * π) 3]
      calc |ξ| ^ 3 * ‖𝓕 G ξ‖ ≤ (2 * π) ^ 3 * (|ξ| ^ 3 * ‖𝓕 G ξ‖) :=
            le_mul_of_one_le_left (by positivity) hπ
        _ = (2 * π * |ξ|) ^ 3 * ‖𝓕 G ξ‖ := by ring
        _ ≤ CG * LG ^ 3 := h3
    calc ‖𝓕 G ξ‖ * (1 + |ξ| / LG) ^ 3 ≤ ‖𝓕 G ξ‖ * (8 * |ξ| ^ 3 / LG ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 8 * (|ξ| ^ 3 * ‖𝓕 G ξ‖) / LG ^ 3 := by ring
      _ ≤ 8 * (CG * LG ^ 3) / LG ^ 3 := by gcongr
      _ = 8 * CG := by field_simp

theorem integrable_fourier_weight (hG : ContDiff ℝ ∞ G) (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2)
    (hL : 1 ≤ LG) (hCG : 0 < CG) (hd : ∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k) :
    Integrable (𝓕 G) := by
  have hL0 : 0 < LG := by linarith
  have hGi : Integrable G := by
    have := integrable_iteratedDeriv_Icc hG hs 0
    simpa using this
  have hmaj : Integrable (fun ξ : ℝ => 8 * CG * (1 + |ξ| / LG) ^ (-(3 : ℝ))) := by
    have h1 := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by norm_num)).comp_div
      hL0.ne'
    have h2 := h1.const_mul (8 * CG)
    refine h2.congr (ae_of_all _ fun ξ => ?_)
    simp [Real.norm_eq_abs, abs_of_pos hL0]
  exact hmaj.mono' (continuous_fourier_of_integrable hGi).aestronglyMeasurable
    (ae_of_all _ fun ξ => norm_fourier_weight_le hG hs hL hCG hd ξ)

/-- Fourier inversion: `G(s) = ∫ Ĝ(ξ) e(sξ) dξ`. -/
theorem fourier_inversion_weight (hG : ContDiff ℝ ∞ G) (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2)
    (hL : 1 ≤ LG) (hCG : 0 < CG) (hd : ∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k)
    (s : ℝ) : G s = ∫ ξ : ℝ, 𝓕 G ξ * Complex.exp (2 * π * Complex.I * (s * ξ)) := by
  have hGi : Integrable G := by
    have := integrable_iteratedDeriv_Icc hG hs 0
    simpa using this
  have h := congrFun (hG.continuous.fourierInv_fourier_eq hGi
    (integrable_fourier_weight hG hs hL hCG hd)) s
  rw [← h, Real.fourierInv_eq']
  congr 1; ext ξ
  rw [smul_eq_mul, mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast; ring

/-- `∫ (1 + |ξ|/L)^(-r) dξ = L ∫ (1 + |u|)^(-r) du`. -/
theorem integral_one_add_div_rpow (r : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ ξ : ℝ, (1 + |ξ| / L) ^ (-r) = L * ∫ u : ℝ, (1 + ‖u‖) ^ (-r) := by
  have := Measure.integral_comp_div (fun u : ℝ => (1 + ‖u‖) ^ (-r)) L
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos hL, smul_eq_mul] at this
  rw [this]
  simp only [Real.norm_eq_abs]

/-- `∫ |Ĝ| ≤ 8 C_G L I₃` with `I₃ = ∫ (1 + |u|)^(-3)`. -/
theorem integral_norm_fourier_weight_le (hG : ContDiff ℝ ∞ G)
    (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hL : 1 ≤ LG) (hCG : 0 < CG)
    (hd : ∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k) :
    ∫ ξ, ‖𝓕 G ξ‖ ≤ 8 * CG * LG * ∫ u : ℝ, (1 + ‖u‖) ^ (-(3 : ℝ)) := by
  have hL0 : 0 < LG := by linarith
  have hmaj : Integrable (fun ξ : ℝ => 8 * CG * (1 + |ξ| / LG) ^ (-(3 : ℝ))) := by
    have h1 := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3) (by norm_num)).comp_div
      hL0.ne'
    refine (h1.const_mul (8 * CG)).congr (ae_of_all _ fun ξ => ?_)
    simp [Real.norm_eq_abs, abs_of_pos hL0]
  calc ∫ ξ, ‖𝓕 G ξ‖ ≤ ∫ ξ, 8 * CG * (1 + |ξ| / LG) ^ (-(3 : ℝ)) :=
        integral_mono (integrable_fourier_weight hG hs hL hCG hd).norm hmaj
          (fun ξ => norm_fourier_weight_le hG hs hL hCG hd ξ)
    _ = 8 * CG * LG * ∫ u : ℝ, (1 + ‖u‖) ^ (-(3 : ℝ)) := by
        rw [integral_const_mul, integral_one_add_div_rpow 3 hL0]; ring

/-- `∫ |Ĝ(ξ)| (1 + |ξ|) dξ ≤ 8 C_G L² I₂` with `I₂ = ∫ (1 + |u|)^(-2)`. -/
theorem integral_norm_fourier_weight_mul_le (hG : ContDiff ℝ ∞ G)
    (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hL : 1 ≤ LG) (hCG : 0 < CG)
    (hd : ∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k) :
    Integrable (fun ξ => ‖𝓕 G ξ‖ * (1 + |ξ|)) ∧
      ∫ ξ, ‖𝓕 G ξ‖ * (1 + |ξ|) ≤ 8 * CG * LG ^ 2 * ∫ u : ℝ, (1 + ‖u‖) ^ (-(2 : ℝ)) := by
  have hL0 : 0 < LG := by linarith
  have hmaj : Integrable (fun ξ : ℝ => 8 * CG * LG * (1 + |ξ| / LG) ^ (-(2 : ℝ))) := by
    have h1 := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)).comp_div
      hL0.ne'
    refine (h1.const_mul (8 * CG * LG)).congr (ae_of_all _ fun ξ => ?_)
    simp [Real.norm_eq_abs, abs_of_pos hL0]
  have hpt : ∀ ξ : ℝ, ‖𝓕 G ξ‖ * (1 + |ξ|) ≤ 8 * CG * LG * (1 + |ξ| / LG) ^ (-(2 : ℝ)) := by
    intro ξ
    have hu : 0 < 1 + |ξ| / LG := by positivity
    have h1 := norm_fourier_weight_le hG hs hL hCG hd ξ
    have h2 : 1 + |ξ| ≤ LG * (1 + |ξ| / LG) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hL0.ne']; linarith
    have e : (1 + |ξ| / LG) ^ (-(2 : ℝ)) = (1 + |ξ| / LG) ^ (-(3 : ℝ)) * (1 + |ξ| / LG) := by
      rw [← Real.rpow_add_one hu.ne']; norm_num
    rw [e]
    calc ‖𝓕 G ξ‖ * (1 + |ξ|) ≤ 8 * CG * (1 + |ξ| / LG) ^ (-(3 : ℝ)) * (LG * (1 + |ξ| / LG)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hint : Integrable (fun ξ => ‖𝓕 G ξ‖ * (1 + |ξ|)) := by
    refine hmaj.mono' ?_ (ae_of_all _ fun ξ => ?_)
    · exact ((continuous_fourier_of_integrable (by
        have := integrable_iteratedDeriv_Icc hG hs 0
        simpa using this)).norm.mul (continuous_const.add continuous_abs)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ξ
  refine ⟨hint, ?_⟩
  calc ∫ ξ, ‖𝓕 G ξ‖ * (1 + |ξ|) ≤ ∫ ξ, 8 * CG * LG * (1 + |ξ| / LG) ^ (-(2 : ℝ)) :=
        integral_mono hint hmaj hpt
    _ = 8 * CG * LG ^ 2 * ∫ u : ℝ, (1 + ‖u‖) ^ (-(2 : ℝ)) := by
        rw [integral_const_mul, integral_one_add_div_rpow 2 hL0]; ring

/-- **Cauchy–Schwarz** with respect to `|F(ξ)| dξ`: `‖∫ F S‖² ≤ (∫ |F|) ∫ |F| |S|²` for integrable
`F` and bounded continuous `S`. -/
theorem norm_integral_mul_sq_le {F S : ℝ → ℂ} (hF : Integrable F) (hS : Continuous S) {B : ℝ}
    (hB : ∀ ξ, ‖S ξ‖ ≤ B) :
    ‖∫ ξ, F ξ * S ξ‖ ^ 2 ≤ (∫ ξ, ‖F ξ‖) * ∫ ξ, ‖F ξ‖ * ‖S ξ‖ ^ 2 := by
  set A := ∫ ξ, ‖F ξ‖ with hAdef
  set Bi := ∫ ξ, ‖F ξ‖ * ‖S ξ‖ ^ 2 with hBdef
  set I := ∫ ξ, ‖F ξ‖ * ‖S ξ‖ with hIdef
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hB0 : 0 ≤ Bi := integral_nonneg fun _ => by positivity
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  have hint1 : Integrable (fun ξ => ‖F ξ‖ * ‖S ξ‖) :=
    hF.norm.mul_bdd hS.norm.aestronglyMeasurable
      (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs, abs_norm]; exact hB ξ)
  have hint2 : Integrable (fun ξ => ‖F ξ‖ * ‖S ξ‖ ^ 2) :=
    hF.norm.mul_bdd (hS.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB ξ) 2)
  have h1 : ‖∫ ξ, F ξ * S ξ‖ ≤ I :=
    (norm_integral_le_integral_norm _).trans (le_of_eq (by simp [hIdef]))
  -- `I ≤ A/(2λ) + λ Bi/2` for every `λ > 0`
  have key : ∀ l : ℝ, 0 < l → I ≤ A / (2 * l) + l * Bi / 2 := by
    intro l hl
    have hpt : ∀ ξ, ‖F ξ‖ * ‖S ξ‖ ≤ ‖F ξ‖ / (2 * l) + l * (‖F ξ‖ * ‖S ξ‖ ^ 2) / 2 := by
      intro ξ
      have h0 : 0 ≤ ‖F ξ‖ := norm_nonneg _
      have hs : ‖S ξ‖ ≤ 1 / (2 * l) + l * ‖S ξ‖ ^ 2 / 2 := by
        rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (l * ‖S ξ‖ - 1)]
      calc ‖F ξ‖ * ‖S ξ‖ ≤ ‖F ξ‖ * (1 / (2 * l) + l * ‖S ξ‖ ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hs h0
        _ = _ := by ring
    calc I ≤ ∫ ξ, (‖F ξ‖ / (2 * l) + l * (‖F ξ‖ * ‖S ξ‖ ^ 2) / 2) :=
          integral_mono hint1 ((hF.norm.div_const _).add ((hint2.const_mul l).div_const _)) hpt
      _ = A / (2 * l) + l * Bi / 2 := by
          rw [integral_add (hF.norm.div_const _) ((hint2.const_mul l).div_const _),
            integral_div, integral_div, integral_const_mul]
  have hI2 : I ^ 2 ≤ A * Bi := by
    rcases hI0.lt_or_eq with hIpos | hIzero
    · rcases hA0.lt_or_eq with hApos | hAzero
      · have := key (A / I) (div_pos hApos hIpos)
        have e1 : A / (2 * (A / I)) = I / 2 := by field_simp
        have e2 : A / I * Bi / 2 = A * Bi / (2 * I) := by field_simp
        rw [e1, e2] at this
        have h3 : I / 2 ≤ A * Bi / (2 * I) := by linarith
        rw [le_div_iff₀ (by positivity)] at h3
        nlinarith
      · exfalso
        have := key (I / (Bi + 1)) (div_pos hIpos (by linarith))
        rw [← hAzero, zero_div, zero_add] at this
        have h2 : I / (Bi + 1) * Bi / 2 < I := by
          rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
    · rw [← hIzero]; simp; positivity
  calc ‖∫ ξ, F ξ * S ξ‖ ^ 2 ≤ I ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ A * Bi := hI2

end Weight

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

theorem exceptional_re {j : D.ι} (hj : D.IsExceptional j) :
    (D.t j).re = 0 ∧ 0 < (D.t j).im ∧ (D.t j).im < 1 / 2 := by
  rcases D.t_mem j with h | h
  · exact absurd h.1 (ne_of_gt hj)
  · exact h

theorem norm_t_le_one {j : D.ι} (hj : D.IsExceptional j) : ‖D.t j‖ ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := D.exceptional_re hj
  have := Complex.norm_le_abs_re_add_abs_im (D.t j)
  rw [h1, abs_zero, zero_add, abs_of_pos h2] at this
  linarith

theorem finite_exceptional : {j | D.IsExceptional j}.Finite :=
  (D.finite_le 1).subset fun _ hj => D.norm_t_le_one hj

/-- For exceptional `j`, `cosh(π t_j) = cos(π θ_j) ∈ (0, 1]`. -/
theorem cosh_re_exceptional {j : D.ι} (hj : D.IsExceptional j) :
    0 < (Complex.cosh (π * D.t j)).re ∧ (Complex.cosh (π * D.t j)).re ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := D.exceptional_re hj
  have ht : D.t j = ((D.t j).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h1]
  rw [ht, ← mul_assoc, Complex.cosh_mul_I, ← Complex.ofReal_mul, Complex.cos_ofReal_re]
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩, Real.cos_le_one _⟩
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- `cosh(π t_j)` has positive real part for every `j`. -/
theorem cosh_re_pos (j : D.ι) : 0 < (Complex.cosh (π * D.t j)).re := by
  by_cases hj : D.IsExceptional j
  · exact (D.cosh_re_exceptional hj).1
  · rcases D.t_mem j with h | h
    · have ht : D.t j = ((D.t j).re : ℂ) := by apply Complex.ext <;> simp [h.1]
      rw [ht, ← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_re]
      exact Real.cosh_pos _
    · exact absurd h.2.1 hj

/-- The pointwise bound in the proof of Lemma 10.5: for every `ξ`, with `α = ξ/M`,
`∑_{exc} 𝒴^(2θ_j) |∑_{n ∼ M} e(nα) ρ_j(n)|²
   ≤ 3·2^η |C(η)| (qM)^η (1 + M/q) M (1 + |ξ|) (1 + 𝒴/max(M, q))^(2θ)`. -/
theorem exc_phase_sum_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) {C : ℝ → ℝ}
    (hDI2 : D.LargeSieveDI2 C) (hPas : D.LargeSievePascadi C) (hexc : D.ExceptionalBound θ)
    (hq : 0 < q) {η : ℝ} (hη : 0 < η) {M Y : ℝ} (hM : 1 / 2 ≤ M) (hY : 1 ≤ Y) (ξ : ℝ) :
    ∑ᶠ j ∈ {j | D.IsExceptional j}, Y ^ (2 * (D.t j).im) *
        ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
          Complex.exp (2 * π * Complex.I * (n * ((ξ / M : ℝ) : ℂ))) * D.ρ j n‖ ^ 2 ≤
      3 * 2 ^ η * |C η| * (q * M) ^ η * (1 + M / q) * M * (1 + |ξ|) *
        (1 + Y / max M q) ^ (2 * θ) := by
  classical
  set E := D.finite_exceptional.toFinset with hE
  set S : D.ι → ℝ := fun j => ‖∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
      Complex.exp (2 * π * Complex.I * (n * ((ξ / M : ℝ) : ℂ))) * D.ρ j n‖ ^ 2 with hS
  have hS0 : ∀ j, 0 ≤ S j := fun j => by positivity
  rw [finsum_mem_eq_finite_toFinset_sum _ D.finite_exceptional]
  have hM0 : 0 < M := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqM : 0 < (q : ℝ) * M := by positivity
  set P := |C η| * ((q * M) ^ η * (1 + M / q) * M) with hP
  have hX0 : 0 ≤ (q * M : ℝ) ^ η * (1 + M / q) * M := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hmax : 0 < max M (q : ℝ) := lt_of_lt_of_le hM0 (le_max_left _ _)
  set R := max M q / (1 + |ξ|) with hR
  have hR0 : 0 < R := by positivity
  set F := (1 + |ξ|) * (1 + Y / max M q) ^ (2 * θ) with hF
  have hu0 : 0 ≤ Y / max M q := by positivity
  have hF1 : 1 ≤ F := by
    have h1 : 1 ≤ 1 + |ξ| := by linarith [abs_nonneg ξ]
    have h2 : 1 ≤ (1 + Y / max M q) ^ (2 * θ) := Real.one_le_rpow (by linarith) (by linarith)
    nlinarith
  have hEmem : ∀ j ∈ E, D.IsExceptional j := fun j hj => by
    rw [hE, Set.Finite.mem_toFinset] at hj; exact hj
  have hθj : ∀ j ∈ E, (D.t j).im ≤ θ := fun j hj => hexc j (hEmem j hj)
  have hθj0 : ∀ j ∈ E, 0 ≤ (D.t j).im := fun j hj => (D.exceptional_re (hEmem j hj)).2.1.le
  -- `(𝒴/R)^(2θ) ≤ F`
  have hYR : (Y / R) ^ (2 * θ) ≤ F := by
    have h1 : Y / R = (1 + |ξ|) * (Y / max M q) := by rw [hR]; field_simp
    have h2 : Y / R ≤ (1 + |ξ|) * (1 + Y / max M q) := by
      rw [h1]; have : 0 ≤ 1 + |ξ| := by positivity
      nlinarith
    calc (Y / R) ^ (2 * θ) ≤ ((1 + |ξ|) * (1 + Y / max M q)) ^ (2 * θ) :=
          Real.rpow_le_rpow (by positivity) h2 (by linarith)
      _ = (1 + |ξ|) ^ (2 * θ) * (1 + Y / max M q) ^ (2 * θ) :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ (1 + |ξ|) ^ (1 : ℝ) * (1 + Y / max M q) ^ (2 * θ) := by
          gcongr
          · linarith [abs_nonneg ξ]
          · linarith
      _ = F := by rw [Real.rpow_one]
  -- Pascadi for `𝒴' ∈ [1, R]`
  have hPasR : ∀ Y' : ℝ, 1 ≤ Y' → Y' ≤ R → ∑ j ∈ E, Y' ^ (2 * (D.t j).im) * S j ≤ P := by
    intro Y' hY1 hYR'
    have hα : M * |ξ / M - round (ξ / M)| ≤ |ξ| := by
      have := round_le (ξ / M) 0
      simp only [Int.cast_zero, sub_zero] at this
      calc M * |ξ / M - round (ξ / M)| ≤ M * |ξ / M| := mul_le_mul_of_nonneg_left this hM0.le
        _ = |ξ| := by rw [abs_div, abs_of_pos hM0]; field_simp
    have hcond : Y' ≤ max M q / (1 + M * |ξ / M - round (ξ / M)|) := by
      refine hYR'.trans ?_
      rw [hR]
      exact div_le_div_of_nonneg_left hmax.le (by positivity) (by linarith)
    have := hPas η hη M hM (ξ / M) Y' hY1 hcond
    rw [finsum_mem_eq_finite_toFinset_sum _ D.finite_exceptional] at this
    refine this.trans ?_
    rw [hP, ← mul_assoc, ← mul_assoc]
    rw [show C η * (q * M) ^ η * (1 + M / q) * M = C η * ((q * M) ^ η * (1 + M / q) * M) by ring,
      show |C η| * (q * M) ^ η * (1 + M / q) * M = |C η| * ((q * M) ^ η * (1 + M / q) * M) by ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hX0
  have h2η : (1 : ℝ) ≤ 2 ^ η := Real.one_le_rpow (by norm_num) hη.le
  have hgoal : 3 * 2 ^ η * |C η| * (q * M) ^ η * (1 + M / q) * M * (1 + |ξ|) *
      (1 + Y / max M q) ^ (2 * θ) = 3 * 2 ^ η * P * F := by rw [hP, hF]; ring
  rw [hgoal]
  rcases le_or_gt Y R with hYR' | hRY
  · -- `𝒴 ≤ R`: Pascadi with `𝒴`
    calc ∑ j ∈ E, Y ^ (2 * (D.t j).im) * S j ≤ P := hPasR Y hY hYR'
      _ ≤ 3 * 2 ^ η * P * F := by
          have : 1 ≤ 3 * 2 ^ η * F := by nlinarith
          nlinarith
  rcases le_or_gt 1 R with hR1 | hR1
  · -- `1 ≤ R < 𝒴`: Pascadi with `R`
    have hYR1 : 1 ≤ Y / R := by rw [le_div_iff₀ hR0]; linarith
    have hpt : ∀ j ∈ E, Y ^ (2 * (D.t j).im) * S j ≤
        (Y / R) ^ (2 * θ) * (R ^ (2 * (D.t j).im) * S j) := by
      intro j hj
      have e : Y = R * (Y / R) := by field_simp
      have h1 : Y ^ (2 * (D.t j).im) = R ^ (2 * (D.t j).im) * (Y / R) ^ (2 * (D.t j).im) := by
        conv_lhs => rw [e]
        exact Real.mul_rpow hR0.le (by positivity)
      have h2 : (Y / R) ^ (2 * (D.t j).im) ≤ (Y / R) ^ (2 * θ) :=
        Real.rpow_le_rpow_of_exponent_le hYR1 (by linarith [hθj j hj])
      rw [h1]
      have hRS : 0 ≤ R ^ (2 * (D.t j).im) * S j := mul_nonneg (by positivity) (hS0 j)
      calc R ^ (2 * (D.t j).im) * (Y / R) ^ (2 * (D.t j).im) * S j
          = (Y / R) ^ (2 * (D.t j).im) * (R ^ (2 * (D.t j).im) * S j) := by ring
        _ ≤ (Y / R) ^ (2 * θ) * (R ^ (2 * (D.t j).im) * S j) :=
          mul_le_mul_of_nonneg_right h2 hRS
    calc ∑ j ∈ E, Y ^ (2 * (D.t j).im) * S j
        ≤ ∑ j ∈ E, (Y / R) ^ (2 * θ) * (R ^ (2 * (D.t j).im) * S j) := Finset.sum_le_sum hpt
      _ = (Y / R) ^ (2 * θ) * ∑ j ∈ E, R ^ (2 * (D.t j).im) * S j := (Finset.mul_sum _ _ _).symm
      _ ≤ F * P := mul_le_mul hYR (hPasR R hR1 le_rfl)
          (Finset.sum_nonneg fun j _ => by have := hS0 j; positivity) (by linarith)
      _ ≤ 3 * 2 ^ η * P * F := by
          have h3 : (1 : ℝ) ≤ 3 * (2 : ℝ) ^ η := by linarith
          have h4 : 0 ≤ P * F := mul_nonneg hP0 (by linarith)
          calc F * P = 1 * (P * F) := by ring
            _ ≤ (3 * (2 : ℝ) ^ η) * (P * F) := mul_le_mul_of_nonneg_right h3 h4
            _ = 3 * 2 ^ η * P * F := by ring
  · -- `R < 1`: Lemma 10.2 with `T = 1`
    have hpt : ∀ j ∈ E, Y ^ (2 * (D.t j).im) * S j ≤ (Y / R) ^ (2 * θ) * S j := by
      intro j hj
      have h1 : Y ^ (2 * (D.t j).im) ≤ Y ^ (2 * θ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith [hθj j hj])
      have h2 : Y ^ (2 * θ) ≤ (Y / R) ^ (2 * θ) := by
        apply Real.rpow_le_rpow (by linarith) _ (by linarith)
        rw [le_div_iff₀ hR0]; nlinarith
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (hS0 j)
    -- the sum over the exceptional spectrum is bounded by Lemma 10.2
    set a : ℕ → ℂ := fun n => if M < n ∧ (n : ℝ) ≤ 2 * M then
      Complex.exp (2 * π * Complex.I * (n * ((ξ / M : ℝ) : ℂ))) else 0 with ha
    have hasupp : ∀ n, a n ≠ 0 → M < n ∧ (n : ℝ) ≤ 2 * M := by
      intro n hn
      by_contra h
      exact hn (by simp [ha, h])
    have hDI := hDI2 η hη 1 le_rfl M hM a hasupp
    have hsum_eq : ∀ j, ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * D.ρ j n =
        ∑ n ∈ (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n),
          Complex.exp (2 * π * Complex.I * (n * ((ξ / M : ℝ) : ℂ))) * D.ρ j n := by
      intro j
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn2 : (n : ℝ) ≤ 2 * M := by
        have := Nat.floor_le (show (0 : ℝ) ≤ 2 * M by linarith)
        exact le_trans (by exact_mod_cast hn.2) this
      by_cases hMn : M < (n : ℝ)
      · simp [ha, hMn, hn2]
      · simp [ha, hMn]
    simp only [hsum_eq] at hDI
    have hfin1 := D.finite_le 1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin1] at hDI
    have hEis : 0 ≤ ∑ 𝔰, ∫ r in Set.Icc (-1 : ℝ) 1,
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * D.ρEis 𝔰 r n‖ ^ 2 / Real.cosh (π * r) :=
      Finset.sum_nonneg fun 𝔰 _ => integral_nonneg fun r => by
        have := Real.cosh_pos (π * r); positivity
    have hsub : E ⊆ hfin1.toFinset := by
      intro j hj
      rw [Set.Finite.mem_toFinset]
      exact D.norm_t_le_one (hEmem j hj)
    have hexcS : ∑ j ∈ E, S j ≤ ∑ j ∈ hfin1.toFinset, S j / (Complex.cosh (π * D.t j)).re := by
      calc ∑ j ∈ E, S j ≤ ∑ j ∈ E, S j / (Complex.cosh (π * D.t j)).re := by
            apply Finset.sum_le_sum
            intro j hj
            obtain ⟨h1, h2⟩ := D.cosh_re_exceptional (hEmem j hj)
            rw [le_div_iff₀ h1]
            have := hS0 j
            nlinarith
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by
            have := D.cosh_re_pos j; have := hS0 j; positivity
    have hcount : ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 ≤ 2 * M := by
      calc ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n _
            by_cases h : M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M
            · simp only [ha, h, and_self, ite_true]
              rw [show 2 * (π : ℂ) * Complex.I * (n * ((ξ / M : ℝ) : ℂ)) =
                ((2 * π * (n * (ξ / M)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.norm_exp_ofReal_mul_I]
              norm_num
            · simp [ha, h]
        _ = ⌊2 * M⌋₊ := by simp
        _ ≤ 2 * M := Nat.floor_le (by linarith)
    have hqM2 : (1 : ℝ) / 2 ≤ q * M := by nlinarith
    have hMη : 1 + M ^ (1 + η) / q ≤ (2 : ℝ) ^ η * (q * M) ^ η * (1 + M / q) := by
      have hab : 1 ≤ (2 : ℝ) ^ η * (q : ℝ) ^ η := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.one_le_rpow (by linarith) hη.le
      have hc : 0 < M ^ η := Real.rpow_pos_of_pos hM0 η
      have hqMη : (q * M : ℝ) ^ η = (q : ℝ) ^ η * M ^ η := Real.mul_rpow (by positivity) hM0.le
      have h1 : 1 ≤ (2 : ℝ) ^ η * (q * M) ^ η := by
        rw [← Real.mul_rpow (by norm_num) hqM.le]
        exact Real.one_le_rpow (by linarith) hη.le
      have h2 : M ^ (1 + η) / q ≤ (2 : ℝ) ^ η * (q * M) ^ η * (M / q) := by
        rw [Real.rpow_add hM0, Real.rpow_one, hqMη]
        have hcle : M ^ η ≤ (2 : ℝ) ^ η * ((q : ℝ) ^ η * M ^ η) := by
          calc M ^ η = 1 * M ^ η := (one_mul _).symm
            _ ≤ ((2 : ℝ) ^ η * (q : ℝ) ^ η) * M ^ η := mul_le_mul_of_nonneg_right hab hc.le
            _ = _ := by ring
        calc M * M ^ η / q = M ^ η * (M / q) := by ring
          _ ≤ (2 : ℝ) ^ η * ((q : ℝ) ^ η * M ^ η) * (M / q) :=
              mul_le_mul_of_nonneg_right hcle (by positivity)
          _ = _ := by ring
      calc 1 + M ^ (1 + η) / q ≤ (2 : ℝ) ^ η * (q * M) ^ η +
            (2 : ℝ) ^ η * (q * M) ^ η * (M / q) := add_le_add h1 h2
        _ = _ := by ring
    calc ∑ j ∈ E, Y ^ (2 * (D.t j).im) * S j ≤ ∑ j ∈ E, (Y / R) ^ (2 * θ) * S j :=
          Finset.sum_le_sum hpt
      _ = (Y / R) ^ (2 * θ) * ∑ j ∈ E, S j := (Finset.mul_sum _ _ _).symm
      _ ≤ F * (2 * 2 ^ η * P) := by
          apply mul_le_mul hYR _ (Finset.sum_nonneg fun j _ => hS0 j) (by linarith)
          calc ∑ j ∈ E, S j ≤ C η * (1 ^ 2 + M ^ (1 + η) / q) *
                ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 := by
                  refine hexcS.trans ?_
                  refine le_trans ?_ hDI
                  simp only [hS]
                  linarith
            _ ≤ |C η| * (1 + M ^ (1 + η) / q) * (2 * M) := by
                rw [one_pow]
                have h1 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 :=
                  Finset.sum_nonneg fun n _ => by positivity
                have h2 : 0 ≤ 1 + M ^ (1 + η) / q := by positivity
                calc C η * (1 + M ^ (1 + η) / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2
                    ≤ |C η| * (1 + M ^ (1 + η) / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 := by
                      gcongr; exact le_abs_self _
                  _ ≤ |C η| * (1 + M ^ (1 + η) / q) * (2 * M) := by gcongr
            _ ≤ |C η| * (2 ^ η * (q * M) ^ η * (1 + M / q)) * (2 * M) := by gcongr
            _ = 2 * 2 ^ η * P := by rw [hP]; ring
      _ ≤ 3 * 2 ^ η * P * F := by
          have h4 : 0 ≤ (2 : ℝ) ^ η * P * F := mul_nonneg (mul_nonneg (by positivity) hP0)
            (by linarith)
          calc F * (2 * (2 : ℝ) ^ η * P) = 2 * ((2 : ℝ) ^ η * P * F) := by ring
            _ ≤ 3 * ((2 : ℝ) ^ η * P * F) := by linarith
            _ = 3 * (2 : ℝ) ^ η * P * F := by ring

/-- A smooth function supported in `[1, 2]` vanishes on `(-∞, 1]`. -/
theorem weight_eq_zero_of_le {G : ℝ → ℂ} (hG : Continuous G) (hs : ∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2)
    {t : ℝ} (ht : t ≤ 1) : G t = 0 := by
  have hcl : IsClosed {t : ℝ | G t = 0} := isClosed_eq hG continuous_const
  have hsub : Set.Iio (1 : ℝ) ⊆ {t : ℝ | G t = 0} := by
    intro t ht
    by_contra hne
    have := (hs t hne).1
    exact absurd ht (not_lt.2 this)
  have := hcl.closure_subset_iff.2 hsub
  rw [closure_Iio' (Set.nonempty_Iio)] at this
  exact this ht

/-- **Lemma 10.5**, with a constant depending only on `η` and on the large sieve constants. -/
theorem smooth_weights {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (C : ℝ → ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∃ C' : ℝ, ∀ (q : ℕ) (D : SpectralData q), 0 < q → D.LargeSieveDI2 C →
      D.LargeSievePascadi C → D.ExceptionalBound θ →
      ∀ (M Y LG CG : ℝ), 1 / 2 ≤ M → 1 ≤ Y → 1 ≤ LG → 0 < CG →
      ∀ G : ℝ → ℂ, ContDiff ℝ ∞ G → (∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2) →
      (∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k) →
      ∑ᶠ j ∈ {j | D.IsExceptional j},
          Y ^ (2 * (D.t j).im) * ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * D.ρ j n‖ ^ 2 ≤
        C' * CG ^ 2 * LG ^ 3 * (q * M) ^ η * (1 + Y / max M q) ^ (2 * θ) * (1 + M / q) * M := by
  classical
  set I₂ := ∫ u : ℝ, (1 + ‖u‖) ^ (-(2 : ℝ)) with hI₂
  set I₃ := ∫ u : ℝ, (1 + ‖u‖) ^ (-(3 : ℝ)) with hI₃
  refine ⟨64 * I₃ * I₂ * (3 * 2 ^ η * |C η|), ?_⟩
  intro q D hq hDI2 hPas hexc M Y LG CG hM hY hL hCG G hG hs hd
  have hM0 : 0 < M := by linarith
  set E := D.finite_exceptional.toFinset with hE
  rw [finsum_mem_eq_finite_toFinset_sum _ D.finite_exceptional]
  -- the phase sums
  set N := (Finset.Icc 1 ⌊2 * M⌋₊).filter (fun n : ℕ => M < n) with hN
  set Sj : D.ι → ℝ → ℂ := fun j ξ => ∑ n ∈ N,
    Complex.exp (2 * π * Complex.I * (n * ((ξ / M : ℝ) : ℂ))) * D.ρ j n with hSj
  have hSj_cont : ∀ j, Continuous (Sj j) := fun j => by
    simp only [hSj]
    fun_prop
  have hSj_bdd : ∀ j ξ, ‖Sj j ξ‖ ≤ ∑ n ∈ N, ‖D.ρ j n‖ := by
    intro j ξ
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, show 2 * (π : ℂ) * Complex.I * (n * ((ξ / M : ℝ) : ℂ)) =
      ((2 * π * (n * (ξ / M)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hFi := integrable_fourier_weight hG hs hL hCG hd
  -- `∑_n G(n/M) ρ_j(n) = ∫ Ĝ(ξ) S_j(ξ) dξ`
  have hT : ∀ j, ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * D.ρ j n =
      ∫ ξ, 𝓕 G ξ * Sj j ξ := by
    intro j
    have h1 : ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * D.ρ j n =
        ∑ n ∈ N, G (n / M) * D.ρ j n := by
      rw [hN, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs with h
      · rfl
      · rw [weight_eq_zero_of_le hG.continuous hs (by
          push Not at h; rw [div_le_one hM0]; exact h), zero_mul]
    rw [h1]
    simp only [hSj, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n _
      rw [fourier_inversion_weight hG hs hL hCG hd, ← integral_mul_const]
      congr 1; ext ξ
      rw [mul_assoc]
      congr 2
      push_cast; ring_nf
    · intro n _
      refine (hFi.mul_bdd (c := ‖D.ρ j n‖) (by fun_prop) (ae_of_all _ fun ξ => ?_))
      rw [norm_mul, show 2 * (π : ℂ) * Complex.I * (n * ((ξ / M : ℝ) : ℂ)) =
        ((2 * π * (n * (ξ / M)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
  -- Cauchy–Schwarz for each `j`
  set A := ∫ ξ, ‖𝓕 G ξ‖ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hCS : ∀ j, ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * D.ρ j n‖ ^ 2 ≤
      A * ∫ ξ, ‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2 := by
    intro j
    rw [hT j]
    exact norm_integral_mul_sq_le hFi (hSj_cont j) (hSj_bdd j)
  have hint_j : ∀ j, Integrable (fun ξ => ‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2) := fun j =>
    hFi.norm.mul_bdd ((hSj_cont j).norm.pow 2).aestronglyMeasurable (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hSj_bdd j ξ) 2)
  set K := 3 * 2 ^ η * |C η| * (q * M) ^ η * (1 + M / q) * M * (1 + Y / max M q) ^ (2 * θ)
    with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  have hpt : ∀ ξ, ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ‖Sj j ξ‖ ^ 2 ≤ K * (1 + |ξ|) := by
    intro ξ
    have := D.exc_phase_sum_le hθ0 hθ hDI2 hPas hexc hq hη hM hY ξ
    rw [finsum_mem_eq_finite_toFinset_sum _ D.finite_exceptional] at this
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · rfl
    · rw [hK]; ring
  obtain ⟨hint1, hbound1⟩ := integral_norm_fourier_weight_mul_le hG hs hL hCG hd
  have hA_le := integral_norm_fourier_weight_le hG hs hL hCG hd
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => by positivity
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  have hsum_int : ∫ ξ, ∑ j ∈ E, Y ^ (2 * (D.t j).im) * (‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2) =
      ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ∫ ξ, ‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2 := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl; intro j _; rw [integral_const_mul]
    · intro j _; exact (hint_j j).const_mul _
  calc ∑ j ∈ E, Y ^ (2 * (D.t j).im) *
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * D.ρ j n‖ ^ 2
      ≤ ∑ j ∈ E, Y ^ (2 * (D.t j).im) * (A * ∫ ξ, ‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hCS j) (by positivity)
    _ = A * ∫ ξ, ‖𝓕 G ξ‖ * ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ‖Sj j ξ‖ ^ 2 := by
        have e : ∀ ξ, ‖𝓕 G ξ‖ * ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ‖Sj j ξ‖ ^ 2 =
            ∑ j ∈ E, Y ^ (2 * (D.t j).im) * (‖𝓕 G ξ‖ * ‖Sj j ξ‖ ^ 2) := fun ξ => by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        simp_rw [e]
        rw [hsum_int, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ A * ∫ ξ, ‖𝓕 G ξ‖ * (1 + |ξ|) * K := by
        apply mul_le_mul_of_nonneg_left _ hA0
        apply integral_mono_of_nonneg (ae_of_all _ fun ξ => by
          have : 0 ≤ ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ‖Sj j ξ‖ ^ 2 :=
            Finset.sum_nonneg fun j _ => by positivity
          positivity) (hint1.mul_const K)
        exact ae_of_all _ fun ξ => by
          calc ‖𝓕 G ξ‖ * ∑ j ∈ E, Y ^ (2 * (D.t j).im) * ‖Sj j ξ‖ ^ 2
              ≤ ‖𝓕 G ξ‖ * (K * (1 + |ξ|)) := mul_le_mul_of_nonneg_left (hpt ξ) (norm_nonneg _)
            _ = ‖𝓕 G ξ‖ * (1 + |ξ|) * K := by ring
    _ = A * (∫ ξ, ‖𝓕 G ξ‖ * (1 + |ξ|)) * K := by rw [integral_mul_const]; ring
    _ ≤ (8 * CG * LG * I₃) * (8 * CG * LG ^ 2 * I₂) * K := by
        apply mul_le_mul_of_nonneg_right _ hK0
        exact mul_le_mul hA_le hbound1 (integral_nonneg fun _ => by positivity) (by positivity)
    _ = _ := by rw [hK]; ring

end SpectralData

end Triples
