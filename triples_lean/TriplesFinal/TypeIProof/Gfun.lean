import TriplesFinal.TypeIProof.BJ1
import TriplesFinal.Analysis.DerivBounds

/-!
# The weights `G_{s,σ}` of the spectrum `𝒥₀`

`G_{s,σ}(y) = ψ₀(y) conj(ψ̂₂(yMXs/K)) e^(-2πyMYs cosh σ)` is smooth, supported in `[1, 2]`,
bounded by `2C₀` for `s ≥ 0`, and `|G_{s,σ}^(k)| ≤ C_G L^k` for `k ≤ 3`, `s ∈ [1/2, 1]`,
uniformly in `σ` (since `λ^k e^(-λy) ≤ 2^k k!` for `y ≥ 1/2`, and `MXs/K ≤ 2Q^η ≤ L/4`).

Paper: §12.2.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval Nat FourierTransform

theorem conj_fourier (ψ : ℝ → ℂ) (ξ : ℝ) :
    (starRingEnd ℂ) (fourier ψ ξ) = fourier (fun t => (starRingEnd ℂ) (ψ t)) (-ξ) := by
  unfold fourier
  rw [← integral_conj]
  congr 1; ext t
  rw [map_mul]
  congr 1
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- `iteratedDeriv k (y ↦ e^(c y)) = c^k e^(c y)` for complex `c` and real `y`. -/
theorem iteratedDeriv_cexp_real (c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => Complex.exp (c * y)) =
      fun y : ℝ => c ^ k * Complex.exp (c * y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext y
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c y := by
      have := ((hasDerivAt_id (y : ℂ)).const_mul c).comp_ofReal (z := y)
      simpa using this
    have h2 := (h1.cexp).const_mul (c ^ k)
    rw [h2.deriv]
    ring

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

theorem Gfun_eq (s σ : ℝ) : S.Gfun ψ₀ s σ = fun y =>
    (ψ₀.ψ₀ y : ℂ) * fourier (fun t => (starRingEnd ℂ) (S.ψ₂ t)) ((-(S.M * S.X * s / S.K)) * y) *
      Complex.exp ((-(2 * Real.pi * S.M * S.Y * s * Real.cosh σ) : ℂ) * y) := by
  ext y
  unfold Gfun
  rw [conj_fourier]
  congr 2
  · congr 1; ring
  · rw [Complex.ofReal_exp]; congr 1; push_cast; ring

theorem Gfun_support (s σ y : ℝ) (h : S.Gfun ψ₀ s σ y ≠ 0) : 1 < y ∧ y ≤ 2 := by
  apply ψ₀.lt_of_ne_zero
  intro h0
  apply h
  unfold Gfun; rw [h0]; simp

theorem norm_Gfun_le {s : ℝ} (hs : 0 ≤ s) (σ y : ℝ) : ‖S.Gfun ψ₀ s σ y‖ ≤ 2 * S.C₀ := by
  by_cases h0 : S.Gfun ψ₀ s σ y = 0
  · rw [h0, norm_zero]; have := S.C₀_nonneg; positivity
  · have hy := S.Gfun_support ψ₀ s σ y h0
    unfold Gfun
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : |ψ₀.ψ₀ y| ≤ 1 := by rw [abs_of_nonneg (ψ₀.nonneg _)]; exact ψ₀.le_one _
    have h2 := S.norm_fourier_ψ₂_le (y * S.M * S.X * s / S.K)
    have h3 : Real.exp (-(2 * Real.pi * (y * S.M) * S.Y * s * Real.cosh σ)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := S.M_pos; have := S.Y_pos; have := Real.cosh_pos σ; have := Real.pi_pos
      have : 0 ≤ y := by linarith [hy.1]
      positivity
    have hC := S.C₀_nonneg
    calc |ψ₀.ψ₀ y| * ‖fourier S.ψ₂ (y * S.M * S.X * s / S.K)‖ *
          Real.exp (-(2 * Real.pi * (y * S.M) * S.Y * s * Real.cosh σ))
        ≤ 1 * (2 * S.C₀) * 1 := by gcongr
      _ = 2 * S.C₀ := by ring

theorem contDiff_ψ₀C : ContDiff ℝ ∞ (fun y : ℝ => (ψ₀.ψ₀ y : ℂ)) :=
  ofRealCLM.contDiff.comp ψ₀.smooth

theorem contDiff_fourier_conj : ContDiff ℝ ∞ (fourier (fun t => (starRingEnd ℂ) (S.ψ₂ t))) := by
  rw [fourier_eq_fourierIntegral]
  apply contDiff_fourier_of_support (S.hyp.smooth₂.continuous.star)
  intro t ht
  apply S.hyp.supp₂ t
  intro h; apply ht; simp [h]

theorem contDiff_Gfun (s σ : ℝ) : ContDiff ℝ ∞ (S.Gfun ψ₀ s σ) := by
  rw [S.Gfun_eq]
  apply ContDiff.mul (ContDiff.mul (contDiff_ψ₀C ψ₀) ?_) ?_
  · exact (S.contDiff_fourier_conj).comp (contDiff_const.mul contDiff_id)
  · exact Complex.contDiff_exp.comp (contDiff_const.mul (ofRealCLM.contDiff))

/-- Bounds for the derivatives of the three factors. -/
theorem norm_iteratedDeriv_fourier_conj_le (c : ℝ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (fun y : ℝ => fourier (fun t => (starRingEnd ℂ) (S.ψ₂ t)) (c * y)) y‖ ≤
      |c| ^ j * ((2 * Real.pi) ^ j * S.C₀ * 2) := by
  have hc : Continuous (fun t => (starRingEnd ℂ) (S.ψ₂ t)) := S.hyp.smooth₂.continuous.star
  have hs : ∀ t, (starRingEnd ℂ) (S.ψ₂ t) ≠ 0 → -1 ≤ t ∧ t ≤ 1 := by
    intro t ht; apply S.hyp.supp₂ t; intro h; apply ht; simp [h]
  have hB : ∀ t, ‖(starRingEnd ℂ) (S.ψ₂ t)‖ ≤ S.C₀ := fun t => by
    rw [RCLike.norm_conj]; exact S.norm_ψ₂_le t
  rw [fourier_eq_fourierIntegral, iteratedDeriv_comp_const_smul
    ((contDiff_fourier_of_support hc hs).of_le (by exact_mod_cast le_top)), norm_smul, norm_pow,
    Real.norm_eq_abs]
  gcongr
  exact norm_iteratedDeriv_fourier_le hc hs hB j _

theorem norm_iteratedDeriv_exp_le {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖iteratedDeriv k (fun y : ℝ => Complex.exp ((-lam : ℂ) * y)) y‖ ≤ 2 ^ k * k ! := by
  rw [iteratedDeriv_cexp_real, norm_mul, norm_pow, Complex.norm_exp]
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  -- `λ^k e^(-λy) ≤ λ^k e^(-λ/2) ≤ 2^k k!`
  have h1 : Real.exp (-(lam * y)) ≤ Real.exp (-(lam / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : (lam / 2) ^ k / k ! ≤ Real.exp (lam / 2) := by
    have := Real.pow_div_factorial_le_exp (x := lam / 2) (by positivity) k
    exact this
  have hf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h3 : lam ^ k * Real.exp (-(lam / 2)) ≤ 2 ^ k * k ! := by
    rw [div_le_iff₀ hf] at h2
    have e : lam ^ k = 2 ^ k * (lam / 2) ^ k := by rw [div_pow]; field_simp
    rw [e, Real.exp_neg]
    have hE := Real.exp_pos (lam / 2)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_inv_le_iff₀ hE]
    linarith
  calc lam ^ k * Real.exp (-(lam * y)) ≤ lam ^ k * Real.exp (-(lam / 2)) := by gcongr
    _ ≤ 2 ^ k * k ! := h3

/-- `MXs/K ≤ 2Q^η` for `s ≤ 1`, so `2π MXs/K ≤ 2L`. -/
theorem twoPi_MXs_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1) :
    2 * Real.pi * |-(S.M * S.X * s / S.K)| ≤ 2 * S.L := by
  have hM := S.M_pos
  have hX := S.X_pos
  have hK := S.K_pos
  rw [abs_neg, abs_of_nonneg (by positivity)]
  have h1 : S.M * S.X * s / S.K ≤ 2 * S.Q ^ S.η := by
    have h2 := S.XK_le
    have h3 : S.M * S.X * s / S.K ≤ S.M * (S.X / S.K) := by
      rw [show S.M * S.X * s / S.K = S.M * (S.X / S.K) * s by ring]
      exact mul_le_of_le_one_right (by positivity) hs
    calc S.M * S.X * s / S.K ≤ S.M * (S.X / S.K) := h3
      _ ≤ S.M * (2 * S.Q ^ S.η / S.M) := mul_le_mul_of_nonneg_left h2 hM.le
      _ = 2 * S.Q ^ S.η := by field_simp
  have h4 := S.L_ge
  have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
  have hQ := S.Qη_pos
  have hx0 : 0 ≤ S.M * S.X * s / S.K := by positivity
  have h5 := mul_le_mul hpi h1 hx0 (by norm_num)
  linarith

/-- **Derivative bounds for `G_{s,σ}`**: `|G_{s,σ}^(k)| ≤ C_G L^k` for `k ≤ 3`, `s ∈ [1/2, 1]`. -/
theorem exists_bound_Gfun (Cν : ℕ → ℝ) (ψ₀ : DyadicPartition) :
    ∃ CG : ℝ, 0 < CG ∧ ∀ (S : Setup Cν) (s : ℝ), s ∈ Icc (1 / 2 : ℝ) 1 → ∀ (σ : ℝ),
      ∀ k ≤ 3, ∀ y : ℝ, ‖iteratedDeriv k (S.Gfun ψ₀ s σ) y‖ ≤ CG * S.L ^ k := by
  have hψc : HasCompactSupport (fun y : ℝ => (ψ₀.ψ₀ y : ℂ)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2))
    intro y hy
    by_contra h
    exact hy (ψ₀.support y (by exact_mod_cast h))
  obtain ⟨Bψ, hBψ0, hBψ⟩ := exists_bound_iteratedDeriv_le (contDiff_ψ₀C ψ₀) hψc 3
  refine ⟨64 * 48 * (Bψ + 1) * (16 * |Cν 0| + 1), by positivity, ?_⟩
  intro S s hs σ k hk y
  have hL := S.one_le_L
  have hC := S.C₀_nonneg
  have hs0 : 0 ≤ s := by linarith [hs.1]
  set c : ℝ := -(S.M * S.X * s / S.K) with hc
  set lam : ℝ := 2 * Real.pi * S.M * S.Y * s * Real.cosh σ with hlam
  have hlam0 : 0 ≤ lam := by
    have := S.M_pos; have := S.Y_pos; have := Real.cosh_pos σ; have := Real.pi_pos
    rw [hlam]; positivity
  set A : ℝ → ℂ := fun y => (ψ₀.ψ₀ y : ℂ) with hA
  set Bf : ℝ → ℂ := fun y => fourier (fun t => (starRingEnd ℂ) (S.ψ₂ t)) (c * y) with hBf
  set Cf : ℝ → ℂ := fun y => Complex.exp ((-lam : ℂ) * y) with hCf
  have hG : S.Gfun ψ₀ s σ = fun y => A y * Bf y * Cf y := by
    rw [S.Gfun_eq]; ext y; simp only [hA, hBf, hCf, hc, hlam]; push_cast; ring_nf
  by_cases hy : y ∈ Ioi (1 / 2 : ℝ)
  · have hAc : ContDiffOn ℝ ∞ A (Ioi (1 / 2 : ℝ)) := (contDiff_ψ₀C ψ₀).contDiffOn
    have hBc : ContDiffOn ℝ ∞ Bf (Ioi (1 / 2 : ℝ)) :=
      ((S.contDiff_fourier_conj).comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hCc : ContDiffOn ℝ ∞ Cf (Ioi (1 / 2 : ℝ)) :=
      (Complex.contDiff_exp.comp (contDiff_const.mul ofRealCLM.contDiff)).contDiffOn
    -- bounds for the factors
    have hAb : ∀ j ≤ 3, ‖iteratedDeriv j A y‖ ≤ Bψ := fun j hj => hBψ j hj y
    have hBb : ∀ m ≤ 3, ‖iteratedDeriv m Bf y‖ ≤ 2 * S.C₀ * (2 * S.L) ^ m := by
      intro m _
      have h1 := S.norm_iteratedDeriv_fourier_conj_le c m y
      have h2 := S.twoPi_MXs_le hs0 hs.2
      have h3 : |c| ^ m * ((2 * Real.pi) ^ m * S.C₀ * 2) = 2 * S.C₀ * (2 * Real.pi * |c|) ^ m := by
        ring
      rw [h3] at h1
      refine h1.trans ?_
      gcongr
    have hCb : ∀ m ≤ 3, ‖iteratedDeriv m Cf y‖ ≤ 48 := by
      intro m hm
      have h1 := norm_iteratedDeriv_exp_le hlam0 m (y := y) (le_of_lt hy)
      refine h1.trans ?_
      have : (2 : ℝ) ^ m * m ! ≤ 2 ^ 3 * 3 ! := by
        have h2 : (2 : ℝ) ^ m ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hm
        have h3 : (m ! : ℝ) ≤ 3 ! := by exact_mod_cast Nat.factorial_le hm
        exact mul_le_mul h2 h3 (by positivity) (by positivity)
      refine this.trans ?_
      norm_num [Nat.factorial]
    -- Leibniz for `A Bf`
    have hAB : ∀ i ≤ 3, ‖iteratedDeriv i (fun y => A y * Bf y) y‖ ≤
        2 ^ i * (Bψ * (2 * S.C₀ * (2 * S.L) ^ i)) := by
      intro i hi
      refine (norm_iteratedDeriv_mul_le_of_isOpen isOpen_Ioi hAc hBc hy i).trans ?_
      have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedDeriv j A y‖ *
          ‖iteratedDeriv (i - j) Bf y‖ ≤
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (Bψ * (2 * S.C₀ * (2 * S.L) ^ i)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have h1 := hAb j (by omega)
        have h2 := hBb (i - j) (by omega)
        have h3 : (2 * S.L) ^ (i - j) ≤ (2 * S.L) ^ i := pow_le_pow_right₀ (by linarith) (by omega)
        calc ‖iteratedDeriv j A y‖ * ‖iteratedDeriv (i - j) Bf y‖
            ≤ Bψ * (2 * S.C₀ * (2 * S.L) ^ (i - j)) :=
              mul_le_mul h1 h2 (norm_nonneg _) hBψ0
          _ ≤ Bψ * (2 * S.C₀ * (2 * S.L) ^ i) := by gcongr
      refine hsum.trans (le_of_eq ?_)
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose i
    have hABc : ContDiffOn ℝ ∞ (fun y => A y * Bf y) (Ioi (1 / 2 : ℝ)) := hAc.mul hBc
    rw [hG]
    refine (norm_iteratedDeriv_mul_le_of_isOpen isOpen_Ioi hABc hCc hy k).trans ?_
    have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedDeriv i (fun y => A y * Bf y) y‖ * ‖iteratedDeriv (k - i) Cf y‖ ≤
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          (2 ^ k * (Bψ * (2 * S.C₀ * (2 * S.L) ^ k)) * 48) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h1 := hAB i (by omega)
      have h2 := hCb (k - i) (by omega)
      have h3 : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi'
      have h4 : (2 * S.L) ^ i ≤ (2 * S.L) ^ k := pow_le_pow_right₀ (by linarith) hi'
      calc ‖iteratedDeriv i (fun y => A y * Bf y) y‖ * ‖iteratedDeriv (k - i) Cf y‖
          ≤ 2 ^ i * (Bψ * (2 * S.C₀ * (2 * S.L) ^ i)) * 48 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ 2 ^ k * (Bψ * (2 * S.C₀ * (2 * S.L) ^ k)) * 48 := by gcongr
    refine hsum.trans ?_
    rw [← Finset.sum_mul, show (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k by
      exact_mod_cast Nat.sum_range_choose k]
    have hk2 : (2 : ℝ) ^ k ≤ 8 := by
      calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
        _ = 8 := by norm_num
    have hC0 : S.C₀ = |Cν 0| := rfl
    rw [mul_pow]
    have hLk : 0 ≤ S.L ^ k := by positivity
    have h2k : 0 ≤ (2 : ℝ) ^ k := by positivity
    have h512 : 2 ^ k * 2 ^ k * 2 ^ k ≤ (8 : ℝ) * 8 * 8 := by
      have := mul_le_mul hk2 hk2 h2k (by norm_num)
      exact mul_le_mul this hk2 h2k (by norm_num)
    have hX : 0 ≤ 48 * Bψ * (2 * S.C₀) * S.L ^ k := by positivity
    calc 2 ^ k * (2 ^ k * (Bψ * (2 * S.C₀ * (2 ^ k * S.L ^ k))) * 48)
        = (2 ^ k * 2 ^ k * 2 ^ k) * (48 * Bψ * (2 * S.C₀) * S.L ^ k) := by ring
      _ ≤ (8 * 8 * 8) * (48 * Bψ * (2 * S.C₀) * S.L ^ k) := mul_le_mul_of_nonneg_right h512 hX
      _ = 64 * 48 * Bψ * (16 * S.C₀) * S.L ^ k := by ring
      _ ≤ 64 * 48 * (Bψ + 1) * (16 * |Cν 0| + 1) * S.L ^ k := by
          rw [hC0]
          have hcabs := abs_nonneg (Cν 0)
          gcongr
          · linarith
          · linarith
  · -- outside `(1/2, ∞)` the function vanishes near `y`
    have hns : y ∉ tsupport (S.Gfun ψ₀ s σ) := by
      intro hmem
      have := tsupport_subset_Icc_of_support (fun u hu => by
        have := S.Gfun_support ψ₀ s σ u hu; exact ⟨this.1.le, this.2⟩) hmem
      simp only [mem_Ioi, not_lt] at hy
      linarith [this.1]
    rw [iteratedDeriv_eq_zero_of_notMem_tsupport hns, norm_zero]
    positivity

end Setup

end Triples
