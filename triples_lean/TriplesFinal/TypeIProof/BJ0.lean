import TriplesFinal.TypeIProof.Setup
import TriplesFinal.TypeIProof.Psi
import TriplesFinal.Poisson.FourierBump
import TriplesFinal.Analysis.MeasureTools

/-!
# The coefficients `B(ω)` of the spectral expansion of `Ξ_M`

For a spectral point with parameter `t` and Fourier coefficients `ρ`,
`B = ∑_h ψ₀(h/M) conj(ρ(h)) ǧ_h(t) = (X/K) Y^(-1/2) ∑_h ψ₀(h/M) conj(ρ(h)) Ψ_h(t)`.
This file proves the pointwise bounds for `|B|²` on the spectrum `𝒥₀` (`|Im t| ≤ 1/2`):
`|B|² ≤ m₀`, where `m₀` involves the sums `S(ρ, s, σ) = ∑_h G_{s,σ}(h/M) ρ(h)` with
`G_{s,σ}(y) = ψ₀(y) conj(ψ̂₂(yMXs/K)) e^(-2πyMYs cosh σ)`, whose coefficients do not depend on `t`.

Paper: §12.2.
-/

namespace Triples

open Complex MeasureTheory Set
open scoped ContDiff Interval

namespace DyadicPartition

variable (ψ₀ : DyadicPartition)

theorem le_one (y : ℝ) : ψ₀.ψ₀ y ≤ 1 := by
  by_cases hy : 0 < y
  · have h := ψ₀.sum_eq_one y hy
    have := le_hasSum h 0 (fun i _ => ψ₀.nonneg _)
    simpa using this
  · by_contra hne
    push Not at hne
    have := ψ₀.support y (by linarith)
    linarith [this.1]

theorem eq_zero_of_lt_one {y : ℝ} (hy : y < 1) : ψ₀.ψ₀ y = 0 := by
  by_contra h
  exact absurd (ψ₀.support y h).1 (not_le.2 hy)

theorem eq_zero_of_le_one {y : ℝ} (hy : y ≤ 1) : ψ₀.ψ₀ y = 0 := by
  rcases lt_or_eq_of_le hy with h | h
  · exact ψ₀.eq_zero_of_lt_one h
  · subst h
    by_contra hne
    have hc : ContinuousAt ψ₀.ψ₀ 1 := ψ₀.smooth.continuous.continuousAt
    have hev := hc.eventually_ne hne
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    have := hball (y := 1 - ε / 2) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact this (ψ₀.eq_zero_of_lt_one (by linarith))

theorem lt_of_ne_zero {y : ℝ} (h : ψ₀.ψ₀ y ≠ 0) : 1 < y ∧ y ≤ 2 := by
  refine ⟨?_, (ψ₀.support y h).2⟩
  by_contra hle
  exact h (ψ₀.eq_zero_of_le_one (not_lt.1 hle))

end DyadicPartition

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

/-- The frequencies `1 ≤ h ≤ 2M`. -/
noncomputable def Hs : Finset ℕ := Finset.Icc 1 ⌊2 * S.M⌋₊

theorem card_Hs_le : ((S.Hs).card : ℝ) ≤ 2 * S.M := by
  unfold Hs
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  exact Nat.floor_le (by linarith [S.hM1])

theorem le_of_mem_Hs {h : ℕ} (hh : h ∈ S.Hs) : 1 ≤ h ∧ (h : ℝ) ≤ 2 * S.M := by
  unfold Hs at hh
  rw [Finset.mem_Icc] at hh
  exact ⟨hh.1, (Nat.le_floor_iff (by linarith [S.hM1])).1 hh.2⟩

/-- If `ψ₀(h/M) ≠ 0` then `M < h ≤ 2M`. -/
theorem lt_of_ψ₀_ne_zero {h : ℝ} (hh : ψ₀.ψ₀ (h / S.M) ≠ 0) : S.M < h ∧ h ≤ 2 * S.M := by
  have := ψ₀.lt_of_ne_zero hh
  have hM := S.M_pos
  rw [lt_div_iff₀ hM, one_mul] at this
  rw [div_le_iff₀ hM] at this
  exact ⟨this.1, by linarith [this.2]⟩

/-- The constant `|C₀|` bounding `ψ₁` and `ψ₂`. -/
noncomputable def C₀ (_ : Setup Cν) : ℝ := |Cν 0|

theorem C₀_nonneg : 0 ≤ S.C₀ := abs_nonneg _

theorem norm_ψ₁_le (t : ℝ) : ‖S.ψ₁ t‖ ≤ S.C₀ := by
  have := S.hyp.deriv₁ 0 t
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
  exact this.trans (le_abs_self _)

theorem norm_ψ₂_le (t : ℝ) : ‖S.ψ₂ t‖ ≤ S.C₀ := by
  have := S.hyp.deriv₂ 0 t
  simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
  exact this.trans (le_abs_self _)

theorem norm_fourier_ψ₂_le (ξ : ℝ) : ‖fourier S.ψ₂ ξ‖ ≤ 2 * S.C₀ := by
  have h := norm_fourier_le S.hyp.smooth₂ S.hyp.supp₂ (k := 0)
    (fun t => by simpa using S.norm_ψ₂_le t) ξ
  simpa using h

theorem norm_w1_le' {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) : ‖w1 S.ψ₁ s‖ ≤ 2 * S.C₀ :=
  norm_w1_le S.norm_ψ₁_le hs

theorem norm_gMh_le (h : ℝ) {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    ‖gMh S.ψ₁ S.ψ₂ S.X S.K h s‖ ≤ 4 * S.C₀ ^ 2 := by
  unfold gMh ah
  rw [norm_mul]
  calc ‖w1 S.ψ₁ s‖ * ‖fourier S.ψ₂ (h * S.X * s / S.K)‖ ≤ (2 * S.C₀) * (2 * S.C₀) :=
        mul_le_mul (S.norm_w1_le' hs) (S.norm_fourier_ψ₂_le _) (norm_nonneg _)
          (by have := S.C₀_nonneg; positivity)
    _ = 4 * S.C₀ ^ 2 := by ring

/-- `B(ρ, t) = ∑_h ψ₀(h/M) conj(ρ(h)) ǧ_h(t)`. -/
noncomputable def B (ρ : ℕ → ℂ) (t : ℂ) : ℂ :=
  ∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) *
    besselTransform (gh S.E S.H S.X S.K S.ψ₁ S.ψ₂ h) h t

theorem B_eq (ρ : ℕ → ℂ) (t : ℂ) :
    S.B ψ₀ ρ t = (S.Bk : ℂ) * ∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) *
      PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t := by
  unfold B
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [besselTransform_gh S.E_pos S.hyp.hH S.K_pos S.hyp.supp₁ h t]
  unfold Bk Y
  ring

/-- `G_{s,σ}(y) = ψ₀(y) conj(ψ̂₂(yMXs/K)) e^(-2π yM Y s cosh σ)`. -/
noncomputable def Gfun (s σ y : ℝ) : ℂ :=
  (ψ₀.ψ₀ y : ℂ) * (starRingEnd ℂ) (fourier S.ψ₂ (y * S.M * S.X * s / S.K)) *
    (Real.exp (-(2 * Real.pi * (y * S.M) * S.Y * s * Real.cosh σ)) : ℂ)

/-- `S(ρ, s, σ) = ∑_h G_{s,σ}(h/M) ρ(h)`. -/
noncomputable def Ssum (ρ : ℕ → ℂ) (s σ : ℝ) : ℂ :=
  ∑ h ∈ S.Hs, S.Gfun ψ₀ s σ (h / S.M) * ρ h

/-- `ε₀ = (4C₀²/(πMY)) e^(-πMYV/2)`, the error from the tails of the `σ`-integrals. -/
noncomputable def eps0 : ℝ :=
  4 * S.C₀ ^ 2 / (Real.pi * S.M * S.Y) * Real.exp (-(Real.pi * S.M * S.Y * S.V / 2))

theorem eps0_nonneg : 0 ≤ S.eps0 := by
  unfold eps0
  have := S.MY_pos
  have := S.C₀_nonneg
  have hpi := Real.pi_pos
  have : 0 < Real.pi * S.M * S.Y := by rw [mul_assoc]; positivity
  positivity

/-- The majorant `m₀` of `|B|²` on `𝒥₀`. -/
noncomputable def m0 (ρ : ℕ → ℂ) (t : ℂ) : ℝ :=
  2 * S.Bk ^ 2 * (S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) *
      (∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ, ‖S.Ssum ψ₀ ρ s σ‖ ^ 2) +
    2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2)

theorem continuous_fourier_ψ₂ : Continuous (fourier S.ψ₂) := by
  rw [fourier_eq_fourierIntegral]
  exact (contDiff_fourier_of_support S.hyp.smooth₂.continuous S.hyp.supp₂).continuous

theorem continuous_gMh (h : ℝ) : Continuous (gMh S.ψ₁ S.ψ₂ S.X S.K h) :=
  (contDiff_gMh S.hyp.smooth₁ S.hyp.supp₁ S.hyp.smooth₂.continuous S.hyp.supp₂ S.X S.K h).continuous

theorem continuous_Gfun (y : ℝ) : Continuous (fun p : ℝ × ℝ => S.Gfun ψ₀ p.1 p.2 y) := by
  unfold Gfun
  have h1 := S.continuous_fourier_ψ₂
  fun_prop

theorem continuous_Ssum (ρ : ℕ → ℂ) : Continuous (fun p : ℝ × ℝ => S.Ssum ψ₀ ρ p.1 p.2) := by
  unfold Ssum
  exact continuous_finsetSum _ fun h _ => (S.continuous_Gfun ψ₀ _).mul continuous_const

theorem PsiH_J0_setup {h : ℕ} (hh : S.M < h) {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    ∃ r : ℂ, ‖r‖ ≤ S.eps0 ∧ PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t =
      (1 / 2 : ℂ) * (∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ,
        gMh S.ψ₁ S.ψ₂ S.X S.K h s *
          ((Real.exp (-(2 * Real.pi * h * S.Y * s * Real.cosh σ)) : ℂ) *
            Complex.exp (I * t * σ))) + r := by
  have hM := S.M_pos
  have hY := S.Y_pos
  have hpi := Real.pi_pos
  obtain ⟨r, hr, heq⟩ := PsiH_J0 S.hyp.smooth₁ S.hyp.supp₁ S.hyp.smooth₂.continuous
    S.hyp.supp₂ hY (h := (h : ℝ)) (by linarith) ht S.ℓ_pos.le (y₀ := Real.pi * S.M * S.Y)
    (by positivity) (by
      have : Real.pi * S.M * S.Y ≤ Real.pi * h * S.Y := by
        apply mul_le_mul_of_nonneg_right _ hY.le
        exact mul_le_mul_of_nonneg_left hh.le hpi.le
      exact this) (A := 4 * S.C₀ ^ 2) (fun s hs => S.norm_gMh_le h hs)
  refine ⟨r, ?_, heq⟩
  rw [S.exp_ℓ] at hr
  unfold eps0
  convert hr using 3

theorem norm_cexp_I_mul_le {t : ℂ} {σ ℓ : ℝ} (hσ : |σ| ≤ ℓ) :
    ‖Complex.exp (I * t * σ)‖ ≤ Real.exp (|t.im| * ℓ) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  simp only [mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero, one_mul,
    zero_sub, mul_im]
  have h1 : -(t.im * σ) ≤ |t.im| * |σ| := by
    rw [← abs_mul]; exact neg_le_abs _
  have h2 : |t.im| * |σ| ≤ |t.im| * ℓ := mul_le_mul_of_nonneg_left hσ (abs_nonneg _)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The pointwise bound on `𝒥₀`**: `|B(ρ, t)|² ≤ m₀(ρ, t)` for `|Im t| ≤ 1/2`. -/
theorem normSq_B_le_m0 (ρ : ℕ → ℂ) {t : ℂ} (ht : |t.im| ≤ 1 / 2) :
    ‖S.B ψ₀ ρ t‖ ^ 2 ≤ S.m0 ψ₀ ρ t := by
  have hM := S.M_pos
  have hY := S.Y_pos
  have hℓ := S.ℓ_pos
  have hC := S.C₀_nonneg
  set E : ℕ → ℝ → ℝ → ℂ := fun h s σ =>
    (Real.exp (-(2 * Real.pi * h * S.Y * s * Real.cosh σ)) : ℂ) * Complex.exp (I * t * σ) with hE
  set Ih : ℕ → ℂ := fun h => ∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ,
    gMh S.ψ₁ S.ψ₂ S.X S.K h s * E h s σ with hIh
  -- the decomposition of each `Ψ_h`
  have hdec : ∀ h : ℕ, ∃ r : ℂ, (ψ₀.ψ₀ (h / S.M) ≠ 0 → ‖r‖ ≤ S.eps0) ∧
      (ψ₀.ψ₀ (h / S.M) : ℂ) * PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t =
        (ψ₀.ψ₀ (h / S.M) : ℂ) * ((1 / 2 : ℂ) * Ih h + r) := by
    intro h
    by_cases h0 : ψ₀.ψ₀ (h / S.M) = 0
    · exact ⟨0, fun h' => absurd h0 h', by rw [h0]; simp⟩
    · obtain ⟨r, hr, heq⟩ := S.PsiH_J0_setup (S.lt_of_ψ₀_ne_zero ψ₀ h0).1 ht
      exact ⟨r, fun _ => hr, by rw [heq]⟩
  choose r hr hreq using hdec
  set c : ℕ → ℂ := fun h => (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) with hc
  set Main : ℂ := ∑ h ∈ S.Hs, c h * Ih h with hMain
  set Rem : ℂ := ∑ h ∈ S.Hs, c h * r h with hRem
  have hB : S.B ψ₀ ρ t = (S.Bk : ℂ) * ((1 / 2 : ℂ) * Main + Rem) := by
    rw [S.B_eq]
    congr 1
    rw [hMain, hRem, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    have := hreq h
    calc (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (ρ h) * PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t
        = (starRingEnd ℂ) (ρ h) * ((ψ₀.ψ₀ (h / S.M) : ℂ) * PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t) := by
          ring
      _ = (starRingEnd ℂ) (ρ h) * ((ψ₀.ψ₀ (h / S.M) : ℂ) * ((1 / 2 : ℂ) * Ih h + r h)) := by
          rw [this]
      _ = _ := by simp only [hc]; ring
  -- continuity of the integrands
  set f : ℕ → ℝ → ℝ → ℂ := fun h s σ => gMh S.ψ₁ S.ψ₂ S.X S.K h s * E h s σ with hf
  have hfc : ∀ h : ℕ, Continuous (Function.uncurry (f h)) := by
    intro h
    have := S.continuous_gMh h
    simp only [hf, hE]
    fun_prop
  have hfσ : ∀ h : ℕ, ∀ s : ℝ, IntervalIntegrable (f h s) volume (-S.ℓ) S.ℓ := fun h s =>
    ((hfc h).comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  have hfs : ∀ h : ℕ, IntervalIntegrable (fun s => ∫ σ in (-S.ℓ)..S.ℓ, f h s σ) volume (1 / 2) 1 :=
    fun h => (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hfc h) _ _
      ).intervalIntegrable _ _
  -- the main term as a double integral
  set F : ℝ → ℝ → ℂ := fun s σ =>
    w1 S.ψ₁ s * Complex.exp (I * t * σ) * (starRingEnd ℂ) (S.Ssum ψ₀ ρ s σ) with hF
  have hpt : ∀ s σ, ∑ h ∈ S.Hs, c h * f h s σ = F s σ := by
    intro s σ
    simp only [hF, Setup.Ssum, map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    simp only [hc, hf, hE, Setup.Gfun, gMh, ah, map_mul, Complex.conj_ofReal, RCLike.conj_conj]
    have hMne : S.M ≠ 0 := hM.ne'
    have e1 : (h : ℝ) / S.M * S.M = h := by field_simp
    rw [e1]
    ring
  have hMain_eq : Main = ∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ, F s σ := by
    rw [hMain]
    simp only [hIh]
    have h1 : ∀ h ∈ S.Hs, c h * ∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ, f h s σ =
        ∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ, c h * f h s σ := by
      intro h _
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext s
      rw [← intervalIntegral.integral_const_mul]
    have hcf : ∀ h, Continuous (Function.uncurry fun s σ => c h * f h s σ) := fun h =>
      (continuous_const (y := c h)).mul (hfc h)
    rw [Finset.sum_congr rfl h1, ← intervalIntegral.integral_finsetSum
      (fun h _ => (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (hcf h) _ _).intervalIntegrable _ _)]
    congr 1; ext s
    rw [← intervalIntegral.integral_finsetSum (fun h _ => (hfσ h s).const_mul (c h))]
    congr 1; ext σ
    exact hpt s σ
  -- the bounds
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous (Function.uncurry fun s σ => ∑ h ∈ S.Hs, c h * f h s σ) := by
      simp only [Function.uncurry_def]
      exact continuous_finsetSum _ fun h _ => continuous_const.mul (hfc h)
    convert h1 using 1
    ext p
    simp only [Function.uncurry_def]
    rw [hpt]
  set G : ℝ → ℂ := fun s => ∫ σ in (-S.ℓ)..S.ℓ, F s σ with hG
  have hGc : Continuous G :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc _ _
  have hSc := S.continuous_Ssum ψ₀ ρ
  set Ssq : ℝ → ℝ := fun s => ∫ σ in (-S.ℓ)..S.ℓ, ‖S.Ssum ψ₀ ρ s σ‖ ^ 2 with hSsq
  have hSsqc : Continuous Ssq := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hSc.norm).pow 2
  have hVpow : ∀ σ, |σ| ≤ S.ℓ → ‖Complex.exp (I * t * σ)‖ ^ 2 ≤ S.V ^ (2 * |t.im|) := by
    intro σ hσ
    have h1 := norm_cexp_I_mul_le (t := t) hσ
    have h2 : Real.exp (|t.im| * S.ℓ) ^ 2 = S.V ^ (2 * |t.im|) := by
      rw [← S.exp_ℓ, ← Real.exp_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hFle : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ, |σ| ≤ S.ℓ →
      ‖F s σ‖ ^ 2 ≤ (2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) * ‖S.Ssum ψ₀ ρ s σ‖ ^ 2 := by
    intro s hs σ hσ
    simp only [hF]
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_pow, mul_pow]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (S.norm_w1_le' hs) 2
    have h2 := hVpow σ hσ
    have h3 : 0 ≤ ‖S.Ssum ψ₀ ρ s σ‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ S.V ^ (2 * |t.im|) := by have := S.V_pos; positivity
    gcongr
  have hGle : ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      ‖G s‖ ^ 2 ≤ 2 * S.ℓ * ((2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) * Ssq s) := by
    intro s hs
    have hFσ : Continuous (F s) := by
      have h1 := hSc.comp (Continuous.prodMk (continuous_const (y := s)) continuous_id)
      simp only [hF]
      exact (continuous_const.mul (by fun_prop)).mul (Complex.continuous_conj.comp h1)
    have h1 := norm_intervalIntegral_sq_le (a := -S.ℓ) (b := S.ℓ) (by linarith)
      (hFσ.intervalIntegrable _ _) ((hFσ.norm.pow 2).intervalIntegrable _ _)
    rw [show S.ℓ - -S.ℓ = 2 * S.ℓ by ring] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    simp only [hSsq]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith) ((hFσ.norm.pow 2).intervalIntegrable _ _)
      ((((hSc.comp (Continuous.prodMk continuous_const continuous_id)).norm).pow 2).const_mul
        _ |>.intervalIntegrable _ _)
    intro σ hσ
    exact hFle s hs σ (abs_le.2 ⟨by linarith [hσ.1], hσ.2⟩)
  have hMain_le : ‖Main‖ ^ 2 ≤ S.ℓ * (2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) *
      ∫ s in (1 / 2 : ℝ)..1, Ssq s := by
    rw [hMain_eq]
    have h1 := norm_intervalIntegral_sq_le (a := 1 / 2) (b := 1) (by norm_num)
      (hGc.intervalIntegrable _ _) ((hGc.norm.pow 2).intervalIntegrable _ _)
    refine h1.trans ?_
    have h2 : ∫ s in (1 / 2 : ℝ)..1, ‖G s‖ ^ 2 ≤
        ∫ s in (1 / 2 : ℝ)..1, 2 * S.ℓ * ((2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) * Ssq s) :=
      intervalIntegral.integral_mono_on (by norm_num) ((hGc.norm.pow 2).intervalIntegrable _ _)
        ((continuous_const.mul (continuous_const.mul hSsqc)).intervalIntegrable _ _) hGle
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h2
    have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [this]
    nlinarith
  have hRem_le : ‖Rem‖ ^ 2 ≤ 2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
    have h1 : ‖Rem‖ ≤ ∑ h ∈ S.Hs, S.eps0 * ‖ρ h‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
      simp only [hc]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
      by_cases h0 : ψ₀.ψ₀ (h / S.M) = 0
      · rw [h0, abs_zero, zero_mul, zero_mul]
        exact mul_nonneg S.eps0_nonneg (norm_nonneg _)
      · have h2 := hr h h0
        have h3 : |ψ₀.ψ₀ (h / S.M)| ≤ 1 := by
          rw [abs_of_nonneg (ψ₀.nonneg _)]; exact ψ₀.le_one _
        calc |ψ₀.ψ₀ (h / S.M)| * ‖ρ h‖ * ‖r h‖ ≤ 1 * ‖ρ h‖ * S.eps0 := by gcongr
          _ = S.eps0 * ‖ρ h‖ := by ring
    have h2 : (∑ h ∈ S.Hs, S.eps0 * ‖ρ h‖) ^ 2 ≤
        (S.Hs).card * ∑ h ∈ S.Hs, (S.eps0 * ‖ρ h‖) ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq S.Hs (fun _ => (1 : ℝ)) (fun h => S.eps0 * ‖ρ h‖)
      simpa using this
    have h3 : (S.Hs).card * ∑ h ∈ S.Hs, (S.eps0 * ‖ρ h‖) ^ 2 =
        (S.Hs).card * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
      have e : ∑ h ∈ S.Hs, (S.eps0 * ‖ρ h‖) ^ 2 = S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring
      rw [e]; ring
    have h4 : 0 ≤ S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by positivity
    have h5 := S.card_Hs_le
    have h6 : ‖Rem‖ ^ 2 ≤ (∑ h ∈ S.Hs, S.eps0 * ‖ρ h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h7 : (S.Hs).card * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 ≤
        2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2 := by
      rw [mul_assoc, mul_assoc (2 * S.M)]
      exact mul_le_mul_of_nonneg_right h5 h4
    linarith
  -- conclusion
  rw [hB, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg S.Bk_pos.le]
  have hsum : ‖(1 / 2 : ℂ) * Main + Rem‖ ^ 2 ≤ 2 * (1 / 4 * ‖Main‖ ^ 2) + 2 * ‖Rem‖ ^ 2 := by
    have h1 : ‖(1 / 2 : ℂ) * Main + Rem‖ ≤ 1 / 2 * ‖Main‖ + ‖Rem‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul]; norm_num
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (1 / 2 * ‖Main‖ - ‖Rem‖)]
  unfold m0
  have hBk2 : 0 ≤ S.Bk ^ 2 := sq_nonneg _
  calc S.Bk ^ 2 * ‖(1 / 2 : ℂ) * Main + Rem‖ ^ 2
      ≤ S.Bk ^ 2 * (2 * (1 / 4 * ‖Main‖ ^ 2) + 2 * ‖Rem‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hBk2
    _ ≤ S.Bk ^ 2 * (2 * (1 / 4 * (S.ℓ * (2 * S.C₀) ^ 2 * S.V ^ (2 * |t.im|) *
          ∫ s in (1 / 2 : ℝ)..1, Ssq s)) + 2 * (2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2)) := by
        gcongr
    _ = _ := by simp only [hSsq]; ring

end Setup

end Triples
