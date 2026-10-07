import TriplesFinal.TypeIProof.BlockJ1Main

/-!
# The remainder terms on `𝒥₁`: the annuli `R < |t| ≤ R₁`

On the real spectrum, the remainder `Bᴿ` of the Mellin–Barnes splitting is bounded through its
majorant `mᴿ` (`normSq_Brem_le`). Stirling's bound for `G_τ` and Peetre's inequality give
`|G_τ(-3/2 + iξ)|² cosh(πτ) ≤ C² (1+|ξ|)^5 (1+|τ|)^(-5)`; exchanging the `ξ`-integral with the
spectral integral (Fubini) and applying the large sieve inequality for each `ξ`:
`∫_{R < |t| ≤ R₁} mᴿ ≤ (X/K)² Y^(-1) (c₂/4π²) C² (1+R)^(-5) C(η)(R₁² + M^(1+η)/q)
  2M ((4πMY)^(3/2) C₆)² c₅`, with `c₅ = ∫ (1+|ξ|)^(-5) dξ`.

Paper: §12.4.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

/-- Peetre's inequality: `(1+|τ|)² ≤ (1+|ξ+τ|)(1+|ξ-τ|)(1+|ξ|)²`. -/
theorem peetre_two (ξ τ : ℝ) :
    (1 + |τ|) ^ 2 ≤ (1 + |ξ + τ|) * (1 + |ξ - τ|) * (1 + |ξ|) ^ 2 := by
  have h1 : 1 + |τ| ≤ (1 + |ξ + τ|) * (1 + |ξ|) := by
    have h := abs_sub_abs_le_abs_sub τ (ξ + τ)
    rw [show τ - (ξ + τ) = -ξ by ring, abs_neg] at h
    nlinarith [abs_nonneg (ξ + τ), abs_nonneg ξ]
  have h2 : 1 + |τ| ≤ (1 + |ξ - τ|) * (1 + |ξ|) := by
    have h := abs_sub_abs_le_abs_sub τ (τ - ξ)
    rw [show τ - (τ - ξ) = ξ by ring, abs_sub_comm τ ξ] at h
    nlinarith [abs_nonneg (ξ - τ), abs_nonneg ξ]
  have h0 : 0 ≤ 1 + |τ| := by positivity
  calc (1 + |τ|) ^ 2 = (1 + |τ|) * (1 + |τ|) := sq _
    _ ≤ ((1 + |ξ + τ|) * (1 + |ξ|)) * ((1 + |ξ - τ|) * (1 + |ξ|)) :=
        mul_le_mul h1 h2 h0 (by positivity)
    _ = _ := by ring

theorem cosh_le_exp_abs (y : ℝ) : Real.cosh y ≤ Real.exp |y| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp y ≤ Real.exp |y| := Real.exp_le_exp.2 (le_abs_self y)
  have h2 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.2 (neg_le_abs y)
  linarith

/-- **Stirling and Peetre**: `|G_τ(-3/2 + iξ)|² cosh(πτ) ≤ C² (1+|ξ|)^5 (1+|τ|)^(-5)`. -/
theorem Gt_sq_mul_cosh_le {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    (τ ξ : ℝ) :
    ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * Real.cosh (Real.pi * τ) ≤
      CGt ^ 2 * ((1 + |ξ|) ^ (5 : ℝ) * (1 + |τ|) ^ (-(5 : ℝ))) := by
  set a := 1 + |ξ + τ| with ha
  set b := 1 + |ξ - τ| with hb
  set u := 1 + |ξ| with hu
  set v := 1 + |τ| with hv
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hu0 : 0 < u := by positivity
  have hv0 : 0 < v := by positivity
  have hG := hGt τ ξ
  have hG2 : ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 ≤
      (CGt * Real.exp (-Real.pi * |τ| / 2) * a ^ (-(5 : ℝ) / 4) * b ^ (-(5 : ℝ) / 4)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hG 2
  have e1 : (CGt * Real.exp (-Real.pi * |τ| / 2) * a ^ (-(5 : ℝ) / 4) * b ^ (-(5 : ℝ) / 4)) ^ 2 =
      CGt ^ 2 * Real.exp (-(Real.pi * |τ|)) * (a * b) ^ (-(5 : ℝ) / 2) := by
    have ea : (a ^ (-(5 : ℝ) / 4)) ^ 2 = a ^ (-(5 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]; norm_num
    have eb : (b ^ (-(5 : ℝ) / 4)) ^ 2 = b ^ (-(5 : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; norm_num
    have ee : Real.exp (-Real.pi * |τ| / 2) ^ 2 = Real.exp (-(Real.pi * |τ|)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [mul_pow, mul_pow, mul_pow, ea, eb, ee, Real.mul_rpow ha0.le hb0.le]
    ring
  have hch : Real.cosh (Real.pi * τ) ≤ Real.exp (Real.pi * |τ|) := by
    have := cosh_le_exp_abs (Real.pi * τ)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have hpeetre : v ^ (2 : ℝ) * u ^ (-(2 : ℝ)) ≤ a * b := by
    have hp := peetre_two ξ τ
    rw [Real.rpow_neg hu0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have e2 : v ^ (2 : ℝ) = v ^ 2 := by exact_mod_cast Real.rpow_natCast v 2
    have e3 : u ^ (2 : ℝ) = u ^ 2 := by exact_mod_cast Real.rpow_natCast u 2
    rw [e2, e3]
    exact hp
  have hlow : 0 < v ^ (2 : ℝ) * u ^ (-(2 : ℝ)) := by positivity
  have hab : (a * b) ^ (-(5 : ℝ) / 2) ≤ u ^ (5 : ℝ) * v ^ (-(5 : ℝ)) := by
    calc (a * b) ^ (-(5 : ℝ) / 2) ≤ (v ^ (2 : ℝ) * u ^ (-(2 : ℝ))) ^ (-(5 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos hlow hpeetre (by norm_num)
      _ = u ^ (5 : ℝ) * v ^ (-(5 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hv0.le,
            ← Real.rpow_mul hu0.le]
          norm_num
          ring
  have hexp : Real.exp (-(Real.pi * |τ|)) * Real.exp (Real.pi * |τ|) = 1 := by
    rw [← Real.exp_add]; simp
  have hc0 : 0 ≤ Real.cosh (Real.pi * τ) := (Real.cosh_pos _).le
  calc ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * Real.cosh (Real.pi * τ)
      ≤ (CGt ^ 2 * Real.exp (-(Real.pi * |τ|)) * (a * b) ^ (-(5 : ℝ) / 2)) *
          Real.exp (Real.pi * |τ|) := by
        rw [← e1]
        exact mul_le_mul hG2 hch hc0 (by positivity)
    _ = CGt ^ 2 * (a * b) ^ (-(5 : ℝ) / 2) * (Real.exp (-(Real.pi * |τ|)) *
          Real.exp (Real.pi * |τ|)) := by ring
    _ = CGt ^ 2 * (a * b) ^ (-(5 : ℝ) / 2) := by rw [hexp, mul_one]
    _ ≤ CGt ^ 2 * (u ^ (5 : ℝ) * v ^ (-(5 : ℝ))) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg _)

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- The coefficients of `D(ρ, ξ)` as a linear form in `ρ`. -/
noncomputable def dcoef (ξ : ℝ) (h : ℕ) : ℂ :=
  (starRingEnd ℂ) ((ψ₀.ψ₀ (h / S.M) : ℂ) *
    ((2 * Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * ξ)) *
      Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ))

theorem norm_Dsum_eq (ρ : ℕ → ℂ) (ξ : ℝ) :
    ‖S.Dsum ψ₀ ρ ξ‖ = ‖∑ h ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, S.dcoef ψ₀ ξ h * ρ h‖ := by
  rw [← RCLike.norm_conj (∑ h ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, S.dcoef ψ₀ ξ h * ρ h)]
  congr 1
  rw [map_sum]
  unfold Dsum Hs
  apply Finset.sum_congr rfl
  intro h _
  simp only [dcoef, map_mul, RCLike.conj_conj]
  ring

theorem norm_dcoef_le {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    (ξ : ℝ) (h : ℕ) :
    ‖S.dcoef ψ₀ ξ h‖ ≤ (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ)) := by
  have hM := S.M_pos
  have hY := S.Y_pos
  have hb0 : 0 ≤ (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ)) := by
    positivity
  by_cases hψ : ψ₀.ψ₀ (h / S.M) = 0
  · rw [show S.dcoef ψ₀ ξ h = 0 by simp [dcoef, hψ], norm_zero]; exact hb0
  obtain ⟨h1, h2⟩ := S.lt_of_ψ₀_ne_zero ψ₀ hψ
  have hh0 : (0 : ℝ) < h := lt_trans hM h1
  have hP : 0 < 2 * Real.pi * h * S.Y := by positivity
  have hmem : h ∈ S.Hs := by
    unfold Hs
    refine Finset.mem_Icc.2 ⟨?_, Nat.le_floor h2⟩
    exact_mod_cast (show (1 : ℝ) ≤ h by
      have : (0 : ℕ) < h := by exact_mod_cast hh0
      exact_mod_cast this)
  unfold dcoef
  rw [RCLike.norm_conj, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ψ₀.nonneg _), norm_cpow_line hP]
  have e1 := ψ₀.le_one (h / S.M)
  have e0 := ψ₀.nonneg (h / S.M)
  have e2 : (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) ≤ (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) := by
    apply Real.rpow_le_rpow hP.le _ (by norm_num)
    nlinarith [Real.pi_pos]
  have e3 := hM6 h hmem ξ
  calc ψ₀.ψ₀ (h / S.M) * (2 * Real.pi * h * S.Y) ^ (3 / 2 : ℝ) *
        ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖
      ≤ 1 * (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6 * (1 + |ξ|) ^ (-(6 : ℝ))) := by
        gcongr
    _ = _ := by ring

/-- **The large sieve for `D(ρ, ξ)`**. -/
theorem LS_Dsum {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {T : ℝ} (hT : 1 ≤ T) (ξ : ℝ) :
    ∫ x in F.ball T, ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x ∂F.ν ≤
      Cls S.η * (T ^ 2 + S.M ^ (1 + S.η) / S.q) *
        (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by
  have hM := S.M_pos
  have hsupp : ∀ n, S.dcoef ψ₀ ξ n ≠ 0 → S.M < n ∧ (n : ℝ) ≤ 2 * S.M := by
    intro n hn
    apply S.lt_of_ψ₀_ne_zero ψ₀
    intro h0
    exact hn (by simp [dcoef, h0])
  have h := hLS S.η S.hη T hT S.M S.hM1 (S.dcoef ψ₀ ξ) hsupp
  simp only [← S.norm_Dsum_eq ψ₀] at h
  refine h.trans ?_
  have hC := S.Cls_nonneg F hLS
  have hq := S.q_pos
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (by positivity))
  set b := (4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ)) with hb
  calc ∑ n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, ‖S.dcoef ψ₀ ξ n‖ ^ 2
      ≤ ∑ _n ∈ Finset.Icc 1 ⌊2 * S.M⌋₊, b ^ 2 :=
        Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _)
          (S.norm_dcoef_le ψ₀ hC6 hM6 ξ n) 2
    _ = ((Finset.Icc 1 ⌊2 * S.M⌋₊).card : ℝ) * b ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * S.M * b ^ 2 := mul_le_mul_of_nonneg_right S.card_Hs_le (sq_nonneg _)

theorem measurable_Dsum_joint :
    Measurable (fun z : F.Ω × ℝ => S.Dsum ψ₀ (F.ρ z.1) z.2) := by
  unfold Dsum
  apply Finset.measurable_sum
  intro h hh
  have hP : 0 < 2 * Real.pi * (h : ℝ) * S.Y := by
    have := (S.le_of_mem_Hs hh).1
    have : (0 : ℝ) < h := by exact_mod_cast this
    have := S.Y_pos
    positivity
  have h1 : Measurable fun z : F.Ω × ℝ => (starRingEnd ℂ) (F.ρ z.1 h) :=
    Complex.continuous_conj.measurable.comp ((F.meas_ρ h).comp measurable_fst)
  have h2 : Measurable fun z : F.Ω × ℝ =>
      ((2 * Real.pi * h * S.Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * z.2)) :=
    (continuous_cpow_line hP).measurable.comp measurable_snd
  have h3 : Measurable fun z : F.Ω × ℝ => Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * z.2) :=
    ((S.continuous_Mh_w h).comp (by fun_prop : Continuous fun ξ : ℝ => -3 / 2 + I * ξ)).measurable.comp
      measurable_snd
  exact ((measurable_const.mul h1).mul h2).mul h3

/-- `c₅ = ∫ (1+|ξ|)^(-5) dξ`. -/
noncomputable def c₅ : ℝ := ∫ ξ : ℝ, (1 + |ξ|) ^ (-(5 : ℝ))

theorem c₅_nonneg : 0 ≤ c₅ := integral_nonneg fun ξ => by positivity

/-- `(1+|ξ|)² (1+|ξ|)^5 ((1+|ξ|)^(-6))² = (1+|ξ|)^(-5)`. -/
theorem one_add_abs_pow_combine (ξ : ℝ) :
    (1 + |ξ|) ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * ((1 + |ξ|) ^ (-(6 : ℝ))) ^ 2 =
      (1 + |ξ|) ^ (-(5 : ℝ)) := by
  have hu : 0 < 1 + |ξ| := by positivity
  rw [← Real.rpow_natCast (1 + |ξ|) 2, ← Real.rpow_natCast ((1 + |ξ|) ^ (-(6 : ℝ))) 2,
    ← Real.rpow_mul hu.le, ← Real.rpow_add hu, ← Real.rpow_add hu]
  norm_num

theorem measurable_Dsum (ξ : ℝ) : Measurable (fun x => S.Dsum ψ₀ (F.ρ x) ξ) := by
  unfold Dsum
  apply Finset.measurable_sum
  intro h _
  exact ((measurable_const.mul (Complex.continuous_conj.measurable.comp (F.meas_ρ h))).mul
    measurable_const).mul measurable_const

/-- The majorant of the integrand of `mᴿ`. -/
theorem rem_dom {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    (ρ : ℕ → ℂ) (τ ξ : ℝ) :
    (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2 ≤
      (CGt ^ 2 * (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) *
        ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) * (1 + |ξ|) ^ (-(5 : ℝ)) := by
  have hM := S.M_pos
  have hY := S.Y_pos
  have hu : 0 < 1 + |ξ| := by positivity
  have hg1 : ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 ≤ CGt ^ 2 * (1 + |ξ|) ^ (5 : ℝ) := by
    have h1 := Gt_sq_mul_cosh_le hGt τ ξ
    have hc1 : 1 ≤ Real.cosh (Real.pi * τ) := Real.one_le_cosh _
    have hv : (1 + |τ|) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by norm_num)
    calc ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 ≤ ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * Real.cosh (Real.pi * τ) :=
          le_mul_of_one_le_right (sq_nonneg _) hc1
      _ ≤ CGt ^ 2 * ((1 + |ξ|) ^ (5 : ℝ) * (1 + |τ|) ^ (-(5 : ℝ))) := h1
      _ ≤ CGt ^ 2 * ((1 + |ξ|) ^ (5 : ℝ) * 1) := by gcongr
      _ = _ := by ring
  have hd := S.norm_Dsum_sq_le ψ₀ hC6 hM6 ρ ξ
  have hcomb := one_add_abs_pow_combine ξ
  calc (1 + |ξ|) ^ 2 * ‖Gt τ (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ ρ ξ‖ ^ 2
      ≤ (1 + |ξ|) ^ 2 * (CGt ^ 2 * (1 + |ξ|) ^ (5 : ℝ)) *
          (2 * S.M * (∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) *
            ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by
        gcongr
    _ = (CGt ^ 2 * (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) *
          ∑ h ∈ S.Hs, ‖ρ h‖ ^ 2) *
          ((1 + |ξ|) ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * ((1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by ring
    _ = _ := by rw [hcomb]

/-- The large sieve bound for each `ξ` on the annulus `R < |t| ≤ R₁`. -/
theorem rem_inner {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {R R₁ : ℝ} (hR : 1 ≤ R) (hR₁ : 1 ≤ R₁) (ξ : ℝ) :
    ∫ x in F.annulus R R₁, (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 *
        ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 ∂F.ν ≤
      CGt ^ 2 * (1 + R) ^ (-(5 : ℝ)) * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) *
        (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) *
          (1 + |ξ|) ^ (-(5 : ℝ)) := by
  have hM := S.M_pos
  have hY := S.Y_pos
  have hAm : MeasurableSet (F.annulus R R₁) := F.measurableSet_annulus R R₁
  have hτm : Measurable fun x => (F.t x).re := Complex.measurable_re.comp F.meas_t
  have hGtc : Continuous fun t : ℝ => Gt t (-3 / 2 + I * ξ) :=
    continuous_Gt_line.comp (f := fun t : ℝ => (t, ξ)) (by fun_prop)
  -- integrability
  have hDi : IntegrableOn (fun x => ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2) (F.ball R₁) F.ν := by
    have := F.integrableOn_sq_sum (Finset.Icc 1 ⌊2 * S.M⌋₊) (c := fun _ n => S.dcoef ψ₀ ξ n)
      (fun _ => measurable_const) (fun _ n => S.norm_dcoef_le ψ₀ hC6 hM6 ξ n) R₁
    simpa only [← S.norm_Dsum_eq ψ₀] using this
  have hDci := F.integrableOn_div_ch hDi
  have hLi : IntegrableOn (fun x => (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 *
      ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2) (F.annulus R R₁) F.ν := by
    have hdom := ((F.integrableOn_sum_sq_ρ S.Hs R₁).mono_set
      (F.annulus_subset_ball R R₁)).const_mul
        (CGt ^ 2 * (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2))
    have hdom' := hdom.mul_const ((1 + |ξ|) ^ (-(5 : ℝ)))
    refine hdom'.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((measurable_const.mul ((hGtc.measurable.comp hτm).norm.pow_const 2)).mul
        ((S.measurable_Dsum ψ₀ F ξ).norm.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact S.rem_dom ψ₀ hC6 hM6 hGt (F.ρ x) (F.t x).re ξ
  set κ : ℝ := (1 + |ξ|) ^ 2 * (CGt ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * (1 + R) ^ (-(5 : ℝ))) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hpt : ∀ x ∈ F.annulus R R₁, (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 *
      ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 ≤ κ * (‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x) := by
    intro x hx
    have hx' : x ∉ F.exc := F.not_exc_of_mem_annulus (by linarith) hx
    have hch := F.ch_of_not_exc hx'
    have hτ : R < |(F.t x).re| := by rw [← F.norm_eq_abs_re_of_not_exc hx']; exact hx.1
    have h1 := Gt_sq_mul_cosh_le hGt (F.t x).re ξ
    have hv : (1 + |(F.t x).re|) ^ (-(5 : ℝ)) ≤ (1 + R) ^ (-(5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    have hG' : ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 ≤
        CGt ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * (1 + R) ^ (-(5 : ℝ)) / F.ch x := by
      rw [le_div_iff₀ (F.ch_pos x), hch]
      calc ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 * Real.cosh (Real.pi * (F.t x).re)
          ≤ CGt ^ 2 * ((1 + |ξ|) ^ (5 : ℝ) * (1 + |(F.t x).re|) ^ (-(5 : ℝ))) := h1
        _ ≤ CGt ^ 2 * ((1 + |ξ|) ^ (5 : ℝ) * (1 + R) ^ (-(5 : ℝ))) := by gcongr
        _ = _ := by ring
    calc (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 * ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2
        ≤ (1 + |ξ|) ^ 2 * (CGt ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * (1 + R) ^ (-(5 : ℝ)) / F.ch x) *
            ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 := by gcongr
      _ = κ * (‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x) := by rw [hκ]; ring
  have hLS' := S.LS_Dsum ψ₀ F hLS hC6 hM6 (T := R₁) hR₁ ξ
  have hcomb := one_add_abs_pow_combine ξ
  calc ∫ x in F.annulus R R₁, (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 *
        ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 ∂F.ν
      ≤ ∫ x in F.annulus R R₁, κ * (‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x) ∂F.ν :=
        setIntegral_mono_on hLi ((hDci.mono_set (F.annulus_subset_ball R R₁)).const_mul κ)
          hAm hpt
    _ = κ * ∫ x in F.annulus R R₁, ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x ∂F.ν :=
        integral_const_mul _ _
    _ ≤ κ * ∫ x in F.ball R₁, ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 / F.ch x ∂F.ν := by
        apply mul_le_mul_of_nonneg_left _ hκ0
        exact setIntegral_mono_set hDci
          (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (F.ch_pos x).le)
          (Eventually.of_forall (F.annulus_subset_ball R R₁))
    _ ≤ κ * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q) *
          (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6 * (1 + |ξ|) ^ (-(6 : ℝ))) ^ 2)) :=
        mul_le_mul_of_nonneg_left hLS' hκ0
    _ = CGt ^ 2 * (1 + R) ^ (-(5 : ℝ)) * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) *
          (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) *
          ((1 + |ξ|) ^ 2 * (1 + |ξ|) ^ (5 : ℝ) * ((1 + |ξ|) ^ (-(6 : ℝ))) ^ 2) := by
        rw [hκ]; ring
    _ = _ := by rw [hcomb]

set_option maxHeartbeats 1000000 in
/-- **The remainder terms on the annulus `R < |t| ≤ R₁`**. -/
theorem rem_block {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {R R₁ : ℝ} (hR : 1 ≤ R) (hR₁ : 1 ≤ R₁) :
    IntegrableOn (fun x => S.mRem ψ₀ (F.ρ x) (F.t x).re) (F.annulus R R₁) F.ν ∧
    ∫ x in F.annulus R R₁, S.mRem ψ₀ (F.ρ x) (F.t x).re ∂F.ν ≤
      S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (1 + R) ^ (-(5 : ℝ)) *
        (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) *
          (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅) := by
  classical
  have hM := S.M_pos
  have hY := S.Y_pos
  set A := F.annulus R R₁ with hA
  set ν1 : Measure F.Ω := F.ν.restrict A with hν1
  have : IsFiniteMeasure ν1 := isFiniteMeasure_restrict.2
    (ne_top_of_le_ne_top (F.finite_ball R₁) (measure_mono (F.annulus_subset_ball R R₁)))
  have hτm : Measurable fun x => (F.t x).re := Complex.measurable_re.comp F.meas_t
  set G : F.Ω → ℝ → ℝ := fun x ξ => (1 + |ξ|) ^ 2 * ‖Gt (F.t x).re (-3 / 2 + I * ξ)‖ ^ 2 *
    ‖S.Dsum ψ₀ (F.ρ x) ξ‖ ^ 2 with hG
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Measurable fun z : F.Ω × ℝ => (1 + |z.2|) ^ 2 :=
      ((continuous_const.add continuous_abs).pow 2).measurable.comp measurable_snd
    have h2 : Measurable fun z : F.Ω × ℝ => ‖Gt (F.t z.1).re (-3 / 2 + I * z.2)‖ ^ 2 :=
      ((continuous_Gt_line.measurable.comp (f := fun z : F.Ω × ℝ => ((F.t z.1).re, z.2))
        ((hτm.comp measurable_fst).prodMk measurable_snd)).norm).pow_const 2
    have h3 : Measurable fun z : F.Ω × ℝ => ‖S.Dsum ψ₀ (F.ρ z.1) z.2‖ ^ 2 :=
      ((S.measurable_Dsum_joint ψ₀ F).norm).pow_const 2
    exact (h1.mul h2).mul h3
  set Kd := CGt ^ 2 * (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) with hKd
  have hsumi : Integrable (fun x => Kd * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) ν1 :=
    ((F.integrableOn_sum_sq_ρ S.Hs R₁).mono_set (F.annulus_subset_ball R R₁)).const_mul _
  have hGi : Integrable (Function.uncurry G) (ν1.prod volume) := by
    refine (hsumi.mul_prod (integrable_one_add_abs_rpow (by norm_num : (1 : ℝ) < 5))).mono'
      hGm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    show ‖G z.1 z.2‖ ≤ Kd * (∑ h ∈ S.Hs, ‖F.ρ z.1 h‖ ^ 2) * (1 + |z.2|) ^ (-(5 : ℝ))
    rw [Real.norm_of_nonneg (by simp only [hG]; positivity)]
    exact S.rem_dom ψ₀ hC6 hM6 hGt (F.ρ z.1) (F.t z.1).re z.2
  set c := S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ with hc
  have hc0 : 0 ≤ c := by have := c₂_nonneg; positivity
  have hm : ∀ x, S.mRem ψ₀ (F.ρ x) (F.t x).re = c * ∫ ξ, G x ξ := fun x => rfl
  have hint : IntegrableOn (fun x => S.mRem ψ₀ (F.ρ x) (F.t x).re) A F.ν := by
    refine (hGi.integral_prod_left.const_mul c).congr (Eventually.of_forall fun x => ?_)
    exact (hm x).symm
  refine ⟨hint, ?_⟩
  rw [show (∫ x in A, S.mRem ψ₀ (F.ρ x) (F.t x).re ∂F.ν) = c * ∫ x, ∫ ξ, G x ξ ∂volume ∂ν1 by
    rw [← integral_const_mul]; rfl]
  rw [integral_integral_swap hGi]
  apply mul_le_mul_of_nonneg_left _ hc0
  set b : ℝ := CGt ^ 2 * (1 + R) ^ (-(5 : ℝ)) * (Cls S.η * (R₁ ^ 2 + S.M ^ (1 + S.η) / S.q)) *
    (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) with hb
  calc ∫ ξ, ∫ x, G x ξ ∂ν1 ∂volume ≤ ∫ ξ : ℝ, b * (1 + |ξ|) ^ (-(5 : ℝ)) :=
        integral_mono hGi.integral_prod_right
          ((integrable_one_add_abs_rpow (by norm_num : (1 : ℝ) < 5)).const_mul b)
          (fun ξ => S.rem_inner ψ₀ F hLS hC6 hM6 hGt hR hR₁ ξ)
    _ = b * c₅ := integral_const_mul _ _

end Setup

end Triples
