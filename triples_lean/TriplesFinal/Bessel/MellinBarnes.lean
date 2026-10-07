import TriplesFinal.Assumptions.Assumptions

/-!
# Lemma 11.2: a Mellin–Barnes formula for `K_{it}`

Let `t ∈ ℝ ∖ {0}` and `y > 0`, and put `G_t(w) = 2^(w-2) Γ((w+it)/2) Γ((w-it)/2)`. Then
`K_{it}(y) = ½ Γ(it) (y/2)^(-it) + ½ Γ(-it) (y/2)^(it) + (1/2πi) ∫_{(-3/2)} G_t(w) y^(-w) dw`,
where the integral converges absolutely, and
`|G_t(-3/2 + iξ)| ≤ C e^(-π|t|/2) (1 + |ξ + t|)^(-5/4) (1 + |ξ - t|)^(-5/4)`.

This file defines `G_t` and proves the bound (`Gt_bound`, from Stirling's bound). The formula is
proved in `Bessel/MellinBarnesProof.lean` (`mellin_barnes`), by Mellin inversion on `Re w = 1/2` and a
contour shift to `Re w = -3/2` (with a Phragmén–Lindelöf bound for `Γ` in the strip).

Paper: §11, Lemma 11.2.
-/

namespace Triples

open Complex MeasureTheory

/-- `G_t(w) = 2^(w-2) Γ((w+it)/2) Γ((w-it)/2)`. -/
noncomputable def Gt (t : ℝ) (w : ℂ) : ℂ :=
  (2 : ℂ) ^ (w - 2) * Complex.Gamma ((w + I * t) / 2) * Complex.Gamma ((w - I * t) / 2)

/-- `(1 + |u|/2)^(-5/4) ≤ 2^(5/4) (1 + |u|)^(-5/4)`. -/
theorem one_add_half_rpow_le (u : ℝ) :
    (1 + |u| / 2) ^ (-(5 : ℝ) / 4) ≤ (2 : ℝ) ^ ((5 : ℝ) / 4) * (1 + |u|) ^ (-(5 : ℝ) / 4) := by
  have h1 : (1 + |u|) / 2 ≤ 1 + |u| / 2 := by linarith [abs_nonneg u]
  have hpos : 0 < (1 + |u|) / 2 := by positivity
  calc (1 + |u| / 2) ^ (-(5 : ℝ) / 4) ≤ ((1 + |u|) / 2) ^ (-(5 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_nonpos hpos h1 (by norm_num)
    _ = (2 : ℝ) ^ ((5 : ℝ) / 4) * (1 + |u|) ^ (-(5 : ℝ) / 4) := by
        rw [Real.div_rpow (by positivity) (by norm_num), div_eq_mul_inv, mul_comm,
          ← Real.rpow_neg (by norm_num)]
        congr 2; ring

/-- **Lemma 11.2**, the bound for `G_t` on `Re w = -3/2`. -/
theorem Gt_bound (hB : BesselAssumptions) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      C * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4) := by
  obtain ⟨C, hC⟩ := hB.stirling
  refine ⟨(2 : ℝ) ^ (-(7 : ℝ) / 2) * C ^ 2 * ((2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2, fun t ξ => ?_⟩
  have h1 : (-3 / 2 + I * ξ + I * t) / 2 = -3 / 4 + I * ((ξ + t) / 2) := by ring
  have h2 : (-3 / 2 + I * ξ - I * t) / 2 = -3 / 4 + I * ((ξ - t) / 2) := by ring
  have hΓ1 := hC ((ξ + t) / 2)
  have hΓ2 := hC ((ξ - t) / 2)
  have hpow : ‖(2 : ℂ) ^ (-3 / 2 + I * ξ - 2)‖ = (2 : ℝ) ^ (-(7 : ℝ) / 2) := by
    have := norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-3 / 2 + I * ξ - 2)
    push_cast at this
    rw [this]
    congr 1
    simp
    norm_num
  -- `C ≥ 0`
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have : 0 < (1 + |(0 : ℝ)|) ^ (-(5 : ℝ) / 4) * Real.exp (-Real.pi * |(0 : ℝ)| / 2) := by
      positivity
    by_contra hneg
    push Not at hneg
    have := norm_nonneg (Complex.Gamma (-3 / 4 + I * (0 : ℝ)))
    nlinarith
  -- the exponential factors
  have hexp : Real.exp (-Real.pi * |(ξ + t) / 2| / 2) * Real.exp (-Real.pi * |(ξ - t) / 2| / 2) ≤
      Real.exp (-Real.pi * |t| / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have habs : 2 * |t| ≤ |ξ + t| + |ξ - t| := by
      have := abs_sub (ξ + t) (ξ - t)
      have h : (ξ + t) - (ξ - t) = 2 * t := by ring
      rw [h, abs_mul, abs_two] at this
      linarith
    rw [abs_div, abs_div, abs_two]
    nlinarith [Real.pi_pos]
  have hA := one_add_half_rpow_le (ξ + t)
  have hB' := one_add_half_rpow_le (ξ - t)
  have habs1 : |(ξ + t) / 2| = |ξ + t| / 2 := by rw [abs_div, abs_two]
  have habs2 : |(ξ - t) / 2| = |ξ - t| / 2 := by rw [abs_div, abs_two]
  unfold Gt
  rw [norm_mul, norm_mul, hpow, h1, h2]
  rw [habs1] at hΓ1
  rw [habs2] at hΓ2
  have e1 : 0 ≤ Real.exp (-Real.pi * |(ξ + t) / 2| / 2) := (Real.exp_pos _).le
  have e2 : 0 ≤ Real.exp (-Real.pi * |(ξ - t) / 2| / 2) := (Real.exp_pos _).le
  rw [habs1] at e1 hexp
  rw [habs2] at e2 hexp
  set a1 := (1 + |ξ + t| / 2) ^ (-(5 : ℝ) / 4)
  set a2 := (1 + |ξ - t| / 2) ^ (-(5 : ℝ) / 4)
  set b1 := (1 + |ξ + t|) ^ (-(5 : ℝ) / 4)
  set b2 := (1 + |ξ - t|) ^ (-(5 : ℝ) / 4)
  set E1 := Real.exp (-Real.pi * (|ξ + t| / 2) / 2)
  set E2 := Real.exp (-Real.pi * (|ξ - t| / 2) / 2)
  set Et := Real.exp (-Real.pi * |t| / 2)
  set c := (2 : ℝ) ^ ((5 : ℝ) / 4)
  have ha1 : 0 ≤ a1 := by positivity
  have ha2 : 0 ≤ a2 := by positivity
  have hb1 : 0 ≤ b1 := by positivity
  have hb2 : 0 ≤ b2 := by positivity
  have hc : 0 ≤ c := by positivity
  have h27 : 0 ≤ (2 : ℝ) ^ (-(7 : ℝ) / 2) := by positivity
  push_cast at hΓ1 hΓ2
  calc (2 : ℝ) ^ (-(7 : ℝ) / 2) * ‖Complex.Gamma (-3 / 4 + I * ((ξ + t) / 2))‖ *
        ‖Complex.Gamma (-3 / 4 + I * ((ξ - t) / 2))‖
      ≤ (2 : ℝ) ^ (-(7 : ℝ) / 2) * (C * a1 * E1) * (C * a2 * E2) := by
        gcongr
    _ = (2 : ℝ) ^ (-(7 : ℝ) / 2) * C ^ 2 * (a1 * a2) * (E1 * E2) := by ring
    _ ≤ (2 : ℝ) ^ (-(7 : ℝ) / 2) * C ^ 2 * ((c * b1) * (c * b2)) * Et := by
        gcongr
    _ = (2 : ℝ) ^ (-(7 : ℝ) / 2) * C ^ 2 * c ^ 2 * Et * b1 * b2 := by ring


end Triples
