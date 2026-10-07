import TriplesFinal.TypeIProof.ContinuousSide

/-!
# Size estimates for the bounds of the blocks

With `x = Q^η ≥ 1` and `W = (1 + M/q) M`: `(1 + M^(1+η)/q) M ≤ 2x² W`,
`(T₁² + M^(1+η)/q) M ≤ 3T₁² W`, `(4 + M^(1+η)/q) M ≤ 6x² W`, `(qM)^η ≤ 2x³`,
`(4πMY)³ ≤ (2πx)³`, `ε₀² ≤ (32C₀²/π)² Q² e^(-πx)` and `Q⁴ e^(-πx) ≤ ⌈4/η⌉!`.

Paper: §12.1 (the polynomial bounds used to discard negligible terms).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν)

/-- `W = (1 + M/q) M`. -/
noncomputable def W : ℝ := (1 + S.M / S.q) * S.M

theorem W_pos : 0 < S.W := by
  unfold W; have := S.M_pos; have := S.q_pos; positivity

theorem M_le_W : S.M ≤ S.W := by
  unfold W; have := S.M_pos; have := S.q_pos
  have : 0 ≤ S.M / S.q := by positivity
  nlinarith

theorem Mq_mul_le_W : S.M / S.q * S.M ≤ S.W := by
  unfold W; have := S.M_pos; nlinarith

theorem Qη2 : S.Q ^ (2 * S.η) = (S.Q ^ S.η) ^ 2 := by
  rw [mul_comm, Real.rpow_mul S.Q_pos.le]; norm_cast

theorem A_nonneg : 0 ≤ S.M ^ (1 + S.η) / S.q := by
  have := S.M_pos; have := S.q_pos; positivity

theorem A_mul_le : S.M ^ (1 + S.η) / S.q * S.M ≤ 2 * (S.Q ^ S.η) ^ 2 * S.W := by
  have h1 := S.M_pow_le
  rw [S.Qη2] at h1
  have hM := S.M_pos
  have h2 := S.Mq_mul_le_W
  have hx : 0 ≤ (S.Q ^ S.η) ^ 2 := sq_nonneg _
  calc S.M ^ (1 + S.η) / S.q * S.M ≤ 2 * (S.Q ^ S.η) ^ 2 * (S.M / S.q) * S.M :=
        mul_le_mul_of_nonneg_right h1 hM.le
    _ = 2 * (S.Q ^ S.η) ^ 2 * (S.M / S.q * S.M) := by ring
    _ ≤ 2 * (S.Q ^ S.η) ^ 2 * S.W := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem one_le_x2 : 1 ≤ (S.Q ^ S.η) ^ 2 := one_le_pow₀ S.Qη_ge

theorem M_le_x2W : S.M ≤ (S.Q ^ S.η) ^ 2 * S.W := by
  have h2 := S.M_le_W
  have h3 := S.one_le_x2
  have hW := S.W_pos
  nlinarith

theorem one_add_A_mul_le :
    (1 + S.M ^ (1 + S.η) / S.q) * S.M ≤ 3 * (S.Q ^ S.η) ^ 2 * S.W := by
  have h1 := S.A_mul_le
  have h4 := S.M_le_x2W
  calc (1 + S.M ^ (1 + S.η) / S.q) * S.M = S.M + S.M ^ (1 + S.η) / S.q * S.M := by ring
    _ ≤ (S.Q ^ S.η) ^ 2 * S.W + 2 * (S.Q ^ S.η) ^ 2 * S.W := add_le_add h4 h1
    _ = 3 * (S.Q ^ S.η) ^ 2 * S.W := by ring

theorem four_add_A_mul_le :
    (4 + S.M ^ (1 + S.η) / S.q) * S.M ≤ 6 * (S.Q ^ S.η) ^ 2 * S.W := by
  have h1 := S.A_mul_le
  have h4 := S.M_le_x2W
  calc (4 + S.M ^ (1 + S.η) / S.q) * S.M = 4 * S.M + S.M ^ (1 + S.η) / S.q * S.M := by ring
    _ ≤ 4 * ((S.Q ^ S.η) ^ 2 * S.W) + 2 * (S.Q ^ S.η) ^ 2 * S.W := by linarith
    _ = 6 * (S.Q ^ S.η) ^ 2 * S.W := by ring

theorem T1sq_add_A_mul_le :
    (S.T₁ ^ 2 + S.M ^ (1 + S.η) / S.q) * S.M ≤ 3 * S.T₁ ^ 2 * S.W := by
  have h1 := S.A_mul_le
  have h2 := S.M_le_W
  have hx : (S.Q ^ S.η) ^ 2 ≤ S.T₁ ^ 2 := pow_le_pow_left₀ S.Qη_pos.le S.Qη_le_T₁ 2
  have hW := S.W_pos
  have hT : 0 ≤ S.T₁ ^ 2 := sq_nonneg _
  calc (S.T₁ ^ 2 + S.M ^ (1 + S.η) / S.q) * S.M
      = S.T₁ ^ 2 * S.M + S.M ^ (1 + S.η) / S.q * S.M := by ring
    _ ≤ S.T₁ ^ 2 * S.W + 2 * S.T₁ ^ 2 * S.W := by nlinarith
    _ = 3 * S.T₁ ^ 2 * S.W := by ring

/-- `q ≤ Q`. -/
theorem q_le_Q : S.q ≤ S.Q := by
  unfold Q; have := S.q_pos; have := S.X_ge; nlinarith

/-- `(qM)^η ≤ 2 (Q^η)³`. -/
theorem qM_rpow_le : (S.q * S.M) ^ S.η ≤ 2 * (S.Q ^ S.η) ^ 3 := by
  have hq := S.q_pos
  have hM := S.M_pos
  have hQ := S.Q_pos
  have h1 : S.q * S.M ≤ 2 * S.Q ^ 3 := by
    have := S.M_le_Q2
    have := S.q_le_Q
    nlinarith
  have h2 : (S.q * S.M) ^ S.η ≤ (2 * S.Q ^ 3) ^ S.η :=
    Real.rpow_le_rpow (by positivity) h1 S.hη.le
  have h3 : (2 * S.Q ^ 3) ^ S.η = 2 ^ S.η * (S.Q ^ S.η) ^ 3 := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast S.Q 3,
      ← Real.rpow_mul hQ.le, ← Real.rpow_natCast (S.Q ^ S.η) 3, ← Real.rpow_mul hQ.le]
    congr 2; push_cast; ring
  have h4 : (2 : ℝ) ^ S.η ≤ 2 := by
    calc (2 : ℝ) ^ S.η ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) S.hη1
      _ = 2 := Real.rpow_one 2
  rw [h3] at h2
  have h5 : 0 ≤ (S.Q ^ S.η) ^ 3 := by have := S.Qη_pos; positivity
  nlinarith

/-- `((4πMY)^(3/2))² ≤ (2π Q^η)³`. -/
theorem fourPiMY_le : ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 ≤
    (2 * Real.pi * S.Q ^ S.η) ^ 3 := by
  have hMY := S.MY_pos
  have hpi := Real.pi_pos
  have ha : 0 ≤ 4 * Real.pi * S.M * S.Y := by
    have : 4 * Real.pi * S.M * S.Y = 4 * Real.pi * (S.M * S.Y) := by ring
    rw [this]; positivity
  have e : ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 = (4 * Real.pi * S.M * S.Y) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  rw [e]
  apply pow_le_pow_left₀ ha
  have := S.MY_le
  have : 4 * Real.pi * S.M * S.Y = 4 * Real.pi * (S.M * S.Y) := by ring
  rw [this]
  nlinarith

/-- `ε₀² ≤ (32C₀²/π)² Q² e^(-πQ^η)`. -/
theorem eps0_sq_le :
    S.eps0 ^ 2 ≤ (32 * S.C₀ ^ 2 / Real.pi) ^ 2 * S.Q ^ 2 * Real.exp (-(Real.pi * S.Q ^ S.η)) := by
  have hMY := S.MY_pos
  have hpi := Real.pi_pos
  have hQ := S.Q_pos
  have hC := S.C₀_nonneg
  have hM0 : S.M ≠ 0 := S.M_pos.ne'
  have hY0 : S.Y ≠ 0 := S.Y_pos.ne'
  have hV : S.M * S.Y * S.V = S.Q ^ S.η := by
    rw [S.V_eq]; field_simp
  have e1 : S.eps0 = 4 * S.C₀ ^ 2 / Real.pi * (1 / (S.M * S.Y)) *
      Real.exp (-(Real.pi * S.Q ^ S.η / 2)) := by
    unfold eps0
    rw [show Real.pi * S.M * S.Y * S.V = Real.pi * (S.M * S.Y * S.V) by ring, hV]
    field_simp
  have h1 : 1 / (S.M * S.Y) ≤ 8 * S.Q := by
    rw [div_le_iff₀ hMY]
    have := S.MY_ge
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : 0 ≤ 1 / (S.M * S.Y) := by positivity
  have h3 : S.eps0 ≤ 32 * S.C₀ ^ 2 / Real.pi * S.Q * Real.exp (-(Real.pi * S.Q ^ S.η / 2)) := by
    rw [e1]
    have h4 : 0 ≤ 4 * S.C₀ ^ 2 / Real.pi := by positivity
    calc 4 * S.C₀ ^ 2 / Real.pi * (1 / (S.M * S.Y)) * Real.exp (-(Real.pi * S.Q ^ S.η / 2))
        ≤ 4 * S.C₀ ^ 2 / Real.pi * (8 * S.Q) * Real.exp (-(Real.pi * S.Q ^ S.η / 2)) := by
          gcongr
      _ = 32 * S.C₀ ^ 2 / Real.pi * S.Q * Real.exp (-(Real.pi * S.Q ^ S.η / 2)) := by ring
  have h5 := S.eps0_nonneg
  calc S.eps0 ^ 2 ≤ (32 * S.C₀ ^ 2 / Real.pi * S.Q * Real.exp (-(Real.pi * S.Q ^ S.η / 2))) ^ 2 :=
        pow_le_pow_left₀ h5 h3 2
    _ = (32 * S.C₀ ^ 2 / Real.pi) ^ 2 * S.Q ^ 2 *
          (Real.exp (-(Real.pi * S.Q ^ S.η / 2))) ^ 2 := by ring
    _ = _ := by
        rw [← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- `Q⁴ e^(-πQ^η) ≤ ⌈4/η⌉!`. -/
theorem Q4_exp_le :
    S.Q ^ 4 * Real.exp (-(Real.pi * S.Q ^ S.η)) ≤ ((Nat.ceil (4 / S.η)).factorial : ℝ) := by
  have hQ := S.Q_pos
  have hη := S.hη
  set x := S.Q ^ S.η with hx
  have hx1 : 1 ≤ x := S.Qη_ge
  set n := Nat.ceil (4 / S.η) with hn
  have h1 : S.Q ^ 4 = x ^ (4 / S.η) := by
    rw [hx, ← Real.rpow_mul hQ.le, mul_div_cancel₀ _ hη.ne']
    norm_cast
  have h2 : x ^ (4 / S.η) ≤ x ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil _)
  have h3 : x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
    have := Real.pow_div_factorial_le_exp x (by linarith) n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h4 : Real.exp x * Real.exp (-(Real.pi * x)) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.2
    nlinarith [Real.pi_gt_three]
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  calc S.Q ^ 4 * Real.exp (-(Real.pi * x)) ≤ ((n.factorial : ℝ) * Real.exp x) *
        Real.exp (-(Real.pi * x)) := by
        rw [h1]; exact mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (Real.exp x * Real.exp (-(Real.pi * x))) := by ring
    _ ≤ (n.factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h4 hf
    _ = _ := mul_one _

end Setup

end Triples
