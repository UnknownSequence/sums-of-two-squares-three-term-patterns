import TriplesFinal.Bessel.Mh
import TriplesFinal.Poisson.Defs

/-!
# The set-up of §12

For data satisfying (H), `0 < η ≤ 1` and a frequency scale `M` with `1/2 ≤ M ≤ 2h₀`, the
parameters `q = 4Ed`, `N = EH`, `Q = qX`, `Y = √N/(EK)`, `L = Δ + 8Q^η`, `V = Q^η/(MY)`,
`ℓ = log V`, `T₁ = Q^η L`, and the size estimates (12.1):
`1/(8Q) ≤ MY ≤ Q^η/2`, `hX/K ≤ 4Q^η` for `h ≤ 2M`, `V ≥ 2`, `M ≤ 2Q²`.

Paper: §12.1.
-/

namespace Triples

/-- The data of the proof of Theorem 6.1 at a frequency scale `M`. -/
structure Setup (Cν : ℕ → ℝ) where
  E : ℕ
  H : ℕ
  d : ℕ
  κ : ℕ
  Δ : ℝ
  X : ℝ
  K : ℝ
  ψ₁ : ℝ → ℂ
  ψ₂ : ℝ → ℂ
  hyp : HypH Cν E H d κ Δ X K ψ₁ ψ₂
  η : ℝ
  hη : 0 < η
  hη1 : η ≤ 1
  M : ℝ
  hM1 : 1 / 2 ≤ M
  hM2 : M ≤ 2 * h₀ E d X K η

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν)

/-- `q = 4Ed`. -/
noncomputable def q : ℝ := ((4 * S.E * S.d : ℕ) : ℝ)
/-- `N = EH`. -/
noncomputable def N : ℝ := ((S.E * S.H : ℕ) : ℝ)
/-- `Q = qX`. -/
noncomputable def Q : ℝ := S.q * S.X
/-- `Y = √N/(EK)`. -/
noncomputable def Y : ℝ := Ypar S.E S.H S.K
/-- `L = Δ + 8Q^η`. -/
noncomputable def L : ℝ := Lpar S.E S.d S.Δ S.X S.η
/-- `V = Q^η/(MY)`. -/
noncomputable def V : ℝ := S.Q ^ S.η / (S.M * S.Y)
/-- `ℓ = log V`. -/
noncomputable def ℓ : ℝ := Real.log S.V
/-- `T₁ = Q^η L`. -/
noncomputable def T₁ : ℝ := S.Q ^ S.η * S.L
/-- `(X/K) Y^(-1/2)`. -/
noncomputable def Bk : ℝ := S.X / S.K * S.Y ^ (-(1 / 2 : ℝ))

theorem E_ge : (4 : ℝ) ≤ S.E := by
  rcases S.hyp.hE with h | h <;> rw [h] <;> norm_num

theorem E_le : (S.E : ℝ) ≤ 8 := by
  rcases S.hyp.hE with h | h <;> rw [h] <;> norm_num

theorem E_pos : 0 < S.E := by
  rcases S.hyp.hE with h | h <;> rw [h] <;> norm_num

theorem H_ge : (1 : ℝ) ≤ S.H := by exact_mod_cast S.hyp.hH

theorem d_ge : (3 : ℝ) ≤ S.d := by exact_mod_cast S.hyp.hd3

theorem N_ge : 4 ≤ S.N := by
  unfold N; push_cast
  nlinarith [S.E_ge, S.H_ge]

theorem sqrtN_ge : 2 ≤ Real.sqrt S.N := by
  rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt S.N_ge

theorem sqrtN_le_X : Real.sqrt S.N ≤ S.X := S.hyp.hX

theorem X_ge : 2 ≤ S.X := S.sqrtN_ge.trans S.sqrtN_le_X

theorem X_pos : 0 < S.X := by linarith [S.X_ge]

theorem K_ge : 1 ≤ S.K := S.hyp.hK1

theorem K_pos : 0 < S.K := by linarith [S.K_ge]

theorem q_eq : S.q = 4 * S.E * S.d := by unfold q; push_cast; ring

theorem q_ge : 48 ≤ S.q := by
  rw [S.q_eq]; nlinarith [S.E_ge, S.d_ge]

theorem q_pos : 0 < S.q := by linarith [S.q_ge]

theorem Q_ge : 96 ≤ S.Q := by
  unfold Q; nlinarith [S.q_ge, S.X_ge]

theorem Q_pos : 0 < S.Q := by linarith [S.Q_ge]

theorem one_le_Q : 1 ≤ S.Q := by linarith [S.Q_ge]

theorem K_le_Q : S.K ≤ S.Q := S.hyp.hKq

theorem Qη_ge : 1 ≤ S.Q ^ S.η := Real.one_le_rpow S.one_le_Q S.hη.le

theorem Qη_pos : 0 < S.Q ^ S.η := by linarith [S.Qη_ge]

theorem Qη_le_Q : S.Q ^ S.η ≤ S.Q := by
  calc S.Q ^ S.η ≤ S.Q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le S.one_le_Q S.hη1
    _ = S.Q := Real.rpow_one _

theorem h₀_eq : h₀ S.E S.d S.X S.K S.η = S.Q ^ S.η * S.K / S.X := rfl

theorem Y_eq : S.Y = Real.sqrt S.N / (S.E * S.K) := rfl

theorem Y_pos : 0 < S.Y := by
  rw [S.Y_eq]
  have := S.sqrtN_ge
  have := S.E_ge
  have := S.K_pos
  positivity

theorem Y_le : S.Y ≤ S.X / (S.E * S.K) := by
  rw [S.Y_eq]
  have := S.E_ge
  have := S.K_pos
  exact div_le_div_of_nonneg_right S.sqrtN_le_X (by positivity)

theorem Y_ge : 1 / (4 * S.Q) ≤ S.Y := by
  rw [S.Y_eq, div_le_div_iff₀ (by have := S.Q_pos; positivity)
    (by have := S.E_ge; have := S.K_pos; positivity)]
  have h1 := S.sqrtN_ge
  have h2 := S.E_le
  have h3 := S.K_le_Q
  have h4 := S.K_pos
  have h5 : S.E * S.K ≤ 8 * S.Q := by
    have := S.E_ge
    nlinarith
  nlinarith

theorem M_pos : 0 < S.M := by linarith [S.hM1]

theorem M_le : S.M ≤ 2 * S.Q ^ S.η * S.K / S.X := by
  have := S.hM2; rw [S.h₀_eq] at this; linarith [show 2 * (S.Q ^ S.η * S.K / S.X) =
    2 * S.Q ^ S.η * S.K / S.X by ring]

/-- `X/K ≤ 2Q^η/M`. -/
theorem XK_le : S.X / S.K ≤ 2 * S.Q ^ S.η / S.M := by
  have h := S.M_le
  have hK := S.K_pos
  have hX := S.X_pos
  have hM := S.M_pos
  rw [div_le_div_iff₀ hK hM]
  rw [le_div_iff₀ hX] at h
  nlinarith

/-- `hX/K ≤ 4Q^η` for `h ≤ 2M`. -/
theorem hXK_le {h : ℝ} (hh : h ≤ 2 * S.M) : h * S.X / S.K ≤ 4 * S.Q ^ S.η := by
  have h1 := S.XK_le
  have hM := S.M_pos
  have : h * S.X / S.K = h * (S.X / S.K) := by ring
  rw [this]
  calc h * (S.X / S.K) ≤ (2 * S.M) * (2 * S.Q ^ S.η / S.M) :=
        mul_le_mul hh h1 (by have := S.X_pos; have := S.K_pos; positivity) (by linarith)
    _ = 4 * S.Q ^ S.η := by field_simp; ring

theorem MY_le : S.M * S.Y ≤ S.Q ^ S.η / 2 := by
  have h1 := S.M_le
  have h2 := S.Y_le
  have hE := S.E_ge
  have hK := S.K_pos
  have hX := S.X_pos
  have hY := S.Y_pos
  have hQ := S.Qη_pos
  calc S.M * S.Y ≤ (2 * S.Q ^ S.η * S.K / S.X) * (S.X / (S.E * S.K)) :=
        mul_le_mul h1 h2 hY.le (by positivity)
    _ = 2 * S.Q ^ S.η / S.E := by field_simp
    _ ≤ S.Q ^ S.η / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

theorem MY_ge : 1 / (8 * S.Q) ≤ S.M * S.Y := by
  have h1 := S.Y_ge
  have hM := S.hM1
  have hQ := S.Q_pos
  calc 1 / (8 * S.Q) = 1 / 2 * (1 / (4 * S.Q)) := by field_simp; ring
    _ ≤ S.M * S.Y := mul_le_mul hM h1 (by positivity) S.M_pos.le

theorem MY_pos : 0 < S.M * S.Y := mul_pos S.M_pos S.Y_pos

/-- `M ≤ 2Q²`. -/
theorem M_le_Q2 : S.M ≤ 2 * S.Q ^ 2 := by
  have h1 := S.M_le
  have h2 := S.Qη_le_Q
  have h3 := S.K_le_Q
  have hX := S.X_ge
  have hK := S.K_pos
  have hQ := S.Q_pos
  calc S.M ≤ 2 * S.Q ^ S.η * S.K / S.X := h1
    _ ≤ 2 * S.Q * S.Q / 1 := by
        apply div_le_div₀ (by positivity) _ zero_lt_one (by linarith)
        have := S.Qη_pos
        apply mul_le_mul _ h3 hK.le (by positivity)
        linarith
    _ = 2 * S.Q ^ 2 := by ring

theorem V_eq : S.V = S.Q ^ S.η / (S.M * S.Y) := rfl

theorem V_ge : 2 ≤ S.V := by
  rw [S.V_eq, le_div_iff₀ S.MY_pos]
  linarith [S.MY_le]

theorem V_pos : 0 < S.V := by linarith [S.V_ge]

theorem V_le : S.V ≤ 8 * S.Q ^ 2 := by
  rw [S.V_eq, div_le_iff₀ S.MY_pos]
  have h1 := S.MY_ge
  have h2 := S.Qη_le_Q
  have hQ := S.Q_pos
  have : S.Q ^ S.η ≤ 8 * S.Q ^ 2 * (1 / (8 * S.Q)) := by
    rw [show 8 * S.Q ^ 2 * (1 / (8 * S.Q)) = S.Q by field_simp]
    exact h2
  calc S.Q ^ S.η ≤ 8 * S.Q ^ 2 * (1 / (8 * S.Q)) := this
    _ ≤ 8 * S.Q ^ 2 * (S.M * S.Y) := by gcongr

theorem ℓ_eq : S.ℓ = Real.log S.V := rfl

theorem ℓ_pos : 0 < S.ℓ := Real.log_pos (by linarith [S.V_ge])

theorem exp_ℓ : Real.exp S.ℓ = S.V := Real.exp_log S.V_pos

/-- `ℓ ≤ 6Q^η/η`. -/
theorem ℓ_le : S.ℓ ≤ 6 * S.Q ^ S.η / S.η := by
  have hη := S.hη
  have h1 : S.ℓ ≤ S.V ^ (S.η / 2) / (S.η / 2) :=
    Real.log_le_rpow_div S.V_pos.le (by positivity)
  have h2 : S.V ^ (S.η / 2) ≤ (8 * S.Q ^ 2) ^ (S.η / 2) :=
    Real.rpow_le_rpow S.V_pos.le S.V_le (by positivity)
  have hQ := S.Q_pos
  have h3 : (8 * S.Q ^ 2) ^ (S.η / 2) = 8 ^ (S.η / 2) * S.Q ^ S.η := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hQ.le]
    congr 2; push_cast; ring
  have h4 : (8 : ℝ) ^ (S.η / 2) ≤ 3 := by
    calc (8 : ℝ) ^ (S.η / 2) ≤ 8 ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [S.hη1])
      _ = Real.sqrt 8 := (Real.sqrt_eq_rpow 8).symm
      _ ≤ 3 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  calc S.ℓ ≤ S.V ^ (S.η / 2) / (S.η / 2) := h1
    _ ≤ (8 * S.Q ^ 2) ^ (S.η / 2) / (S.η / 2) := by gcongr
    _ = 8 ^ (S.η / 2) * S.Q ^ S.η * 2 / S.η := by rw [h3]; field_simp
    _ ≤ 3 * S.Q ^ S.η * 2 / S.η := by
        have := S.Qη_pos
        gcongr
    _ = 6 * S.Q ^ S.η / S.η := by ring

theorem L_eq : S.L = S.Δ + 8 * S.Q ^ S.η := rfl

theorem Δ_ge : 1 ≤ S.Δ := S.hyp.hΔ

theorem L_ge : 8 * S.Q ^ S.η ≤ S.L := by rw [S.L_eq]; linarith [S.Δ_ge]

theorem one_le_L : 1 ≤ S.L := by linarith [S.L_ge, S.Qη_ge]

theorem L_pos : 0 < S.L := by linarith [S.one_le_L]

theorem Δ_le_L : S.Δ ≤ S.L := by rw [S.L_eq]; linarith [S.Qη_pos]

theorem L_le : S.L ≤ 9 * S.Δ * S.Q ^ S.η := by
  rw [S.L_eq]
  have := S.Δ_ge
  have := S.Qη_ge
  nlinarith

theorem T₁_eq : S.T₁ = S.Q ^ S.η * S.L := rfl

theorem one_le_T₁ : 1 ≤ S.T₁ := by
  rw [S.T₁_eq]; nlinarith [S.Qη_ge, S.one_le_L]

theorem T₁_pos : 0 < S.T₁ := by linarith [S.one_le_T₁]

theorem Qη_le_T₁ : S.Q ^ S.η ≤ S.T₁ := by
  rw [S.T₁_eq]; nlinarith [S.Qη_ge, S.one_le_L]

theorem L_le_T₁ : S.L ≤ S.T₁ := by
  rw [S.T₁_eq]; nlinarith [S.Qη_ge, S.one_le_L]

theorem Bk_pos : 0 < S.Bk := by
  unfold Bk
  have := S.X_pos; have := S.K_pos; have := S.Y_pos
  positivity

/-- `M^(1+η)/q ≤ 2 Q^(2η) M/q`. -/
theorem M_pow_le : S.M ^ (1 + S.η) / S.q ≤ 2 * S.Q ^ (2 * S.η) * (S.M / S.q) := by
  have hM := S.M_pos
  have hq := S.q_pos
  have hQ := S.Q_pos
  rw [Real.rpow_add hM, Real.rpow_one]
  have h1 : S.M ^ S.η ≤ (2 * S.Q ^ 2) ^ S.η := Real.rpow_le_rpow hM.le S.M_le_Q2 S.hη.le
  have h2 : (2 * S.Q ^ 2) ^ S.η = 2 ^ S.η * S.Q ^ (2 * S.η) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    push_cast; ring_nf
  have h3 : (2 : ℝ) ^ S.η ≤ 2 := by
    calc (2 : ℝ) ^ S.η ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) S.hη1
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ S.Q ^ (2 * S.η) := by positivity
  calc S.M * S.M ^ S.η / S.q = S.M ^ S.η * (S.M / S.q) := by ring
    _ ≤ (2 * S.Q ^ (2 * S.η)) * (S.M / S.q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [h2] at h1
        nlinarith
    _ = 2 * S.Q ^ (2 * S.η) * (S.M / S.q) := by ring

end Setup

end Triples
