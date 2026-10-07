import TriplesFinal.TypeIProof.SizeBounds

/-!
# The bound for `A₀` (the block `‖t‖ ≤ 1`)

`boundJ0 ≤ K_{J0} · ((X/K) Y^(-1/2) L² Q^(3η) 𝔈)² · W`, given a bound
`E ≤ K_E L³ Q^(3η) 𝔈² W` for the exceptional sums.

Paper: §12.2.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν)

/-- The constant of the bound for `A₀`. -/
noncomputable def KJ0 (Cls : ℝ → ℝ) (KE : ℝ) : ℝ :=
  2 * (36 * S.C₀ ^ 2 / S.η ^ 2 * (24 * Real.cosh Real.pi * Cls S.η * S.C₀ ^ 2 + KE) +
    24 * Real.cosh Real.pi * Cls S.η * (32 * S.C₀ ^ 2 / Real.pi) ^ 2 *
      ((Nat.ceil (4 / S.η)).factorial : ℝ))

theorem KJ0_nonneg {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {KE : ℝ} (hKE : 0 ≤ KE) :
    0 ≤ S.KJ0 Cls KE := by
  unfold KJ0
  have := S.C₀_nonneg
  have hc := (Real.cosh_pos Real.pi).le
  have hη := S.hη
  have h1 : 0 ≤ 24 * Real.cosh Real.pi * Cls S.η * S.C₀ ^ 2 + KE := by
    have : 0 ≤ 24 * Real.cosh Real.pi * Cls S.η * S.C₀ ^ 2 := by
      apply mul_nonneg _ (sq_nonneg _); apply mul_nonneg _ hCls; positivity
    linarith
  have h2 : 0 ≤ 24 * Real.cosh Real.pi * Cls S.η := mul_nonneg (by positivity) hCls
  positivity

/-- `x^a W ≤ L⁴ x⁶ 𝔈² W` for `a ≤ 6`. -/
theorem pow_le_unit {𝔈 : ℝ} (h𝔈 : 1 ≤ 𝔈) {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 4) :
    S.L ^ b * (S.Q ^ S.η) ^ a * S.W ≤ S.L ^ 4 * (S.Q ^ S.η) ^ 6 * 𝔈 ^ 2 * S.W := by
  have hx := S.Qη_ge
  have hL := S.one_le_L
  have hW := S.W_pos
  have h1 : (S.Q ^ S.η) ^ a ≤ (S.Q ^ S.η) ^ 6 := pow_le_pow_right₀ hx ha
  have h2 : S.L ^ b ≤ S.L ^ 4 := pow_le_pow_right₀ hL hb
  have h3 : 1 ≤ 𝔈 ^ 2 := one_le_pow₀ h𝔈
  have h4 : 0 ≤ (S.Q ^ S.η) ^ a := by have := S.Qη_pos; positivity
  have h5 : 0 ≤ S.L ^ b := by have := S.L_pos; positivity
  have h6 : S.L ^ b * (S.Q ^ S.η) ^ a ≤ S.L ^ 4 * (S.Q ^ S.η) ^ 6 := mul_le_mul h2 h1 h4 (by positivity)
  have h7 : 0 ≤ S.L ^ 4 * (S.Q ^ S.η) ^ 6 := by have := S.Qη_pos; have := S.L_pos; positivity
  calc S.L ^ b * (S.Q ^ S.η) ^ a * S.W ≤ S.L ^ 4 * (S.Q ^ S.η) ^ 6 * S.W :=
        mul_le_mul_of_nonneg_right h6 hW.le
    _ = S.L ^ 4 * (S.Q ^ S.η) ^ 6 * 1 * S.W := by ring
    _ ≤ S.L ^ 4 * (S.Q ^ S.η) ^ 6 * 𝔈 ^ 2 * S.W := by gcongr

set_option maxHeartbeats 2000000 in
/-- **The bound for `A₀`.** -/
theorem boundJ0_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {Eexc KE 𝔈 : ℝ} (hKE : 0 ≤ KE)
    (h𝔈 : 1 ≤ 𝔈) (hE : Eexc ≤ KE * (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W)) :
    S.boundJ0 Cls Eexc ≤ S.KJ0 Cls KE * (S.Bk * S.L ^ 2 * (S.Q ^ S.η) ^ 3 * 𝔈) ^ 2 * S.W := by
  set x := S.Q ^ S.η with hx
  set c := Real.cosh Real.pi with hc
  set A := S.M ^ (1 + S.η) / S.q with hA
  set Z := S.L ^ 4 * x ^ 6 * 𝔈 ^ 2 * S.W with hZ
  have hx1 : 1 ≤ x := S.Qη_ge
  have hx0 : 0 < x := S.Qη_pos
  have hc0 : 0 < c := Real.cosh_pos _
  have hC0 := S.C₀_nonneg
  have hM := S.M_pos
  have hW := S.W_pos
  have hη := S.hη
  have hq := S.q_pos
  have hQ := S.Q_pos
  have hL1 := S.one_le_L
  have hL0 := S.L_pos
  have hA0 : 0 ≤ A := S.A_nonneg
  have hℓ0 : 0 ≤ S.ℓ := S.ℓ_pos.le
  have hℓ : S.ℓ ≤ 6 * x / S.η := S.ℓ_le
  have h𝔈2 : 1 ≤ 𝔈 ^ 2 := one_le_pow₀ h𝔈
  have hcCls : 0 ≤ c * Cls S.η := mul_nonneg hc0.le hCls
  -- the units
  have hu2 : x ^ 2 * S.W ≤ Z := by
    have := S.pow_le_unit h𝔈 (a := 2) (b := 0) (by norm_num) (by norm_num)
    simpa [hx, hZ] using this
  have hu4 : x ^ 4 * S.W ≤ Z := by
    have := S.pow_le_unit h𝔈 (a := 4) (b := 0) (by norm_num) (by norm_num)
    simpa [hx, hZ] using this
  have hu5 : S.L ^ 3 * x ^ 5 * 𝔈 ^ 2 * S.W ≤ Z := by
    have h1 : S.L ^ 3 ≤ S.L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : 0 ≤ 𝔈 ^ 2 * S.W := by positivity
    calc S.L ^ 3 * x ^ 5 * 𝔈 ^ 2 * S.W = S.L ^ 3 * x ^ 5 * (𝔈 ^ 2 * S.W) := by ring
      _ ≤ S.L ^ 4 * x ^ 6 * (𝔈 ^ 2 * S.W) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
      _ = Z := by rw [hZ]; ring
  -- the factor `C₀² ℓ²`
  have hP1a : S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ ≤ 36 * S.C₀ ^ 2 / S.η ^ 2 * x ^ 2 := by
    have e : S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ = S.C₀ ^ 2 * S.ℓ ^ 2 := by ring
    rw [e]
    have : S.ℓ ^ 2 ≤ (6 * x / S.η) ^ 2 := pow_le_pow_left₀ hℓ0 hℓ 2
    calc S.C₀ ^ 2 * S.ℓ ^ 2 ≤ S.C₀ ^ 2 * (6 * x / S.η) ^ 2 :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = 36 * S.C₀ ^ 2 / S.η ^ 2 * x ^ 2 := by field_simp; ring
  -- the inner factor
  have hin1 : c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) ≤
      24 * c * Cls S.η * S.C₀ ^ 2 * (x ^ 2 * S.W) := by
    have h := S.one_add_A_mul_le
    rw [← hx, ← hA] at h
    have e : c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) =
        (8 * S.C₀ ^ 2) * (c * Cls S.η) * ((1 + A) * S.M) := by ring
    rw [e]
    calc (8 * S.C₀ ^ 2) * (c * Cls S.η) * ((1 + A) * S.M)
        ≤ (8 * S.C₀ ^ 2) * (c * Cls S.η) * (3 * x ^ 2 * S.W) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (by positivity) hcCls)
      _ = 24 * c * Cls S.η * S.C₀ ^ 2 * (x ^ 2 * S.W) := by ring
  have h24 : 0 ≤ 24 * c * Cls S.η * S.C₀ ^ 2 := by
    have : 24 * c * Cls S.η * S.C₀ ^ 2 = 24 * S.C₀ ^ 2 * (c * Cls S.η) := by ring
    rw [this]; exact mul_nonneg (by positivity) hcCls
  set Rin := 24 * c * Cls S.η * S.C₀ ^ 2 * (x ^ 2 * S.W) +
    KE * (S.L ^ 3 * x ^ 3 * 𝔈 ^ 2 * S.W) with hRin
  have hRin0 : 0 ≤ Rin := by
    apply add_nonneg (mul_nonneg h24 (by positivity)) (mul_nonneg hKE (by positivity))
  -- `P1`
  have hP1 : S.ℓ / 4 * (2 * S.C₀) ^ 2 *
      (S.ℓ * (c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) + Eexc)) ≤
      36 * S.C₀ ^ 2 / S.η ^ 2 * (24 * c * Cls S.η * S.C₀ ^ 2 + KE) * Z := by
    have hf0 : 0 ≤ S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ := by positivity
    have e1 : S.ℓ / 4 * (2 * S.C₀) ^ 2 *
        (S.ℓ * (c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) + Eexc)) =
        (S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ) *
          (c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) + Eexc) := by ring
    rw [e1]
    have e2 : 36 * S.C₀ ^ 2 / S.η ^ 2 * x ^ 2 * Rin = 36 * S.C₀ ^ 2 / S.η ^ 2 *
        (24 * c * Cls S.η * S.C₀ ^ 2 * (x ^ 4 * S.W) + KE * (S.L ^ 3 * x ^ 5 * 𝔈 ^ 2 * S.W)) := by
      rw [hRin]; ring
    have h36 : 0 ≤ 36 * S.C₀ ^ 2 / S.η ^ 2 := by positivity
    calc (S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ) *
          (c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) + Eexc)
        ≤ (S.ℓ / 4 * (2 * S.C₀) ^ 2 * S.ℓ) * Rin :=
          mul_le_mul_of_nonneg_left (add_le_add hin1 hE) hf0
      _ ≤ (36 * S.C₀ ^ 2 / S.η ^ 2 * x ^ 2) * Rin := mul_le_mul_of_nonneg_right hP1a hRin0
      _ = 36 * S.C₀ ^ 2 / S.η ^ 2 *
          (24 * c * Cls S.η * S.C₀ ^ 2 * (x ^ 4 * S.W) + KE * (S.L ^ 3 * x ^ 5 * 𝔈 ^ 2 * S.W)) := e2
      _ ≤ 36 * S.C₀ ^ 2 / S.η ^ 2 * (24 * c * Cls S.η * S.C₀ ^ 2 * Z + KE * Z) := by
          apply mul_le_mul_of_nonneg_left _ h36
          exact add_le_add (mul_le_mul_of_nonneg_left hu4 h24) (mul_le_mul_of_nonneg_left hu5 hKE)
      _ = _ := by ring
  -- `P2`
  have hsum : ∑ h ∈ S.Hs, c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)) ≤
      2 * S.M * (c * Cls S.η * (1 + A)) := by
    calc ∑ h ∈ S.Hs, c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q))
        ≤ ∑ _h ∈ S.Hs, c * Cls S.η * (1 + A) := by
          apply Finset.sum_le_sum
          intro h hh
          have h2 := (S.le_of_mem_Hs hh).2
          have h3 : (h : ℝ) / 2 ≤ S.M := by linarith
          have h4 : ((h : ℝ) / 2) ^ (1 + S.η) ≤ S.M ^ (1 + S.η) :=
            Real.rpow_le_rpow (by positivity) h3 (by linarith)
          have h5 : ((h : ℝ) / 2) ^ (1 + S.η) / S.q ≤ A := by
            rw [hA]; exact div_le_div_of_nonneg_right h4 hq.le
          calc c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q))
              = c * Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q) := by ring
            _ ≤ c * Cls S.η * (1 + A) := by
                apply mul_le_mul_of_nonneg_left _ hcCls; linarith
      _ = ((S.Hs).card : ℝ) * (c * Cls S.η * (1 + A)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * S.M * (c * Cls S.η * (1 + A)) :=
          mul_le_mul_of_nonneg_right S.card_Hs_le (mul_nonneg hcCls (by linarith))
  have hP2 : 2 * S.M * S.eps0 ^ 2 *
      ∑ h ∈ S.Hs, c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)) ≤
      24 * c * Cls S.η * (32 * S.C₀ ^ 2 / Real.pi) ^ 2 *
        ((Nat.ceil (4 / S.η)).factorial : ℝ) * Z := by
    have he := S.eps0_sq_le
    rw [← hx] at he
    have hQ4 := S.Q4_exp_le
    rw [← hx] at hQ4
    have hMQ := S.M_le_Q2
    have h1A := S.one_add_A_mul_le
    rw [← hx, ← hA] at h1A
    have hε0 : 0 ≤ S.eps0 ^ 2 := sq_nonneg _
    have hK0 : 0 ≤ (32 * S.C₀ ^ 2 / Real.pi) ^ 2 := sq_nonneg _
    have hexp : 0 < Real.exp (-(Real.pi * x)) := Real.exp_pos _
    calc 2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q))
        ≤ 2 * S.M * S.eps0 ^ 2 * (2 * S.M * (c * Cls S.η * (1 + A))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * (c * Cls S.η) * S.eps0 ^ 2 * S.M * ((1 + A) * S.M) := by ring
      _ ≤ 4 * (c * Cls S.η) * S.eps0 ^ 2 * (2 * S.Q ^ 2) * (3 * x ^ 2 * S.W) := by
          apply mul_le_mul _ h1A (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hMQ (by positivity)
      _ = 24 * (c * Cls S.η) * S.eps0 ^ 2 * S.Q ^ 2 * (x ^ 2 * S.W) := by ring
      _ ≤ 24 * (c * Cls S.η) * ((32 * S.C₀ ^ 2 / Real.pi) ^ 2 * S.Q ^ 2 *
            Real.exp (-(Real.pi * x))) * S.Q ^ 2 * (x ^ 2 * S.W) := by
          gcongr
      _ = 24 * (c * Cls S.η) * (32 * S.C₀ ^ 2 / Real.pi) ^ 2 *
            (S.Q ^ 4 * Real.exp (-(Real.pi * x))) * (x ^ 2 * S.W) := by ring
      _ ≤ 24 * (c * Cls S.η) * (32 * S.C₀ ^ 2 / Real.pi) ^ 2 *
            ((Nat.ceil (4 / S.η)).factorial : ℝ) * Z := by
          apply mul_le_mul _ hu2 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hQ4 (mul_nonneg (by positivity) hK0)
      _ = _ := by ring
  -- assembling
  have hBk := S.Bk_pos
  unfold boundJ0
  rw [← hc, ← hA]
  calc 2 * S.Bk ^ 2 * (S.ℓ / 4 * (2 * S.C₀) ^ 2 *
        (S.ℓ * (c * Cls S.η * (1 + A) * (2 * S.M * (2 * S.C₀) ^ 2) + Eexc)) +
        2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, c * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)))
      ≤ 2 * S.Bk ^ 2 * (36 * S.C₀ ^ 2 / S.η ^ 2 * (24 * c * Cls S.η * S.C₀ ^ 2 + KE) * Z +
          24 * c * Cls S.η * (32 * S.C₀ ^ 2 / Real.pi) ^ 2 *
            ((Nat.ceil (4 / S.η)).factorial : ℝ) * Z) :=
        mul_le_mul_of_nonneg_left (add_le_add hP1 hP2) (by positivity)
    _ = S.KJ0 Cls KE * (S.Bk * S.L ^ 2 * x ^ 3 * 𝔈) ^ 2 * S.W := by
        rw [hZ]; unfold KJ0; rw [← hc]; ring

end Setup

end Triples
