import TriplesFinal.TypeIProof.BoundJ0

/-!
# The bounds for `A₁` and for the tail, and the bound for the spectral side

`3(2·main + rem(1, T₁)) ≤ K₁ ((X/K) Y^(-1/2) T₁² Q^(2η) L⁶)² W`,
`W_tail ≤ K₂ ((X/K) Y^(-1/2) Q^(3η) L⁹)² W P`, and together with the bound for `A₀`:
the right-hand side of `spectral_side'` is `≤ K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √W √P`.

Paper: §§12.2–12.4.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν)

/-- The constant of the bound for `A₁`. -/
noncomputable def KA1 (Cls : ℝ → ℝ) (Cψ Cd C6' CGt : ℝ) : ℝ :=
  3 * (2 * (21 * ((2 * S.C₀ ^ 2) ^ 2 + ((Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd) ^ 2) * Cls S.η) +
    c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 6 * (2 * Real.pi) ^ 3 * C6' ^ 2)

/-- The constant of the bound for the tail. -/
noncomputable def KT (Cls : ℝ → ℝ) (C6' CGt Ckt : ℝ) : ℝ :=
  3 * (2 * (84 * Cls S.η * Ckt ^ 2) +
    c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 12 * (2 * Real.pi) ^ 3 * C6' ^ 2) *
      (1024 / Real.pi)

theorem c₂c₅_nonneg : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) := by
  have := c₂_nonneg; have := c₅_nonneg; positivity

set_option maxHeartbeats 2000000 in
/-- **The bound for `A₁`.** -/
theorem boundA1_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {Cψ Cd C6' CGt : ℝ} :
    3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁) ≤
      S.KA1 Cls Cψ Cd C6' CGt * (S.Bk * S.T₁ ^ 2 * (S.Q ^ S.η) ^ 2 * S.L ^ 6) ^ 2 * S.W := by
  set x := S.Q ^ S.η with hx
  set A := S.M ^ (1 + S.η) / S.q with hA
  set K₁ := (Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd with hK₁
  have hx1 : 1 ≤ x := S.Qη_ge
  have hx0 : 0 < x := S.Qη_pos
  have hT1 := S.one_le_T₁
  have hT0 : 0 < S.T₁ := S.T₁_pos
  have hL1 := S.one_le_L
  have hL0 := S.L_pos
  have hW := S.W_pos
  have hM := S.M_pos
  have hBk := S.Bk_pos
  have hpi := Real.pi_pos
  have hc25 := c₂c₅_nonneg
  -- the main terms
  have hmain : S.boundMain Cls Cψ Cd ≤
      21 * ((2 * S.C₀ ^ 2) ^ 2 + K₁ ^ 2) * Cls S.η * (S.Bk ^ 2 * S.T₁ ^ 4 * S.W) := by
    unfold boundMain
    rw [← hA, ← hK₁]
    have h1 : (2 * S.C₀ ^ 2) ^ 2 + (K₁ * S.T₁) ^ 2 ≤ ((2 * S.C₀ ^ 2) ^ 2 + K₁ ^ 2) * S.T₁ ^ 2 := by
      have : 1 ≤ S.T₁ ^ 2 := one_le_pow₀ hT1
      have h0 : 0 ≤ (2 * S.C₀ ^ 2) ^ 2 := sq_nonneg _
      nlinarith
    have h2 : Cls S.η * (S.T₁ ^ 2 + A) * (2 * S.M) ≤ Cls S.η * (6 * S.T₁ ^ 2 * S.W) := by
      have h := S.T1sq_add_A_mul_le
      rw [← hA] at h
      have e : Cls S.η * (S.T₁ ^ 2 + A) * (2 * S.M) = Cls S.η * (2 * ((S.T₁ ^ 2 + A) * S.M)) := by
        ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hCls
      linarith
    have h3 : 0 ≤ Cls S.η * (S.T₁ ^ 2 + A) * (2 * S.M) := by
      have := S.A_nonneg; rw [← hA] at this
      apply mul_nonneg (mul_nonneg hCls (by positivity)) (by positivity)
    calc S.Bk ^ 2 * (7 / 4) * (2 * ((2 * S.C₀ ^ 2) ^ 2 + (K₁ * S.T₁) ^ 2) *
          (Cls S.η * (S.T₁ ^ 2 + A) * (2 * S.M)))
        ≤ S.Bk ^ 2 * (7 / 4) * (2 * (((2 * S.C₀ ^ 2) ^ 2 + K₁ ^ 2) * S.T₁ ^ 2) *
            (Cls S.η * (6 * S.T₁ ^ 2 * S.W))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul (by linarith) h2 h3 (by positivity)
      _ = _ := by ring
  -- the remainder term
  have hrem : S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁ ≤
      c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 6 * (2 * Real.pi) ^ 3 * C6' ^ 2 *
        (S.Bk ^ 2 * S.T₁ ^ 2 * x ^ 3 * S.L ^ 12 * S.W) := by
    unfold boundRem
    rw [← hA]
    have h1 : (1 + (1 : ℝ)) ^ (-(5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have h1' : 0 ≤ (1 + (1 : ℝ)) ^ (-(5 : ℝ)) := by positivity
    have h2 := S.fourPiMY_le
    rw [← hx] at h2
    have h3 := S.T1sq_add_A_mul_le
    rw [← hA] at h3
    have hA0 : 0 ≤ A := by have := S.A_nonneg; rwa [← hA] at this
    have e : S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (1 + 1) ^ (-(5 : ℝ)) *
        (Cls S.η * (S.T₁ ^ 2 + A)) *
          (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6' * S.L ^ 6)) ^ 2) * c₅) =
        (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          ((1 + 1) ^ (-(5 : ℝ)) * ((S.T₁ ^ 2 + A) * S.M) *
            ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 * (S.Bk ^ 2 * S.L ^ 12)) := by
      ring
    rw [e]
    have hk0 : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2 := by
      have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
        mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
      positivity
    have hTA : 0 ≤ (S.T₁ ^ 2 + A) * S.M := by positivity
    calc (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          ((1 + 1) ^ (-(5 : ℝ)) * ((S.T₁ ^ 2 + A) * S.M) *
            ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 * (S.Bk ^ 2 * S.L ^ 12))
        ≤ (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          (1 * (3 * S.T₁ ^ 2 * S.W) * (2 * Real.pi * x) ^ 3 * (S.Bk ^ 2 * S.L ^ 12)) := by
          apply mul_le_mul_of_nonneg_left _ hk0
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul (mul_le_mul h1 h3 hTA zero_le_one) h2 (by positivity) (by positivity)
      _ = _ := by ring
  -- combining
  have hK : 0 ≤ 21 * ((2 * S.C₀ ^ 2) ^ 2 + K₁ ^ 2) * Cls S.η :=
    mul_nonneg (by positivity) hCls
  have hu1 : S.Bk ^ 2 * S.T₁ ^ 4 * S.W ≤ (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W := by
    have h1 : 1 ≤ x ^ 4 := one_le_pow₀ hx1
    have h2 : 1 ≤ S.L ^ 12 := one_le_pow₀ hL1
    have e : (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W =
        S.Bk ^ 2 * S.T₁ ^ 4 * S.W * (x ^ 4 * S.L ^ 12) := by ring
    rw [e]
    have : 1 ≤ x ^ 4 * S.L ^ 12 := one_le_mul_of_one_le_of_one_le h1 h2
    have h0 : 0 ≤ S.Bk ^ 2 * S.T₁ ^ 4 * S.W := by positivity
    nlinarith
  have hu2 : S.Bk ^ 2 * S.T₁ ^ 2 * x ^ 3 * S.L ^ 12 * S.W ≤
      (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W := by
    have e : (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W =
        S.Bk ^ 2 * S.T₁ ^ 2 * x ^ 3 * S.L ^ 12 * S.W * (S.T₁ ^ 2 * x) := by ring
    rw [e]
    have : 1 ≤ S.T₁ ^ 2 * x := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hT1) hx1
    have h0 : 0 ≤ S.Bk ^ 2 * S.T₁ ^ 2 * x ^ 3 * S.L ^ 12 * S.W := by positivity
    nlinarith
  have hKR : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 6 * (2 * Real.pi) ^ 3 *
      C6' ^ 2 := by
    have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
      mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
    positivity
  calc 3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁)
      ≤ 3 * (2 * (21 * ((2 * S.C₀ ^ 2) ^ 2 + K₁ ^ 2) * Cls S.η *
          ((S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W)) +
          c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 6 * (2 * Real.pi) ^ 3 * C6' ^ 2 *
            ((S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W)) := by
        have := mul_le_mul_of_nonneg_left hu1 hK
        have := mul_le_mul_of_nonneg_left hu2 hKR
        linarith
    _ = S.KA1 Cls Cψ Cd C6' CGt * (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) ^ 2 * S.W := by
        unfold KA1; rw [← hK₁]; ring

set_option maxHeartbeats 2000000 in
/-- **The bound for the tail.** -/
theorem Wtail_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {C6' CGt k Ck Ckt P : ℝ} (hP : 0 ≤ P)
    (hCk0 : 0 ≤ Ck * S.T₁ ^ (-(k - 3))) (hCkt : Ck * S.T₁ ^ (-(k - 3)) * S.Q ≤ Ckt * S.L ^ 3) :
    S.Wtail Cls (C6' * S.L ^ 6) CGt k Ck P ≤
      S.KT Cls C6' CGt Ckt * (S.Bk * (S.Q ^ S.η) ^ 3 * S.L ^ 9) ^ 2 * S.W * P := by
  set x := S.Q ^ S.η with hx
  set A := S.M ^ (1 + S.η) / S.q with hA
  set ε := Ck * S.T₁ ^ (-(k - 3)) with hε
  have hx1 : 1 ≤ x := S.Qη_ge
  have hx0 : 0 < x := S.Qη_pos
  have hL1 := S.one_le_L
  have hL0 := S.L_pos
  have hW := S.W_pos
  have hM := S.M_pos
  have hBk := S.Bk_pos
  have hpi := Real.pi_pos
  have hQ := S.Q_pos
  have hc25 := c₂c₅_nonneg
  have hA0 : 0 ≤ A := by have := S.A_nonneg; rwa [← hA] at this
  have hCkt0 : 0 ≤ Ckt := by
    have h1 : 0 ≤ Ckt * S.L ^ 3 := le_trans (mul_nonneg hCk0 hQ.le) hCkt
    have h2 : 0 < S.L ^ 3 := by positivity
    nlinarith
  have hMε : S.M * ε ^ 2 ≤ 2 * (Ckt * S.L ^ 3) ^ 2 := by
    have h1 := S.M_le_Q2
    have h2 : (ε * S.Q) ^ 2 ≤ (Ckt * S.L ^ 3) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCk0 hQ.le) hCkt 2
    calc S.M * ε ^ 2 ≤ 2 * S.Q ^ 2 * ε ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 2 * (ε * S.Q) ^ 2 := by ring
      _ ≤ 2 * (Ckt * S.L ^ 3) ^ 2 := by linarith
  have h4A := S.four_add_A_mul_le
  rw [← hx, ← hA] at h4A
  have h4A0 : 0 ≤ (4 + A) * S.M := by positivity
  -- the first part
  have hfirst : S.Bk ^ 2 * (7 / 4) * (2 * S.M * ε ^ 2) * (2 * S.M * (Cls S.η * (4 + A))) ≤
      84 * Cls S.η * Ckt ^ 2 * (S.Bk ^ 2 * x ^ 2 * S.L ^ 6 * S.W) := by
    have e : S.Bk ^ 2 * (7 / 4) * (2 * S.M * ε ^ 2) * (2 * S.M * (Cls S.η * (4 + A))) =
        (7 * Cls S.η * S.Bk ^ 2) * ((S.M * ε ^ 2) * ((4 + A) * S.M)) := by ring
    rw [e]
    have h7 : 0 ≤ 7 * Cls S.η * S.Bk ^ 2 := by positivity
    calc (7 * Cls S.η * S.Bk ^ 2) * ((S.M * ε ^ 2) * ((4 + A) * S.M))
        ≤ (7 * Cls S.η * S.Bk ^ 2) * ((2 * (Ckt * S.L ^ 3) ^ 2) * (6 * x ^ 2 * S.W)) := by
          apply mul_le_mul_of_nonneg_left _ h7
          exact mul_le_mul hMε h4A h4A0 (by positivity)
      _ = _ := by ring
  -- the second part
  have hsecond : S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (Cls S.η * (4 + A)) *
      (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6' * S.L ^ 6)) ^ 2) * c₅) ≤
      c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 12 * (2 * Real.pi) ^ 3 * C6' ^ 2 *
        (S.Bk ^ 2 * x ^ 5 * S.L ^ 12 * S.W) := by
    have h2 := S.fourPiMY_le
    rw [← hx] at h2
    have e : S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (Cls S.η * (4 + A)) *
        (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6' * S.L ^ 6)) ^ 2) * c₅) =
        (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          (((4 + A) * S.M) * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 *
            (S.Bk ^ 2 * S.L ^ 12)) := by ring
    rw [e]
    have hk0 : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2 := by
      have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
        mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
      positivity
    calc (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          (((4 + A) * S.M) * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ)) ^ 2 *
            (S.Bk ^ 2 * S.L ^ 12))
        ≤ (c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 2 * C6' ^ 2) *
          ((6 * x ^ 2 * S.W) * (2 * Real.pi * x) ^ 3 * (S.Bk ^ 2 * S.L ^ 12)) := by
          apply mul_le_mul_of_nonneg_left _ hk0
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul h4A h2 (by positivity) (by positivity)
      _ = _ := by ring
  -- the units
  have hu1 : S.Bk ^ 2 * x ^ 2 * S.L ^ 6 * S.W ≤ (S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W := by
    have e : (S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W =
        S.Bk ^ 2 * x ^ 2 * S.L ^ 6 * S.W * (x ^ 4 * S.L ^ 12) := by
      ring
    rw [e]
    have : 1 ≤ x ^ 4 * S.L ^ 12 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) (one_le_pow₀ hL1)
    have h0 : 0 ≤ S.Bk ^ 2 * x ^ 2 * S.L ^ 6 * S.W := by positivity
    nlinarith
  have hu2 : S.Bk ^ 2 * x ^ 5 * S.L ^ 12 * S.W ≤ (S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W := by
    have e : (S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W =
        S.Bk ^ 2 * x ^ 5 * S.L ^ 12 * S.W * (x * S.L ^ 6) := by ring
    rw [e]
    have : 1 ≤ x * S.L ^ 6 := one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hL1)
    have h0 : 0 ≤ S.Bk ^ 2 * x ^ 5 * S.L ^ 12 * S.W := by positivity
    nlinarith
  have hK84 : 0 ≤ 84 * Cls S.η * Ckt ^ 2 := by positivity
  have hKR : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 12 * (2 * Real.pi) ^ 3 *
      C6' ^ 2 := by
    have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
      mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
    positivity
  have hP' : 0 ≤ 1024 / Real.pi * P := by positivity
  unfold Wtail
  rw [← hA, ← hε]
  calc 3 * (2 * (S.Bk ^ 2 * (7 / 4) * (2 * S.M * ε ^ 2) * (2 * S.M * (Cls S.η * (4 + A)))) +
        S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (Cls S.η * (4 + A)) *
          (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * (C6' * S.L ^ 6)) ^ 2) * c₅)) *
        (1024 / Real.pi * P)
      ≤ 3 * (2 * (84 * Cls S.η * Ckt ^ 2 * ((S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W)) +
          c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η * 12 * (2 * Real.pi) ^ 3 * C6' ^ 2 *
            ((S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W)) * (1024 / Real.pi * P) := by
        apply mul_le_mul_of_nonneg_right _ hP'
        have := mul_le_mul_of_nonneg_left hu1 hK84
        have := mul_le_mul_of_nonneg_left hu2 hKR
        linarith
    _ = S.KT Cls C6' CGt Ckt * (S.Bk * x ^ 3 * S.L ^ 9) ^ 2 * S.W * P := by
        unfold KT; ring

theorem sqrt_mul_sq_mul {K Z W : ℝ} (hK : 0 ≤ K) (hZ : 0 ≤ Z) :
    Real.sqrt (K * Z ^ 2 * W) = Real.sqrt K * Z * Real.sqrt W := by
  rw [Real.sqrt_mul (by positivity) W, Real.sqrt_mul hK, Real.sqrt_sq hZ]

/-- The constant of the bound for the spectral side. -/
noncomputable def Kspec (Cls : ℝ → ℝ) (KE Cψ Cd C6' CGt Ckt : ℝ) : ℝ :=
  Real.sqrt (S.KJ0 Cls KE) * Real.sqrt (256 / Real.pi) +
    Real.sqrt (S.KA1 Cls Cψ Cd C6' CGt) * Real.sqrt (256 / Real.pi) +
    Real.sqrt (S.KT Cls C6' CGt Ckt) * (1 - Real.sqrt (1 / 2))⁻¹

set_option maxHeartbeats 2000000 in
/-- **The bound for the spectral side**:
the right-hand side of `spectral_side'` is `≤ K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √W √P`. -/
theorem spectral_rhs_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {Eexc KE 𝔈 : ℝ} (hKE : 0 ≤ KE)
    (h𝔈 : 1 ≤ 𝔈) (hE : Eexc ≤ KE * (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W))
    {Cψ Cd C6' CGt k Ck Ckt P : ℝ} (hP : 0 ≤ P)
    (hCk0 : 0 ≤ Ck * S.T₁ ^ (-(k - 3))) (hCkt : Ck * S.T₁ ^ (-(k - 3)) * S.Q ≤ Ckt * S.L ^ 3) :
    Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * P) +
      Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁)) *
        Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) +
      Real.sqrt (S.Wtail Cls (C6' * S.L ^ 6) CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹ ≤
    S.Kspec Cls KE Cψ Cd C6' CGt Ckt * (S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈) *
      Real.sqrt S.W * Real.sqrt P := by
  set x := S.Q ^ S.η with hx
  have hx1 : 1 ≤ x := S.Qη_ge
  have hx0 : 0 < x := S.Qη_pos
  have hL1 := S.one_le_L
  have hL0 := S.L_pos
  have hW := S.W_pos
  have hBk := S.Bk_pos
  have hpi := Real.pi_pos
  have hT1 := S.one_le_T₁
  have h𝔈0 : 0 ≤ 𝔈 := by linarith
  have hsW := Real.sqrt_nonneg S.W
  have hsP := Real.sqrt_nonneg P
  have hs2 : 0 ≤ (1 - Real.sqrt (1 / 2))⁻¹ := by
    have := sqrt_half_lt_one; rw [inv_nonneg]; linarith
  set Zf := S.Bk * S.L ^ 9 * x ^ 6 * 𝔈 with hZf
  -- the three constants
  have hK0 : 0 ≤ S.KJ0 Cls KE := S.KJ0_nonneg hCls hKE
  have hK1 : 0 ≤ S.KA1 Cls Cψ Cd C6' CGt := by
    unfold KA1
    have hc25 := c₂c₅_nonneg
    have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
      mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
    have : 0 ≤ 21 * ((2 * S.C₀ ^ 2) ^ 2 + ((Cψ + 1) * (2 * S.C₀ ^ 2) + 2 * Cd) ^ 2) * Cls S.η :=
      mul_nonneg (by positivity) hCls
    positivity
  have hK2 : 0 ≤ S.KT Cls C6' CGt Ckt := by
    unfold KT
    have hc25 := c₂c₅_nonneg
    have : 0 ≤ c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls S.η :=
      mul_nonneg (mul_nonneg hc25 (sq_nonneg _)) hCls
    have : 0 ≤ 84 * Cls S.η * Ckt ^ 2 := by positivity
    positivity
  -- the unit comparisons
  have hZ0 : S.Bk * S.L ^ 2 * x ^ 3 * 𝔈 ≤ Zf := by
    have h1 : S.L ^ 2 ≤ S.L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    rw [hZf]
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h3 : 0 ≤ S.Bk * 𝔈 := by positivity
    nlinarith
  have hZ1 : S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6 * S.T₁ ≤ Zf := by
    have e : S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6 * S.T₁ = S.Bk * S.L ^ 9 * x ^ 5 := by
      rw [S.T₁_eq]; ring
    rw [e, hZf]
    have h2 : x ^ 5 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    have h3 : 0 ≤ S.Bk * S.L ^ 9 := by positivity
    have h4 : x ^ 6 ≤ x ^ 6 * 𝔈 := le_mul_of_one_le_right (by positivity) h𝔈
    nlinarith
  have hZ2 : S.Bk * x ^ 3 * S.L ^ 9 ≤ Zf := by
    have h2 : x ^ 3 ≤ x ^ 6 := pow_le_pow_right₀ hx1 (by norm_num)
    rw [hZf]
    have h4 : 0 ≤ S.Bk * S.L ^ 9 := by positivity
    have h5 : x ^ 6 ≤ x ^ 6 * 𝔈 := le_mul_of_one_le_right (by positivity) h𝔈
    have e : S.Bk * S.L ^ 9 * x ^ 6 * 𝔈 = (S.Bk * S.L ^ 9) * (x ^ 6 * 𝔈) := by ring
    have e' : S.Bk * x ^ 3 * S.L ^ 9 = (S.Bk * S.L ^ 9) * x ^ 3 := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left (h2.trans h5) h4
  -- `T₀`
  have hT0 : Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * P) ≤
      Real.sqrt (S.KJ0 Cls KE) * Real.sqrt (256 / Real.pi) * Zf * Real.sqrt S.W * Real.sqrt P := by
    have h1 := Real.sqrt_le_sqrt (S.boundJ0_le hCls hKE h𝔈 hE)
    rw [sqrt_mul_sq_mul hK0 (by positivity)] at h1
    rw [Real.sqrt_mul (by positivity) P]
    calc Real.sqrt (S.boundJ0 Cls Eexc) * (Real.sqrt (256 / Real.pi) * Real.sqrt P)
        ≤ (Real.sqrt (S.KJ0 Cls KE) * (S.Bk * S.L ^ 2 * x ^ 3 * 𝔈) * Real.sqrt S.W) *
            (Real.sqrt (256 / Real.pi) * Real.sqrt P) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Real.sqrt (S.KJ0 Cls KE) * Zf * Real.sqrt S.W) *
            (Real.sqrt (256 / Real.pi) * Real.sqrt P) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hsW
          exact mul_le_mul_of_nonneg_left hZ0 (Real.sqrt_nonneg _)
      _ = _ := by ring
  -- `T₁`
  have hT1' : Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁)) *
        Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) ≤
      Real.sqrt (S.KA1 Cls Cψ Cd C6' CGt) * Real.sqrt (256 / Real.pi) * Zf * Real.sqrt S.W *
        Real.sqrt P := by
    have h1 := Real.sqrt_le_sqrt (S.boundA1_le hCls (Cψ := Cψ) (Cd := Cd) (C6' := C6')
      (CGt := CGt))
    rw [sqrt_mul_sq_mul hK1 (by positivity)] at h1
    have e : Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) =
        Real.sqrt (256 / Real.pi) * S.T₁ * Real.sqrt P := by
      rw [Real.sqrt_mul (by positivity) P, Real.sqrt_mul (by positivity) (S.T₁ ^ 2),
        Real.sqrt_sq (by linarith)]
    rw [e]
    calc Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁)) *
          (Real.sqrt (256 / Real.pi) * S.T₁ * Real.sqrt P)
        ≤ (Real.sqrt (S.KA1 Cls Cψ Cd C6' CGt) * (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6) *
            Real.sqrt S.W) * (Real.sqrt (256 / Real.pi) * S.T₁ * Real.sqrt P) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Real.sqrt (S.KA1 Cls Cψ Cd C6' CGt) * Real.sqrt (256 / Real.pi) *
            (S.Bk * S.T₁ ^ 2 * x ^ 2 * S.L ^ 6 * S.T₁) * Real.sqrt S.W * Real.sqrt P := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hsP
          apply mul_le_mul_of_nonneg_right _ hsW
          exact mul_le_mul_of_nonneg_left hZ1 (by positivity)
  -- the tail
  have hT2 : Real.sqrt (S.Wtail Cls (C6' * S.L ^ 6) CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹ ≤
      Real.sqrt (S.KT Cls C6' CGt Ckt) * (1 - Real.sqrt (1 / 2))⁻¹ * Zf * Real.sqrt S.W *
        Real.sqrt P := by
    have h1 := Real.sqrt_le_sqrt (S.Wtail_le hCls hP hCk0 hCkt (C6' := C6') (CGt := CGt))
    rw [Real.sqrt_mul (by have := S.W_pos; positivity) P, sqrt_mul_sq_mul hK2 (by positivity)] at h1
    calc Real.sqrt (S.Wtail Cls (C6' * S.L ^ 6) CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹
        ≤ (Real.sqrt (S.KT Cls C6' CGt Ckt) * (S.Bk * x ^ 3 * S.L ^ 9) * Real.sqrt S.W *
            Real.sqrt P) * (1 - Real.sqrt (1 / 2))⁻¹ := mul_le_mul_of_nonneg_right h1 hs2
      _ ≤ (Real.sqrt (S.KT Cls C6' CGt Ckt) * Zf * Real.sqrt S.W * Real.sqrt P) *
            (1 - Real.sqrt (1 / 2))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hs2
          apply mul_le_mul_of_nonneg_right _ hsP
          apply mul_le_mul_of_nonneg_right _ hsW
          exact mul_le_mul_of_nonneg_left hZ2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  calc _ ≤ Real.sqrt (S.KJ0 Cls KE) * Real.sqrt (256 / Real.pi) * Zf * Real.sqrt S.W *
        Real.sqrt P + Real.sqrt (S.KA1 Cls Cψ Cd C6' CGt) * Real.sqrt (256 / Real.pi) * Zf *
        Real.sqrt S.W * Real.sqrt P + Real.sqrt (S.KT Cls C6' CGt Ckt) *
        (1 - Real.sqrt (1 / 2))⁻¹ * Zf * Real.sqrt S.W * Real.sqrt P :=
        add_le_add (add_le_add hT0 hT1') hT2
    _ = _ := by unfold Kspec; ring

end Setup

end Triples
