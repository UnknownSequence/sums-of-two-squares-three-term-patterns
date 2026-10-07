import TriplesFinal.TypeIProof.SpectralSide

/-!
# Summability over the dyadic blocks

For `R = 2^m T₁` the block bounds satisfy `A_{m+2} · 256/π (2R)² P ≤ W/(1 + R)`
(`tail_term_le`), so the terms of the Cauchy–Schwarz series are `≤ √W (1/√2)^m` and the
series converges (`summable_blocks`). This gives `spectral_side`.

Paper: §§12.3–12.4 (summing over `k ≥ 0`).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

theorem sqrt_half_pow (m : ℕ) : Real.sqrt ((1 / 2 : ℝ) ^ m) = Real.sqrt (1 / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- The constant of the tail terms. -/
noncomputable def Wtail (Cls : ℝ → ℝ) (C6 CGt k Ck P : ℝ) : ℝ :=
  3 * (2 * (S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * S.T₁ ^ (-(k - 3))) ^ 2) *
      (2 * S.M * (Cls S.η * (4 + S.M ^ (1 + S.η) / S.q)))) +
    S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 *
      (Cls S.η * (4 + S.M ^ (1 + S.η) / S.q)) *
        (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅)) *
    (1024 / Real.pi * P)

theorem Wtail_nonneg {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {C6 CGt k Ck P : ℝ} (hP : 0 ≤ P) :
    0 ≤ S.Wtail Cls C6 CGt k Ck P := by
  have hM := S.M_pos
  have hq := S.q_pos
  have hY := S.Y_pos
  have h2 := c₂_nonneg
  have h5 := c₅_nonneg
  have hA : 0 ≤ Cls S.η * (4 + S.M ^ (1 + S.η) / S.q) := mul_nonneg hCls (by positivity)
  unfold Wtail
  apply mul_nonneg _ (mul_nonneg (by positivity) hP)
  apply mul_nonneg (by norm_num)
  apply add_nonneg
  · apply mul_nonneg (by norm_num)
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hA)
  · apply mul_nonneg (by positivity)
    apply mul_nonneg _ h5
    apply mul_nonneg _ (by positivity)
    exact mul_nonneg (sq_nonneg _) hA

/-- **The tail terms**: for `R ≥ 1` and `k ≥ 3`,
`3(2 tail(R, 2R) + rem(R, 2R)) · 256/π (2R)² P ≤ W/(1 + R)`. -/
theorem tail_term_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {C6 CGt k Ck P : ℝ}
    (hk : 3 ≤ k) (hCk : 0 ≤ Ck) (hP : 0 ≤ P) {R : ℝ} (hR : 1 ≤ R) (hRT : S.T₁ ≤ R) :
    3 * (2 * S.boundTail Cls k Ck R (2 * R) + S.boundRem Cls C6 CGt R (2 * R)) *
        (256 / Real.pi * (2 * R) ^ 2 * P) ≤
      S.Wtail Cls C6 CGt k Ck P / (1 + R) := by
  have hM := S.M_pos
  have hq := S.q_pos
  have hY := S.Y_pos
  have h2 := c₂_nonneg
  have h5 := c₅_nonneg
  set u := 1 + R with hu
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  set A := S.M ^ (1 + S.η) / S.q with hA
  have hA0 : 0 ≤ A := by positivity
  -- the powers of `u`
  have e3 : u ^ (-(3 : ℝ)) = (u ^ 3)⁻¹ := by
    rw [Real.rpow_neg hu0.le]; norm_cast
  have e5 : u ^ (-(5 : ℝ)) = (u ^ 5)⁻¹ := by
    rw [Real.rpow_neg hu0.le]; norm_cast
  have hT0 : 0 < S.T₁ := S.T₁_pos
  have hk' : u ^ (-k) ≤ (u ^ 3)⁻¹ * S.T₁ ^ (-(k - 3)) := by
    have e : u ^ (-k) = u ^ (-(3 : ℝ)) * u ^ (-(k - 3)) := by
      rw [← Real.rpow_add hu0]; congr 1; ring
    rw [e, e3]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hT0 (by linarith) (by linarith)
  have hRu : (2 * R) ^ 2 + A ≤ (4 + A) * u ^ 2 := by nlinarith
  -- the tail term
  have hT : S.boundTail Cls k Ck R (2 * R) ≤
      S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * S.T₁ ^ (-(k - 3))) ^ 2) *
        (2 * S.M * (Cls S.η * (4 + A))) * (u ^ 4)⁻¹ := by
    unfold boundTail
    have h1 : (Ck * u ^ (-k)) ^ 2 ≤ (Ck * S.T₁ ^ (-(k - 3))) ^ 2 * ((u ^ 3)⁻¹) ^ 2 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (mul_nonneg hCk (by positivity))
      calc Ck * u ^ (-k) ≤ Ck * ((u ^ 3)⁻¹ * S.T₁ ^ (-(k - 3))) :=
            mul_le_mul_of_nonneg_left hk' hCk
        _ = Ck * S.T₁ ^ (-(k - 3)) * (u ^ 3)⁻¹ := by ring
    have h2' : Cls S.η * ((2 * R) ^ 2 + A) ≤ Cls S.η * ((4 + A) * u ^ 2) :=
      mul_le_mul_of_nonneg_left hRu hCls
    calc S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * u ^ (-k)) ^ 2) *
          (2 * S.M * (Cls S.η * ((2 * R) ^ 2 + A)))
        ≤ S.Bk ^ 2 * (7 / 4) * (2 * S.M * ((Ck * S.T₁ ^ (-(k - 3))) ^ 2 * ((u ^ 3)⁻¹) ^ 2)) *
            (2 * S.M * (Cls S.η * ((4 + A) * u ^ 2))) := by
          gcongr
      _ = S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * S.T₁ ^ (-(k - 3))) ^ 2) *
            (2 * S.M * (Cls S.η * (4 + A))) * (u ^ 4)⁻¹ := by
          field_simp
  -- the remainder term
  have hRm : S.boundRem Cls C6 CGt R (2 * R) ≤
      S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (Cls S.η * (4 + A)) *
        (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅) * (u ^ 3)⁻¹ := by
    unfold boundRem
    rw [e5]
    have h2' : Cls S.η * ((2 * R) ^ 2 + A) ≤ Cls S.η * ((4 + A) * u ^ 2) :=
      mul_le_mul_of_nonneg_left hRu hCls
    calc S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (u ^ 5)⁻¹ *
          (Cls S.η * ((2 * R) ^ 2 + A)) *
            (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅)
        ≤ S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (u ^ 5)⁻¹ *
          (Cls S.η * ((4 + A) * u ^ 2)) *
            (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅) := by
          gcongr
      _ = _ := by field_simp
  -- the Heegner side
  have hb : 256 / Real.pi * (2 * R) ^ 2 * P ≤ 1024 / Real.pi * P * u ^ 2 := by
    have : (2 * R) ^ 2 ≤ 4 * u ^ 2 := by nlinarith
    have hπ := Real.pi_pos
    calc 256 / Real.pi * (2 * R) ^ 2 * P ≤ 256 / Real.pi * (4 * u ^ 2) * P := by gcongr
      _ = 1024 / Real.pi * P * u ^ 2 := by ring
  have hb0 : 0 ≤ 256 / Real.pi * (2 * R) ^ 2 * P := mul_nonneg (by positivity) hP
  set Tt := S.Bk ^ 2 * (7 / 4) * (2 * S.M * (Ck * S.T₁ ^ (-(k - 3))) ^ 2) *
    (2 * S.M * (Cls S.η * (4 + A))) with hTt
  set Tr := S.Bk ^ 2 * (1 / (4 * Real.pi ^ 2)) * c₂ * (CGt ^ 2 * (Cls S.η * (4 + A)) *
    (2 * S.M * ((4 * Real.pi * S.M * S.Y) ^ (3 / 2 : ℝ) * C6) ^ 2) * c₅) with hTr
  have hTt0 : 0 ≤ Tt := mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (mul_nonneg hCls (by positivity)))
  have hTr0 : 0 ≤ Tr := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg _ h5
    apply mul_nonneg _ (by positivity)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hCls (by positivity))
  have hu4 : (u ^ 4)⁻¹ ≤ (u ^ 3)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc u ^ 3 = u ^ 3 * 1 := by ring
      _ ≤ u ^ 3 * u := mul_le_mul_of_nonneg_left hu1 (by positivity)
      _ = u ^ 4 := by ring
  have ha : 3 * (2 * S.boundTail Cls k Ck R (2 * R) + S.boundRem Cls C6 CGt R (2 * R)) ≤
      3 * (2 * Tt + Tr) * (u ^ 3)⁻¹ := by
    have h1 : S.boundTail Cls k Ck R (2 * R) ≤ Tt * (u ^ 3)⁻¹ :=
      hT.trans (mul_le_mul_of_nonneg_left hu4 hTt0)
    nlinarith
  have hW : S.Wtail Cls C6 CGt k Ck P = 3 * (2 * Tt + Tr) * (1024 / Real.pi * P) := by
    simp only [Wtail, hTt, hTr, hA]
  rw [hW]
  have hW0 : 0 ≤ 3 * (2 * Tt + Tr) := by positivity
  calc 3 * (2 * S.boundTail Cls k Ck R (2 * R) + S.boundRem Cls C6 CGt R (2 * R)) *
        (256 / Real.pi * (2 * R) ^ 2 * P)
      ≤ 3 * (2 * Tt + Tr) * (u ^ 3)⁻¹ * (1024 / Real.pi * P * u ^ 2) :=
        mul_le_mul ha hb hb0 (mul_nonneg hW0 (by positivity))
    _ = 3 * (2 * Tt + Tr) * (1024 / Real.pi * P) / u := by
        field_simp

theorem sqrt_half_lt_one : Real.sqrt (1 / 2 : ℝ) < 1 :=
  (Real.sqrt_lt' one_pos).2 (by norm_num)

/-- The terms of the series over the blocks `m + 2` are `≤ √W (1/√2)^m`. -/
theorem block_term_le {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {Eexc Cψ Cd C6 CGt k Ck P : ℝ}
    (hk : 3 ≤ k) (hCk : 0 ≤ Ck) (hP : 0 ≤ P) (m : ℕ) :
    Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck (m + 2)) *
        Real.sqrt (256 / Real.pi * blockHi S.T₁ (m + 2) ^ 2 * P) ≤
      Real.sqrt (S.Wtail Cls C6 CGt k Ck P) * Real.sqrt (1 / 2) ^ m := by
  have hT1 := S.one_le_T₁
  have hW0 := S.Wtail_nonneg hCls (C6 := C6) (CGt := CGt) (k := k) (Ck := Ck) hP
  have hRT : S.T₁ ≤ 2 ^ m * S.T₁ := le_mul_of_one_le_left S.T₁_pos.le (one_le_pow₀ (by norm_num))
  have hR : 1 ≤ 2 ^ m * S.T₁ :=
    le_trans (by norm_num) (mul_le_mul (one_le_pow₀ (by norm_num)) hT1 zero_le_one
      (by positivity))
  have e1 : S.blockA Cls Eexc Cψ Cd C6 CGt k Ck (m + 2) =
      3 * (2 * S.boundTail Cls k Ck (2 ^ m * S.T₁) (2 * (2 ^ m * S.T₁)) +
        S.boundRem Cls C6 CGt (2 ^ m * S.T₁) (2 * (2 ^ m * S.T₁))) := by
    simp only [blockA]
    rw [show (2 : ℝ) ^ (m + 1) * S.T₁ = 2 * (2 ^ m * S.T₁) by ring]
  have e2 : blockHi S.T₁ (m + 2) = 2 * (2 ^ m * S.T₁) := by
    simp only [blockHi]; ring
  have hb0 : 0 ≤ 256 / Real.pi * (2 * (2 ^ m * S.T₁)) ^ 2 * P := mul_nonneg (by positivity) hP
  rw [e1, e2, ← Real.sqrt_mul' _ hb0]
  have h2m : (2 : ℝ) ^ m ≤ 1 + 2 ^ m * S.T₁ := by
    have : (2 : ℝ) ^ m ≤ 2 ^ m * S.T₁ := le_mul_of_one_le_right (by positivity) hT1
    linarith
  calc Real.sqrt (3 * (2 * S.boundTail Cls k Ck (2 ^ m * S.T₁) (2 * (2 ^ m * S.T₁)) +
          S.boundRem Cls C6 CGt (2 ^ m * S.T₁) (2 * (2 ^ m * S.T₁))) *
          (256 / Real.pi * (2 * (2 ^ m * S.T₁)) ^ 2 * P))
      ≤ Real.sqrt (S.Wtail Cls C6 CGt k Ck P / (1 + 2 ^ m * S.T₁)) :=
        Real.sqrt_le_sqrt (S.tail_term_le hCls hk hCk hP hR hRT)
    _ ≤ Real.sqrt (S.Wtail Cls C6 CGt k Ck P * (1 / 2) ^ m) := by
        apply Real.sqrt_le_sqrt
        rw [one_div_pow, mul_one_div]
        exact div_le_div_of_nonneg_left hW0 (by positivity) h2m
    _ = Real.sqrt (S.Wtail Cls C6 CGt k Ck P) * Real.sqrt (1 / 2) ^ m := by
        rw [Real.sqrt_mul hW0, sqrt_half_pow]

theorem summable_blocks {Cls : ℝ → ℝ} (hCls : 0 ≤ Cls S.η) {Eexc Cψ Cd C6 CGt k Ck P : ℝ}
    (hk : 3 ≤ k) (hCk : 0 ≤ Ck) (hP : 0 ≤ P) :
    Summable fun n => Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck n) *
      Real.sqrt (256 / Real.pi * blockHi S.T₁ n ^ 2 * P) := by
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun m => S.block_term_le hCls hk hCk hP m)
    ((summable_geometric_of_lt_one (Real.sqrt_nonneg _) sqrt_half_lt_one).mul_left _)

set_option maxHeartbeats 1000000 in
/-- **The spectral side**, explicitly:
`∫ |B(ρ_t, t)| |U| ≤ √A₀ √(256P/π) + √A₁ √(256 T₁² P/π) + √W / (1 - 1/√2)`. -/
theorem spectral_side (hB : BesselAssumptions) {Cls : ℝ → ℝ}
    (hLS : F.LS S.q Cls) {P : ℝ} (hP : 0 ≤ P) (hHS : F.HS P)
    (hBm : Measurable fun x => S.B ψ₀ (F.ρ x) (F.t x)) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck : ℝ} (hk : 3 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k)) :
    Integrable (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖) F.ν ∧
      ∫ x, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖ ∂F.ν ≤
        Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * P) +
        Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)) *
          Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) +
        Real.sqrt (S.Wtail Cls C6 CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹ := by
  have hCls := S.Cls_nonneg F hLS
  have hsum := S.summable_blocks hCls (Eexc := Eexc) (Cψ := Cψ) (Cd := Cd) (C6 := C6)
    (CGt := CGt) (Ck := Ck) hk hCk hP
  obtain ⟨hint, hle⟩ := S.spectral_side_of_summable ψ₀ F hB hLS hHS hBm hE hCψ hψ hCd hMd hC6
    hM6 hGt (by linarith) hCk hMk hsum
  refine ⟨hint, hle.trans ?_⟩
  rw [← hsum.sum_add_tsum_nat_add 2]
  have hgeo := (summable_geometric_of_lt_one (Real.sqrt_nonneg _) sqrt_half_lt_one).mul_left
    (Real.sqrt (S.Wtail Cls C6 CGt k Ck P))
  have htail : ∑' m, Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck (m + 2)) *
      Real.sqrt (256 / Real.pi * blockHi S.T₁ (m + 2) ^ 2 * P) ≤
      Real.sqrt (S.Wtail Cls C6 CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹ := by
    rw [← tsum_geometric_of_lt_one (Real.sqrt_nonneg _) sqrt_half_lt_one, ← tsum_mul_left]
    exact ((summable_nat_add_iff 2).2 hsum).tsum_le_tsum
      (fun m => S.block_term_le hCls hk hCk hP m)
      hgeo
  have e0 : Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck 0) *
      Real.sqrt (256 / Real.pi * blockHi S.T₁ 0 ^ 2 * P) =
      Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * P) := by
    simp [blockA, blockHi]
  have e1 : Real.sqrt (S.blockA Cls Eexc Cψ Cd C6 CGt k Ck 1) *
      Real.sqrt (256 / Real.pi * blockHi S.T₁ 1 ^ 2 * P) =
      Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)) *
        Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) := by
    simp [blockA, blockHi]
  rw [Finset.sum_range_succ, Finset.sum_range_one, e0, e1]
  linarith

end Setup

end Triples
