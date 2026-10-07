import TriplesFinal.Asymptotic.SmoothSum
import TriplesFinal.Asymptotic.CutoffIntegral

/-!
# Lemma 7.2: the main term

`ℳ_d = 32 c_F 𝔏_d 2^(-j) √(x/d) + O(x^(1/4+ε) d^(1/2+ε))`, uniformly for good primes
`d ≤ x^(1/4)` and `x ≥ x₀(a, b, ε)`. The proof uses Lemma 5.3(b),(c) (and hence the
Pólya–Vinogradov inequality).

Proof. Since `ϱ(dk) = 2f(k)` for odd `k` and the sum over `k` is finite,
`ℳ_d = (16/d) ∫ F(T(t)/x) G(y(t)) dt` with `y(t) = 2^(-(v-2)/2) √T(t)` (`IsGood.Md_eq`,
`IsGood.sum_kRange_eq_Gsum`). On the support of `F(T(t)/x)` we have `x/2 ≤ T(t) ≤ x`, so
`y(t) ≍ √x`, and `|G(y) - 𝔏_d| ≪ y^(-1/2+ε) d^(1+ε)` (`abs_Ld_sub_Gsum_le`). Writing
`T(t) = At² + B` with `A = 2^(2j)/(4d)` and `B = m/(4d)`, the substitution `t = √(x/A) s` gives
`∫ F(T(t)/x) dt = √(x/A) J(B/x)` with `|J(B/x) - c_F| ≪ B/x ≪ d/x` (`Cutoff.integral_quadratic`,
`Cutoff.abs_J_sub_cF_le`), and `√(x/A) = 2^(1-j) √(dx)`. This replaces the substitution
`T = T(t)` of the paper. The two errors are `≪ x^(1/4+ε) d^(1/2+ε)` and
`≪ d^(3/2+ε) x^(-1/2) ≤ x^(1/4+ε) d^(1/2+ε)`.

Paper: §7.2, Lemma 7.2.
-/

namespace Triples

open MeasureTheory Filter Topology

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- `T(t) = A t² + B` with `A = 2^(2j)/(4d)` and `B = m/(4d)`. -/
theorem IsGood.Treal_eq_quad {d : ℕ} (hd : P.IsGood d) (t : ℝ) :
    P.Treal d t = (2 : ℝ) ^ (2 * P.j) / (4 * d) * t ^ 2 + (P.m d : ℝ) / (4 * d) := by
  unfold Treal
  have h1 : (2 : ℝ) ^ P.v * P.E = 2 ^ (2 * P.j) := by exact_mod_cast P.two_pow_v_mul_E
  have h2 : (P.m d : ℝ) = 2 ^ P.v * P.H d := by exact_mod_cast hd.m_eq
  have h3 : (2 : ℝ) ^ P.v = 4 * 2 ^ (P.v - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; have := P.hv; omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.prime.ne_zero
  rw [← h1, h2, h3]
  field_simp

theorem continuous_Treal (d : ℕ) : Continuous (P.Treal d) := by
  unfold Treal; fun_prop

theorem IsGood.Treal_pos {d : ℕ} (hd : P.IsGood d) (t : ℝ) : 0 < P.Treal d t := by
  rw [hd.Treal_eq_quad]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hm : (0 : ℝ) < P.m d := by exact_mod_cast P.m_pos hd.d₁_lt
  positivity

/-- `y(t) = 2^(-(v-2)/2) √T(t)`. -/
noncomputable def yy (P : PatternData a b) (d : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (P.Treal d t) / (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2)

theorem continuous_yy (d : ℕ) : Continuous (P.yy d) := by
  unfold yy
  exact ((continuous_Treal d).sqrt).div_const _

theorem IsGood.yy_pos {d : ℕ} (hd : P.IsGood d) (t : ℝ) : 0 < P.yy d t := by
  unfold yy
  have := Real.sqrt_pos.2 (hd.Treal_pos t)
  positivity

theorem Phi_eq (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x : ℝ) (k : ℕ) (t : ℝ) :
    P.Phi F W d x k t = F.F (P.Treal d t / x) * W.W (k / P.yy d t) := by
  unfold Phi yy
  congr 2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) := by positivity
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (P.Treal d t)) with h | h
  · rw [← h]; simp
  · field_simp

/-- The weight `t ↦ F(T(t)/x)` has compact support. -/
theorem IsGood.hasCompactSupport_FT {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx : 0 < x) : HasCompactSupport (fun t => F.F (P.Treal d t / x)) := by
  set A : ℝ := (2 : ℝ) ^ (2 * P.j) / (4 * d) with hA
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hA0 : 0 < A := by positivity
  have hm : (0 : ℝ) < P.m d := by exact_mod_cast P.m_pos hd.d₁_lt
  set R := Real.sqrt (x / A) with hR
  apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
  intro t ht
  apply F.F_eq_zero_of_gt
  rw [one_lt_div hx, hd.Treal_eq_quad, ← hA]
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  have htR : R < |t| := by
    rcases ht with h | h
    · rw [abs_of_neg (by linarith [Real.sqrt_nonneg (x / A)])]; linarith
    · rw [abs_of_pos (by linarith [Real.sqrt_nonneg (x / A)])]; exact h
  have hR2 : R ^ 2 = x / A := Real.sq_sqrt (by positivity)
  have ht2 : x / A < t ^ 2 := by
    rw [← hR2, ← sq_abs t]
    exact pow_lt_pow_left₀ htR (Real.sqrt_nonneg _) (by norm_num)
  have : x < A * t ^ 2 := by
    rw [div_lt_iff₀ hA0] at ht2; linarith
  have : 0 < (P.m d : ℝ) / (4 * d) := by positivity
  linarith

theorem IsGood.continuous_Phi {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    (x : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Continuous (fun t => F.F (P.Treal d t / x) * W.W (k / P.yy d t)) := by
  apply (F.smooth.continuous.comp ((continuous_Treal d).div_const x)).mul
  have hW : ContinuousOn W.W (Set.Ioi 0) := W.smooth.continuousOn
  apply hW.comp_continuous (continuous_const.div (continuous_yy d) (fun t => (hd.yy_pos t).ne'))
  intro t
  have : (0 : ℝ) < k := by exact_mod_cast hk
  exact div_pos this (hd.yy_pos t)

theorem IsGood.integrable_Phi {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun t => F.F (P.Treal d t / x) * W.W (k / P.yy d t)) :=
  (hd.continuous_Phi F W x hk).integrable_of_hasCompactSupport
    ((hd.hasCompactSupport_FT F hx).mul_right)

/-- `ℳ_d = (16/d) ∫ F(T(t)/x) ∑_k χ(k) f(k)/k · W(k/y(t)) dt`. -/
theorem IsGood.Md_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight) {x : ℝ}
    (hx : 0 < x) :
    P.Md F W d x = 16 / d * ∫ t, F.F (P.Treal d t / x) *
      ∑ k ∈ kRange x, P.gR d k / k * W.W (k / P.yy d t) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.prime.ne_zero
  unfold Md
  have hterm : ∀ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) * (rho (P.m d) (d * k) : ℝ) /
      (d * k) * ∫ t, P.Phi F W d x k t =
        2 / d * ∫ t, P.gR d k / k * (F.F (P.Treal d t / x) * W.W (k / P.yy d t)) := by
    intro k hk
    have hodd : k % 2 = 1 := (Finset.mem_filter.1 hk).2
    have hk1 : 1 ≤ k := by omega
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hg : P.gR d k = (ZMod.χ₄ (k : ZMod 4) : ℝ) * ((rho (P.m d) (d * k) : ℝ) / 2) := by
      rw [hd.gR_eq, fd, ite_eq_left hodd]
    rw [integral_const_mul]
    simp_rw [Phi_eq]
    rw [hg]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← integral_finsetSum]
  · rw [← mul_assoc]
    congr 1
    · ring
    · congr 1; ext t
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; ring
  · intro k hk
    have hodd : k % 2 = 1 := (Finset.mem_filter.1 hk).2
    exact (hd.integrable_Phi F W hx (by omega)).const_mul _

/-- On the support of `F(T(t)/x)`, the sum over `kRange x` is `G(y(t))`. -/
theorem IsGood.sum_kRange_eq_Gsum {d : ℕ} (hd : P.IsGood d) (W : HyperbolaWeight) {x y : ℝ}
    (hy0 : 0 < y) (hyx : y ≤ Real.sqrt x) :
    ∑ k ∈ kRange x, P.gR d k / k * W.W (k / y) = P.Gsum W d y := by
  have heven : ∀ k : ℕ, ¬ k % 2 = 1 → P.gR d k = 0 := by
    intro k hk
    rw [hd.gR_eq, fd, ite_eq_right hk, mul_zero]
  rw [kRange, Finset.sum_filter, Gsum]
  have h1 : ∑ k ∈ Finset.range (⌈2 * Real.sqrt x⌉₊ + 1),
      (if k % 2 = 1 then P.gR d k / k * W.W (k / y) else 0) =
      ∑ k ∈ Finset.range (⌈2 * Real.sqrt x⌉₊ + 1), P.gR d k / k * W.W (k / y) := by
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rfl
    · rw [heven k h]; simp
  rw [h1]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    have h2 : ⌊2 * y⌋₊ ≤ ⌈2 * Real.sqrt x⌉₊ :=
      (Nat.floor_le_floor (by linarith)).trans (Nat.floor_le_ceil _)
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [W_div_eq_zero W hy0 (by omega), mul_zero]

/-- On the support of `F(T(t)/x)`: `x/2 ≤ T(t) ≤ x`. -/
theorem Treal_mem_of_F_ne_zero (F : Cutoff) {d : ℕ} {x t : ℝ} (hx : 0 < x)
    (h : F.F (P.Treal d t / x) ≠ 0) : x / 2 ≤ P.Treal d t ∧ P.Treal d t ≤ x := by
  obtain ⟨h1, h2⟩ := F.support _ h
  constructor
  · rw [le_div_iff₀ hx] at h1; linarith
  · rwa [div_le_one hx] at h2

/-- `y₀^(-1/2+ε) √x = (√2 V)^(1/2-ε) x^(1/4+ε/2)` for `y₀ = √(x/2)/V`. -/
theorem sqrt_mul_rpow_y0 {x V ε : ℝ} (hx : 0 < x) (hV : 0 < V) :
    Real.sqrt x * (Real.sqrt (x / 2) / V) ^ (-(1 / 2 : ℝ) + ε) =
      (Real.sqrt 2 * V) ^ (1 / 2 - ε) * x ^ (1 / 4 + ε / 2) := by
  have hs : Real.sqrt (x / 2) = Real.sqrt x / Real.sqrt 2 := Real.sqrt_div' x (by norm_num)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : 0 < Real.sqrt 2 * V := by positivity
  set e : ℝ := -(1 / 2 : ℝ) + ε with he
  have h1 : (Real.sqrt x / (Real.sqrt 2 * V)) ^ e = (Real.sqrt x) ^ e / (Real.sqrt 2 * V) ^ e :=
    Real.div_rpow hsx.le hs2.le e
  have h2 : (Real.sqrt x) ^ e = x ^ (e / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; ring_nf
  have h3 : (Real.sqrt 2 * V) ^ e = ((Real.sqrt 2 * V) ^ (1 / 2 - ε))⁻¹ := by
    rw [show e = -(1 / 2 - ε) by rw [he]; ring, Real.rpow_neg hs2.le]
  have h4 : Real.sqrt x * x ^ (e / 2) = x ^ (1 / 4 + ε / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; congr 1; rw [he]; ring
  rw [hs, div_div, h1, h2, h3, div_inv_eq_mul, ← mul_assoc, h4, mul_comm]

set_option maxHeartbeats 1000000 in
variable (P) in
/-- **Lemma 7.2.** -/
theorem main_term (hPV : PolyaVinogradov) (F : Cutoff) (W : HyperbolaWeight) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Md F W d x - 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d)| ≤
        C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨CR, hCR0, hCR⟩ := P.abs_Ld_sub_Gsum_le hPV W hε (by linarith)
  obtain ⟨CL, hCL⟩ := P.Ld_bound hPV hε
  obtain ⟨LF, hLF0, hLF⟩ := F.exists_lipschitz
  set V : ℝ := (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) with hV
  have hV1 : 1 ≤ V := Real.one_le_rpow (by norm_num) (by
    have : (2 : ℝ) ≤ P.v := by exact_mod_cast P.hv
    linarith)
  have hV0 : 0 < V := by linarith
  have hV2 : V ^ 2 = (2 : ℝ) ^ ((P.v : ℝ) - 2) := by
    rw [hV, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  set K2 : ℝ := (Real.sqrt 2 * V) ^ (1 / 2 - ε) with hK2
  have hK20 : 0 ≤ K2 := by positivity
  refine ⟨32 * |CL| * LF + 64 * CR * K2, (2 : ℝ) ^ (P.v : ℝ), fun x hx d hd hdx => ?_⟩
  -- basic facts
  have hv2 : (4 : ℝ) ≤ (2 : ℝ) ^ (P.v : ℝ) := by
    calc (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
      _ ≤ 2 ^ (P.v : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by exact_mod_cast P.hv)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  have hm0 : (0 : ℝ) < P.m d := by exact_mod_cast P.m_pos hd.d₁_lt
  have hm2 : (P.m d : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
    have := (P.m_bounds hd.d₁_lt).2; exact_mod_cast this
  set A : ℝ := (2 : ℝ) ^ (2 * P.j) / (4 * d) with hA
  set Bq : ℝ := (P.m d : ℝ) / (4 * d) with hBq
  have hA0 : 0 < A := by positivity
  have hBq0 : 0 ≤ Bq := by positivity
  have hBqd : Bq ≤ d / 2 := by
    rw [hBq, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  -- `√(x/A) = 2 √(dx) / 2^j`
  set S : ℝ := Real.sqrt (x / A) with hS
  have hS_eq : S = 2 * Real.sqrt (d * x) / 2 ^ P.j := by
    rw [hS, hA]
    have h2j : (0 : ℝ) < 2 ^ P.j := by positivity
    rw [show x / ((2 : ℝ) ^ (2 * P.j) / (4 * d)) = (2 * Real.sqrt (d * x) / 2 ^ P.j) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm P.j 2]
      field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSle : S ≤ 2 * Real.sqrt (d * x) := by
    rw [hS_eq]
    exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  -- the integral of the weight
  set I : ℝ := ∫ t, F.F (P.Treal d t / x) with hI
  have hT : ∀ t, P.Treal d t = A * t ^ 2 + Bq := fun t => hd.Treal_eq_quad t
  have hI_eq : I = S * F.J (Bq / x) := by
    rw [hI]
    simp_rw [hT]
    exact F.integral_quadratic hA0 hBq0 hx0
  have hI_le : I ≤ 2 * S := by
    rw [hI_eq]; nlinarith [F.J_le_two (Bq / x)]
  have hI_cF : |I - S * F.cF| ≤ S * (2 * LF * (Bq / x)) := by
    rw [hI_eq, ← mul_sub, abs_mul, abs_of_nonneg hS0]
    exact mul_le_mul_of_nonneg_left (F.abs_J_sub_cF_le hLF (by positivity)) hS0
  -- `y(t)` on the support
  set y₀ : ℝ := Real.sqrt (x / 2) / V with hy₀
  have hy₀1 : 1 ≤ y₀ := by
    rw [hy₀, le_div_iff₀ hV0, one_mul, Real.le_sqrt hV0.le (by positivity), hV2]
    have : (2 : ℝ) ^ ((P.v : ℝ) - 2) * 2 ≤ x := by
      have h22 : (2 : ℝ) ^ ((P.v : ℝ) - 2) * 2 ^ (2 : ℝ) = 2 ^ (P.v : ℝ) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf
      have : (2 : ℝ) ^ ((P.v : ℝ) - 2) * 2 ≤ (2 : ℝ) ^ ((P.v : ℝ) - 2) * 2 ^ (2 : ℝ) := by
        gcongr; norm_num
      linarith
    linarith
  set Rmax : ℝ := CR * y₀ ^ (-(1 / 2 : ℝ) + ε) * (d : ℝ) ^ (1 + ε) with hRmax
  have hRmax0 : 0 ≤ Rmax := by positivity
  set Gt : ℝ → ℝ := fun t => ∑ k ∈ kRange x, P.gR d k / k * W.W (k / P.yy d t) with hGt
  have hpt : ∀ t, ‖F.F (P.Treal d t / x) * (Gt t - P.Ld d)‖ ≤ Rmax * F.F (P.Treal d t / x) := by
    intro t
    by_cases hF : F.F (P.Treal d t / x) = 0
    · rw [hF]; simp
    obtain ⟨hT1, hT2⟩ := Treal_mem_of_F_ne_zero F hx0 hF
    have hy : P.yy d t ≤ Real.sqrt x := by
      unfold yy
      rw [div_le_iff₀ hV0]
      calc Real.sqrt (P.Treal d t) ≤ Real.sqrt x := Real.sqrt_le_sqrt hT2
        _ ≤ Real.sqrt x * V := le_mul_of_one_le_right (Real.sqrt_nonneg _) hV1
    have hy0 : y₀ ≤ P.yy d t := by
      unfold yy
      rw [hy₀]
      exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hT1) hV0.le
    have hG : Gt t = P.Gsum W d (P.yy d t) :=
      hd.sum_kRange_eq_Gsum W (hd.yy_pos t) hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (F.nonneg _), hG, abs_sub_comm, mul_comm Rmax]
    apply mul_le_mul_of_nonneg_left _ (F.nonneg _)
    have hpow : (P.yy d t) ^ (-(1 / 2 : ℝ) + ε) ≤ y₀ ^ (-(1 / 2 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hy0 (by linarith)
    calc |P.Ld d - P.Gsum W d (P.yy d t)|
        ≤ CR * (P.yy d t) ^ (-(1 / 2 : ℝ) + ε) * (d : ℝ) ^ (1 + ε) :=
          hCR d hd _ (hy₀1.trans hy0)
      _ ≤ Rmax := by
          rw [hRmax]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCR0) (by positivity)
  -- integrability
  have hFint : Integrable (fun t => F.F (P.Treal d t / x)) :=
    (F.smooth.continuous.comp ((continuous_Treal d).div_const x)).integrable_of_hasCompactSupport
      (hd.hasCompactSupport_FT F hx0)
  have hFGint : Integrable (fun t => F.F (P.Treal d t / x) * Gt t) := by
    have : (fun t => F.F (P.Treal d t / x) * Gt t) =
        fun t => ∑ k ∈ kRange x, P.gR d k / k * (F.F (P.Treal d t / x) * W.W (k / P.yy d t)) := by
      ext t; rw [hGt, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [this]
    apply integrable_finsetSum
    intro k hk
    have hodd : k % 2 = 1 := (Finset.mem_filter.1 hk).2
    exact (hd.integrable_Phi F W hx0 (by omega)).const_mul _
  have hdiff_int : Integrable (fun t => F.F (P.Treal d t / x) * (Gt t - P.Ld d)) := by
    have : (fun t => F.F (P.Treal d t / x) * (Gt t - P.Ld d)) =
        fun t => F.F (P.Treal d t / x) * Gt t - P.Ld d * F.F (P.Treal d t / x) := by
      ext t; ring
    rw [this]
    exact hFGint.sub (hFint.const_mul _)
  -- the decomposition
  have hMd0 : P.Md F W d x = 16 / d * ∫ t, F.F (P.Treal d t / x) * Gt t := hd.Md_eq F W hx0
  have hsum := integral_add hdiff_int (hFint.const_mul (P.Ld d))
  have hMd : P.Md F W d x = 16 / d * (∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)) +
      16 / d * P.Ld d * I := by
    rw [hMd0]
    have : ∫ t, F.F (P.Treal d t / x) * Gt t =
        ∫ t, (F.F (P.Treal d t / x) * (Gt t - P.Ld d) + P.Ld d * F.F (P.Treal d t / x)) := by
      congr 1; ext t; ring
    rw [this, hsum, integral_const_mul, ← hI]
    ring
  have hmain : 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d) =
      16 / d * P.Ld d * (S * F.cF) := by
    rw [hS_eq]
    have e1 : Real.sqrt (d * x) = Real.sqrt d * Real.sqrt x := Real.sqrt_mul hd0.le x
    have e2 : Real.sqrt (x / d) = Real.sqrt x / Real.sqrt d := Real.sqrt_div' x hd0.le
    have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
    have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0.le
    rw [e1, e2]
    field_simp
    rw [Real.sq_sqrt hd0.le]
    ring
  have hint_bound : |∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)| ≤ Rmax * I := by
    rw [hI, ← integral_const_mul, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hFint.const_mul _) (Filter.Eventually.of_forall hpt)
  -- the final estimate
  rw [hMd, hmain]
  have hsplit : 16 / ↑d * (∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)) + 16 / ↑d * P.Ld d * I -
      16 / ↑d * P.Ld d * (S * F.cF) =
      16 / d * (∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)) +
        16 / d * P.Ld d * (I - S * F.cF) := by ring
  rw [hsplit]
  -- auxiliary identities
  have hdpow : (d : ℝ) ^ (1 + ε) = d * (d : ℝ) ^ ε := by
    rw [Real.rpow_add hd0, Real.rpow_one]
  have hdhalf : (d : ℝ) ^ (1 / 2 + ε) = Real.sqrt d * (d : ℝ) ^ ε := by
    rw [Real.rpow_add hd0, Real.sqrt_eq_rpow]
  have hsdx : Real.sqrt (d * x) = Real.sqrt d * Real.sqrt x := Real.sqrt_mul hd0.le x
  have hy0e : Real.sqrt x * y₀ ^ (-(1 / 2 : ℝ) + ε) = K2 * x ^ (1 / 4 + ε / 2) := by
    rw [hy₀, hK2]; exact sqrt_mul_rpow_y0 hx0 hV0
  have hxe : x ^ (1 / 4 + ε / 2) ≤ x ^ (1 / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hde0 : 0 ≤ (d : ℝ) ^ ε := by positivity
  have hsd0 : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  -- the error from `G(y(t)) - 𝔏_d`
  have hT2 : |16 / (d : ℝ) * ∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)| ≤
      64 * CR * K2 * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 / d)]
    calc 16 / (d : ℝ) * |∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)|
        ≤ 16 / d * (Rmax * (2 * (2 * Real.sqrt (d * x)))) := by
          gcongr
          calc |∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)| ≤ Rmax * I := hint_bound
            _ ≤ Rmax * (2 * S) := by gcongr
            _ ≤ Rmax * (2 * (2 * Real.sqrt (d * x))) := by gcongr
      _ = 64 * CR * (Real.sqrt d * (d : ℝ) ^ ε) * (Real.sqrt x * y₀ ^ (-(1 / 2 : ℝ) + ε)) := by
          rw [hRmax, hdpow, hsdx]
          field_simp
          ring
      _ = 64 * CR * K2 * (x ^ (1 / 4 + ε / 2) * (d : ℝ) ^ (1 / 2 + ε)) := by
          rw [hy0e, hdhalf]; ring
      _ ≤ 64 * CR * K2 * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by gcongr
  -- the error from replacing `J(B/x)` by `c_F`
  have hT1 : |16 / (d : ℝ) * P.Ld d * (I - S * F.cF)| ≤
      32 * |CL| * LF * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by
    have hLd : |P.Ld d| ≤ |CL| * (d : ℝ) ^ (1 + ε) :=
      (hCL d hd).trans (mul_le_mul_of_nonneg_right (le_abs_self CL) (by positivity))
    have hdx : (d : ℝ) ≤ Real.sqrt x := by
      calc (d : ℝ) ≤ x ^ (1 / 4 : ℝ) := hdx
        _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    have hx14 : (1 : ℝ) ≤ x ^ (1 / 4 + ε) := Real.one_le_rpow hx1 (by positivity)
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 / d)]
    calc 16 / (d : ℝ) * |P.Ld d| * |I - S * F.cF|
        ≤ 16 / d * (|CL| * (d : ℝ) ^ (1 + ε)) * (2 * Real.sqrt (d * x) * (2 * LF * ((d / 2) / x))) := by
          gcongr
          calc |I - S * F.cF| ≤ S * (2 * LF * (Bq / x)) := hI_cF
            _ ≤ 2 * Real.sqrt (d * x) * (2 * LF * ((d / 2) / x)) := by gcongr
      _ = 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε) * (d / Real.sqrt x) := by
          rw [hdpow, hsdx]
          field_simp
          rw [Real.sq_sqrt hx0.le]
          ring
      _ ≤ 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε) * 1 := by
          gcongr
          rw [div_le_one hsx0]; exact hdx
      _ ≤ 32 * |CL| * LF * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by
          rw [hdhalf, mul_one]
          have h0 : 0 ≤ 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε) := by positivity
          calc 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε)
              = 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε) * 1 := (mul_one _).symm
            _ ≤ 32 * |CL| * LF * (Real.sqrt d * (d : ℝ) ^ ε) * x ^ (1 / 4 + ε) :=
                mul_le_mul_of_nonneg_left hx14 h0
            _ = 32 * |CL| * LF * (x ^ (1 / 4 + ε) * (Real.sqrt d * (d : ℝ) ^ ε)) := by ring
  calc _ ≤ |16 / (d : ℝ) * ∫ t, F.F (P.Treal d t / x) * (Gt t - P.Ld d)| +
        |16 / (d : ℝ) * P.Ld d * (I - S * F.cF)| := abs_add_le _ _
    _ ≤ 64 * CR * K2 * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) +
        32 * |CL| * LF * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := add_le_add hT2 hT1
    _ = (32 * |CL| * LF + 64 * CR * K2) * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε)) := by ring

end PatternData

end Triples
