import TriplesFinal.Asymptotic.Setup

/-!
# Lemma 7.2: smoothed partial sums of the singular series

For `y > 0` let `G(y) = ∑_{k ≤ 2y} χ(k) f(k)/k · W(k/y)` (`Gsum`). Then for `0 < ε ≤ 1/4`,
`|𝔏_d - G(y)| ≪_ε y^(-1/2+ε) d^(1+ε)` for `y ≥ 1`, uniformly in good primes `d`
(`abs_Ld_sub_Gsum_le`).

Proof: `𝔏_d - G(y) = ∑_k χf(k) w(k)` with `w(k) = (1 - W(k/y))/k`, and by summation by parts
this is `∑_k A_f(k) (w(k) - w(k+1))`. The increments vanish for `k + 1 ≤ y/2`, are at most
`1/k² + L/(yk)` (`L` a Lipschitz constant of `W`, `HyperbolaWeight.exists_lipschitz`), and equal
`1/k - 1/(k+1)` for `k ≥ 2y`; Lemma 5.3(b) bounds `A_f(k)`.

Paper: §7.2, proof of Lemma 7.2 (the estimate for `𝔏_d - G(y)`).
-/

namespace Triples

open Filter Topology

/-- The weight `W` is Lipschitz on `(0, ∞)`. -/
theorem HyperbolaWeight.exists_lipschitz (W : HyperbolaWeight) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : ℝ, 0 < a → 0 < b → |W.W a - W.W b| ≤ L * |a - b| := by
  have hopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hcont : ContinuousOn (deriv W.W) (Set.Ioi 0) :=
    W.smooth.continuousOn_deriv_of_isOpen hopen (by simp)
  have hK : IsCompact (Set.Icc (1 / 4 : ℝ) 4) := isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hcont.mono (fun t ht => lt_of_lt_of_le (by norm_num) ht.1))
  have hdiff : ∀ t ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ W.W t := fun t ht =>
    ((W.smooth.differentiableOn (by simp)) t ht).differentiableAt (hopen.mem_nhds ht)
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ), ‖deriv W.W t‖ ≤ max C 0 := by
    intro t ht
    by_cases h1 : t < 1 / 4
    · -- `W = 1` near `t`
      have heq : W.W =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Ioo_mem_nhds (ht : (0 : ℝ) < t) (by linarith : t < 1 / 2)] with s hs
        exact W.eq_one s hs.1 hs.2.le
      rw [heq.deriv_eq, deriv_const]; simp
    by_cases h2 : 4 < t
    · have heq : W.W =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds (by linarith : (2 : ℝ) < t)] with s hs
        exact W.eq_zero s (le_of_lt hs)
      rw [heq.deriv_eq, deriv_const]; simp
    push Not at h1 h2
    exact (hC t ⟨h1, h2⟩).trans (le_max_left _ _)
  refine ⟨max C 0, le_max_right _ _, fun a b ha hb => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioi 0) hb ha
  simpa [Real.norm_eq_abs] using this

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- The smoothed partial sums `G(y) = ∑_{k ≤ 2y} χ(k) f(k)/k · W(k/y)`. -/
noncomputable def Gsum (P : PatternData a b) (W : HyperbolaWeight) (d : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (⌊2 * y⌋₊ + 1), P.gR d k / k * W.W (k / y)

/-- The weight `w(k) = (1 - W(k/y))/k` (and `w(0) = 0`). -/
noncomputable def wgt (W : HyperbolaWeight) (y : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (1 - W.W (k / y)) / k

theorem W_div_eq_zero (W : HyperbolaWeight) {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : ⌊2 * y⌋₊ < k) :
    W.W (k / y) = 0 := by
  apply W.eq_zero
  rw [le_div_iff₀ hy]
  have h1 := Nat.lt_floor_add_one (2 * y)
  have h2 : ((⌊2 * y⌋₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hk
  linarith

/-- `∑_{k ≤ N} χf(k) w(k) = ∑_{k ≤ N} χf(k)/k - G(y)` for `N ≥ 2y`. -/
theorem IsGood.sum_gR_wgt {d : ℕ} (hd : P.IsGood d) (W : HyperbolaWeight) {y : ℝ} (hy : 0 < y)
    {N : ℕ} (hN : ⌊2 * y⌋₊ ≤ N) :
    ∑ k ∈ Finset.range (N + 1), P.gR d k * wgt W y k = P.LdPartial d (N + 1) - P.Gsum W d y := by
  rw [hd.LdPartial_eq, Gsum]
  have hsplit : ∀ k ∈ Finset.range (N + 1), P.gR d k * wgt W y k =
      P.gR d k / k - P.gR d k / k * W.W (k / y) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [wgt, gR_zero]
    · rw [wgt, ite_eq_right (by omega)]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  congr 1
  symm
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [W_div_eq_zero W hy (by omega), mul_zero]

/-- The increments of `w`: `|w(k) - w(k+1)| ≤ 1/k² + L/(yk)`, they vanish for `k + 1 ≤ y/2`, and
`w(k) - w(k+1) = 1/k - 1/(k+1)` for `k ≥ 2y`. -/
theorem abs_wgt_sub_le (W : HyperbolaWeight) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a b : ℝ, 0 < a → 0 < b → |W.W a - W.W b| ≤ L * |a - b|) {y : ℝ} (hy : 0 < y)
    {k : ℕ} (hk : 1 ≤ k) :
    |wgt W y k - wgt W y (k + 1)| ≤ 1 / (k : ℝ) ^ 2 + L / (y * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [wgt, wgt, ite_eq_right (by omega), ite_eq_right (by omega)]
  push_cast
  have hW1 : 0 ≤ 1 - W.W (k / y) := by linarith [W.le_one (k / y) (by positivity)]
  have hW1' : 1 - W.W (k / y) ≤ 1 := by linarith [W.nonneg (k / y) (by positivity)]
  have hLip := hL ((k + 1) / y) (k / y) (by positivity) (by positivity)
  have hdiff : |((k : ℝ) + 1) / y - k / y| = 1 / y := by
    rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
  rw [hdiff] at hLip
  have heq : (1 - W.W (k / y)) / k - (1 - W.W ((k + 1) / y)) / (k + 1) =
      (1 - W.W (k / y)) * (1 / k - 1 / (k + 1)) +
        (W.W ((k + 1) / y) - W.W (k / y)) / (k + 1) := by
    field_simp; ring
  rw [heq]
  have h1 : |(1 - W.W (k / y)) * (1 / (k : ℝ) - 1 / (k + 1))| ≤ 1 / (k : ℝ) ^ 2 := by
    have hpos : 0 ≤ 1 / (k : ℝ) - 1 / (k + 1) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hk0 (by linarith)
    rw [abs_mul, abs_of_nonneg hW1, abs_of_nonneg hpos]
    have : 1 / (k : ℝ) - 1 / (k + 1) ≤ 1 / (k : ℝ) ^ 2 := by
      rw [div_sub_div _ _ hk0.ne' hk1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (1 - W.W (k / y)) * (1 / (k : ℝ) - 1 / (k + 1)) ≤ 1 * (1 / (k : ℝ) - 1 / (k + 1)) :=
          mul_le_mul_of_nonneg_right hW1' hpos
      _ ≤ 1 / (k : ℝ) ^ 2 := by linarith
  have h2 : |(W.W ((k + 1) / y) - W.W (k / y)) / ((k : ℝ) + 1)| ≤ L / (y * k) := by
    rw [abs_div, abs_of_pos hk1, div_le_div_iff₀ hk1 (by positivity)]
    have : L * (1 / y) * (y * k) = L * k := by field_simp
    calc |W.W ((k + 1) / y) - W.W (k / y)| * (y * k) ≤ L * (1 / y) * (y * k) :=
          mul_le_mul_of_nonneg_right hLip (by positivity)
      _ = L * k := this
      _ ≤ L * (k + 1) := by nlinarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem wgt_eq_zero (W : HyperbolaWeight) {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k)
    (hky : ((k : ℝ)) / y ≤ 1 / 2) : wgt W y k = 0 := by
  rw [wgt, ite_eq_right (by omega), W.eq_one _ (by positivity) hky]; simp

theorem wgt_of_large (W : HyperbolaWeight) {y : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hky : 2 ≤ (k : ℝ) / y) : wgt W y k = 1 / k := by
  rw [wgt, ite_eq_right (by omega), W.eq_zero _ hky]; simp

theorem abs_wgt_le (W : HyperbolaWeight) (y : ℝ) (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) :
    |wgt W y k| ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [wgt, ite_eq_right (by omega), abs_div, abs_of_pos hk0]
  have h1 := W.le_one (k / y) (by positivity)
  have h2 := W.nonneg (k / y) (by positivity)
  rw [abs_of_nonneg (by linarith)]
  gcongr
  linarith

/-- The termwise bound in the summation by parts for `𝔏_d - G(y)`. -/
theorem abs_psum_mul_wgt_sub_le {g : ℕ → ℝ} {K θ ε' : ℝ} (hK : 0 ≤ K) (hθ1 : θ - 1 + ε' ≤ 0)
    (hθ : θ < 1) (hA : ∀ k : ℕ, 1 ≤ k → |psum g k| ≤ K * (k : ℝ) ^ θ)
    (W : HyperbolaWeight) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a b : ℝ, 0 < a → 0 < b → |W.W a - W.W b| ≤ L * |a - b|) {y : ℝ} (hy : 1 ≤ y)
    {k : ℕ} (hk : 1 ≤ k) :
    |psum g k * (wgt W y k - wgt W y (k + 1))| ≤
      K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') +
        (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0)) := by
  have hy0 : 0 < y := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hy4 : 0 < y / 4 := by positivity
  have hite : 0 ≤ (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0) := by
    split_ifs <;> positivity
  have hRHS0 : 0 ≤ K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') +
      (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0)) := by positivity
  by_cases hsmall : (k : ℝ) < y / 4
  · -- `w(k) = w(k+1) = 0`
    have hy4' : 1 < y / 4 := lt_of_le_of_lt hk1 hsmall
    have h1 : wgt W y k = 0 := wgt_eq_zero W hy0 hk (by
      rw [div_le_iff₀ hy0]; nlinarith)
    have h2 : wgt W y (k + 1) = 0 := wgt_eq_zero W hy0 (by omega) (by
      rw [div_le_iff₀ hy0]; push_cast; nlinarith)
    rw [h1, h2, sub_self, mul_zero, abs_zero]
    exact hRHS0
  push Not at hsmall
  -- `k^(θ-2) ≤ (y/4)^(θ-1+ε') k^(-1-ε')`
  have hα : (k : ℝ) ^ (θ - 2) ≤ (y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') := by
    have : (k : ℝ) ^ (θ - 2) = (k : ℝ) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') := by
      rw [← Real.rpow_add hk0]; ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hy4 hsmall hθ1)
      (Real.rpow_nonneg hk0.le _)
  have hβ : (k : ℝ) ^ (θ - 1) ≤ (y / 4) ^ (θ - 1) :=
    Real.rpow_le_rpow_of_nonpos hy4 hsmall (by linarith)
  have hAk := hA k hk
  have hpow2 : (k : ℝ) ^ θ * (1 / (k : ℝ) ^ 2) = (k : ℝ) ^ (θ - 2) := by
    rw [Real.rpow_sub hk0, Real.rpow_two]; field_simp
  have hpow1 : (k : ℝ) ^ θ * (1 / (k : ℝ)) = (k : ℝ) ^ (θ - 1) := by
    rw [Real.rpow_sub_one hk0.ne']; field_simp
  by_cases hlarge : 2 * y ≤ (k : ℝ)
  · -- `w(k) - w(k+1) = 1/k - 1/(k+1) ≤ 1/k²`
    have h1 : wgt W y k = 1 / k := wgt_of_large W hk (by rw [le_div_iff₀ hy0]; linarith)
    have h2 : wgt W y (k + 1) = 1 / ((k + 1 : ℕ) : ℝ) :=
      wgt_of_large W (by omega) (by rw [le_div_iff₀ hy0]; push_cast; linarith)
    rw [h1, h2]
    push_cast
    have hd0 : 0 ≤ 1 / (k : ℝ) - 1 / (k + 1) := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hk0 (by linarith)
    have hd1 : 1 / (k : ℝ) - 1 / (k + 1) ≤ 1 / (k : ℝ) ^ 2 := by
      rw [div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_mul, abs_of_nonneg hd0]
    calc |psum g k| * (1 / (k : ℝ) - 1 / (k + 1)) ≤ (K * (k : ℝ) ^ θ) * (1 / (k : ℝ) ^ 2) :=
          mul_le_mul hAk hd1 hd0 (by positivity)
      _ = K * (k : ℝ) ^ (θ - 2) := by rw [mul_assoc, hpow2]
      _ ≤ K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε')) := by gcongr
      _ ≤ _ := by gcongr; linarith
  · push Not at hlarge
    have hw := abs_wgt_sub_le W hL0 hL hy0 hk
    rw [abs_mul, ite_eq_left hlarge.le]
    calc |psum g k| * |wgt W y k - wgt W y (k + 1)|
        ≤ (K * (k : ℝ) ^ θ) * (1 / (k : ℝ) ^ 2 + L / (y * k)) :=
          mul_le_mul hAk hw (abs_nonneg _) (by positivity)
      _ = K * ((k : ℝ) ^ (θ - 2) + L / y * (k : ℝ) ^ (θ - 1)) := by
          rw [← hpow2, ← hpow1]; field_simp
      _ ≤ K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') + L / y * (y / 4) ^ (θ - 1)) := by
          gcongr

variable (P) in
/-- **Smoothed partial sums** (proof of Lemma 7.2): for `0 < ε ≤ 1/4`,
`|𝔏_d - G(y)| ≪_ε y^(-1/2+ε) d^(1+ε)` for `y ≥ 1`, uniformly in good primes `d`. -/
theorem abs_Ld_sub_Gsum_le (hPV : PolyaVinogradov) (W : HyperbolaWeight) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, P.IsGood d → ∀ y : ℝ, 1 ≤ y →
      |P.Ld d - P.Gsum W d y| ≤ C * y ^ (-(1 / 2 : ℝ) + ε) * (d : ℝ) ^ (1 + ε) := by
  set ε' := ε / 2 with hε'def
  have hε' : 0 < ε' := by positivity
  obtain ⟨Cg, hCg0, hCg⟩ := P.abs_psum_gR_le hPV hε'
  obtain ⟨L, hL0, hL⟩ := W.exists_lipschitz
  set θ : ℝ := 1 / 2 + ε' with hθdef
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθε : θ - 1 + ε' ≤ 0 := by rw [hθdef]; linarith
  have hZs : Summable (fun k : ℕ => (k : ℝ) ^ (-1 - ε')) :=
    Real.summable_nat_rpow.2 (by linarith)
  set Z := ∑' k : ℕ, (k : ℝ) ^ (-1 - ε') with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  refine ⟨Cg * (2 * Z + 6 * L), by positivity, fun d hd y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set K := Cg * (d : ℝ) ^ (1 + ε') with hK
  have hK0 : 0 ≤ K := by positivity
  have hA : ∀ k : ℕ, 1 ≤ k → |psum (P.gR d) k| ≤ K * (k : ℝ) ^ θ := fun k hk => hCg d hd k hk
  -- the bound for the sum of the increments
  set B := K * ((y / 4) ^ (θ - 1 + ε') * Z + ((⌊2 * y⌋₊ : ℝ) + 1) * (L / y * (y / 4) ^ (θ - 1)))
    with hB
  have hsumB : ∀ N : ℕ, |∑ k ∈ Finset.range N,
      psum (P.gR d) k * (wgt W y k - wgt W y (k + 1))| ≤ B := by
    intro N
    have hterm : ∀ k ∈ Finset.range N, |psum (P.gR d) k * (wgt W y k - wgt W y (k + 1))| ≤
        K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') +
          (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0)) := by
      intro k _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [psum_zero (P.gR d) (gR_zero d), zero_mul, abs_zero]
        have : 0 ≤ (if ((0 : ℕ) : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0) := by
          split_ifs <;> positivity
        positivity
      exact abs_psum_mul_wgt_sub_le hK0 hθε hθ1 hA W hL0 hL hy hk
    calc |∑ k ∈ Finset.range N, psum (P.gR d) k * (wgt W y k - wgt W y (k + 1))|
        ≤ ∑ k ∈ Finset.range N, |psum (P.gR d) k * (wgt W y k - wgt W y (k + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, K * ((y / 4) ^ (θ - 1 + ε') * (k : ℝ) ^ (-1 - ε') +
          (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0)) :=
          Finset.sum_le_sum hterm
      _ = K * ((y / 4) ^ (θ - 1 + ε') * ∑ k ∈ Finset.range N, (k : ℝ) ^ (-1 - ε') +
          ∑ k ∈ Finset.range N, (if (k : ℝ) ≤ 2 * y then L / y * (y / 4) ^ (θ - 1) else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ B := by
          rw [hB]
          gcongr
          · exact hZs.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
          · rw [← Finset.sum_filter]
            have hc0 : 0 ≤ L / y * (y / 4) ^ (θ - 1) := by positivity
            calc ∑ k ∈ (Finset.range N).filter (fun k : ℕ => (k : ℝ) ≤ 2 * y),
                  L / y * (y / 4) ^ (θ - 1)
                = (((Finset.range N).filter (fun k : ℕ => (k : ℝ) ≤ 2 * y)).card : ℝ) *
                    (L / y * (y / 4) ^ (θ - 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ((Finset.range (⌊2 * y⌋₊ + 1)).card : ℝ) * (L / y * (y / 4) ^ (θ - 1)) := by
                  gcongr
                  intro k hk
                  rw [Finset.mem_filter] at hk
                  rw [Finset.mem_range]
                  exact Nat.lt_succ_of_le (Nat.le_floor hk.2)
              _ = ((⌊2 * y⌋₊ : ℝ) + 1) * (L / y * (y / 4) ^ (θ - 1)) := by
                  rw [Finset.card_range]; push_cast; ring
  -- pass to the limit
  have hlim : Tendsto (fun N : ℕ => P.LdPartial d (N + 1) - P.Gsum W d y) atTop
      (𝓝 (P.Ld d - P.Gsum W d y)) :=
    (((P.Ld_tendsto hPV hd).comp (tendsto_add_atTop_nat 1))).sub_const _
  have hbound : ∀ᶠ N : ℕ in atTop,
      |P.LdPartial d (N + 1) - P.Gsum W d y| ≤ K * (N : ℝ) ^ (θ - 1) + B := by
    filter_upwards [eventually_ge_atTop (⌊2 * y⌋₊ + 1)] with N hN
    have hN1 : 1 ≤ N := by omega
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [← hd.sum_gR_wgt W hy0 (by omega : ⌊2 * y⌋₊ ≤ N),
      sum_range_mul_eq_abel (P.gR d) (wgt W y) (gR_zero d) N]
    have h1 : |psum (P.gR d) N * wgt W y N| ≤ K * (N : ℝ) ^ (θ - 1) := by
      rw [abs_mul]
      calc |psum (P.gR d) N| * |wgt W y N| ≤ (K * (N : ℝ) ^ θ) * (1 / N) :=
            mul_le_mul (hA N hN1) (abs_wgt_le W y hy0 hN1) (abs_nonneg _) (by positivity)
        _ = K * (N : ℝ) ^ (θ - 1) := by
            rw [Real.rpow_sub_one hN0.ne']; field_simp
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 (hsumB N)
  have hlim2 : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (θ - 1) + B) atTop (𝓝 (K * 0 + B)) := by
    apply Tendsto.add_const
    apply Tendsto.const_mul
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp tendsto_natCast_atTop_atTop
    refine this.congr (fun N => ?_)
    simp only [Function.comp_apply, neg_sub]
  have hfinal : |P.Ld d - P.Gsum W d y| ≤ B := by
    have := le_of_tendsto_of_tendsto (hlim.abs) hlim2 hbound
    simpa using this
  -- estimate `B`
  have hy4 : (0 : ℝ) < y / 4 := by positivity
  have hpowA : (y / 4) ^ (θ - 1 + ε') ≤ 2 * y ^ (-(1 / 2 : ℝ) + ε) := by
    have hexp : θ - 1 + ε' = -(1 / 2 : ℝ) + ε := by rw [hθdef, hε'def]; ring
    rw [hexp, Real.div_rpow hy0.le (by norm_num)]
    have h4 : (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ) + ε) := by
      calc (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
              ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ) + ε) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ y ^ (-(1 / 2 : ℝ) + ε) := Real.rpow_nonneg hy0.le _
    nlinarith
  have hpowB : ((⌊2 * y⌋₊ : ℝ) + 1) * (L / y * (y / 4) ^ (θ - 1)) ≤
      6 * L * y ^ (-(1 / 2 : ℝ) + ε) := by
    have hfl : ((⌊2 * y⌋₊ : ℝ) + 1) ≤ 3 * y := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * y)
      linarith
    have hexp : θ - 1 = -(1 / 2 : ℝ) + ε' := by rw [hθdef]; ring
    have h1 : (y / 4) ^ (θ - 1) ≤ 2 * y ^ (-(1 / 2 : ℝ) + ε') := by
      rw [hexp, Real.div_rpow hy0.le (by norm_num)]
      have h4 : (1 / 2 : ℝ) ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ) + ε') := by
        calc (1 / 2 : ℝ) = (4 : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [Real.rpow_neg (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
                ← Real.rpow_mul (by norm_num)]
              norm_num
          _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ) + ε') :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ y ^ (-(1 / 2 : ℝ) + ε') := Real.rpow_nonneg hy0.le _
      nlinarith
    have h2 : y ^ (-(1 / 2 : ℝ) + ε') ≤ y ^ (-(1 / 2 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hy (by linarith)
    calc ((⌊2 * y⌋₊ : ℝ) + 1) * (L / y * (y / 4) ^ (θ - 1))
        ≤ (3 * y) * (L / y * (2 * y ^ (-(1 / 2 : ℝ) + ε))) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 6 * L * y ^ (-(1 / 2 : ℝ) + ε) := by field_simp; ring
  have hdpow : (d : ℝ) ^ (1 + ε') ≤ (d : ℝ) ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd.prime.one_lt.le) (by linarith)
  calc |P.Ld d - P.Gsum W d y| ≤ B := hfinal
    _ ≤ K * (Z * (2 * y ^ (-(1 / 2 : ℝ) + ε)) + 6 * L * y ^ (-(1 / 2 : ℝ) + ε)) := by
        rw [hB]
        have h1 : (y / 4) ^ (θ - 1 + ε') * Z ≤ Z * (2 * y ^ (-(1 / 2 : ℝ) + ε)) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hpowA hZ0
        exact mul_le_mul_of_nonneg_left (add_le_add h1 hpowB) hK0
    _ = Cg * (2 * Z + 6 * L) * y ^ (-(1 / 2 : ℝ) + ε) * (d : ℝ) ^ (1 + ε') := by
        rw [hK]; ring
    _ ≤ Cg * (2 * Z + 6 * L) * y ^ (-(1 / 2 : ℝ) + ε) * (d : ℝ) ^ (1 + ε) := by
        gcongr

end PatternData

end Triples
