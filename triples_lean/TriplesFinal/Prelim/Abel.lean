import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# An Abelian theorem for Dirichlet series at `s = 1`

Let `a : ℕ → ℝ` with `a(0) = 0` and partial sums `A(N) = ∑_{k ≤ N} a(k)` satisfying
`|A(N)| ≤ K N^θ` for `N ≥ 1`, with `θ < 1`. Summation by parts (`sum_range_mul_eq_abel`) gives

* `∑_{k < N} a(k)/k → S := ∑_k A(k) (1/k - 1/(k+1))` (`tendsto_sum_div`), with
  `|S| ≤ 2K ∑_k k^(θ-2)` (`abs_tsum_abelTerm_le`);
* if `∑_k a(k) k^(-s)` converges absolutely for `1 < s ≤ 2`, then `∑_k a(k) k^(-s) → S` as
  `s → 1⁺` (`tendsto_tsum_rpow`, by dominated convergence, using
  `0 ≤ k^(-s) - (k+1)^(-s) ≤ 2k^(-2)` for `1 ≤ s ≤ 2`).

This is used for Lemma 5.3(c) (convergence of `𝔏_d`, its size, and the identification of `𝔏_d`
with the value at `s = 1` of the Dirichlet series), and for `L(1, χ₄) = π/4`.

Paper: §5.3, proof of Lemma 5.3(c).
-/

namespace Triples

open Filter Topology

/-- For `k ≥ 1` and `1 ≤ s ≤ 2`: `0 ≤ k^(-s) - (k+1)^(-s) ≤ 2 k^(-2)`. -/
theorem rpow_neg_sub_rpow_neg_le {k : ℝ} (hk : 1 ≤ k) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    0 ≤ k ^ (-s) - (k + 1) ^ (-s) ∧ k ^ (-s) - (k + 1) ^ (-s) ≤ 2 * k ^ (-(2 : ℝ)) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-s))
    (fun t => -s * t ^ (-s - 1)) (by linarith : k < k + 1)
    (by
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx; left; exact (by linarith [hx.1] : (0:ℝ) < x).ne')
    (by
      intro x hx
      exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : (0:ℝ) < x).ne'))
  simp only [add_sub_cancel_left, div_one] at hderiv
  have hc0 : 0 < c := by linarith [hc.1]
  have hpos : 0 < c ^ (-s - 1) := Real.rpow_pos_of_pos hc0 _
  have hle : c ^ (-s - 1) ≤ k ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hk0 hc.1.le (by linarith)
  have hle2 : k ^ (-s - 1) ≤ k ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  have heq : k ^ (-s) - (k + 1) ^ (-s) = s * c ^ (-s - 1) := by linarith
  rw [heq]
  constructor
  · positivity
  · calc s * c ^ (-s - 1) ≤ 2 * k ^ (-(2 : ℝ)) := by
          have : 0 ≤ k ^ (-(2 : ℝ)) := Real.rpow_nonneg hk0.le _
          nlinarith

/-- Partial sums `A(N) = ∑_{k ≤ N} a(k)`. -/
noncomputable def psum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range (N + 1), a k

theorem psum_zero (a : ℕ → ℝ) (ha0 : a 0 = 0) : psum a 0 = 0 := by simp [psum, ha0]

theorem psum_succ (a : ℕ → ℝ) (N : ℕ) : psum a (N + 1) = psum a N + a (N + 1) := by
  unfold psum; rw [Finset.sum_range_succ]

/-- Summation by parts: `∑_{k ≤ N} a(k) w(k) = A(N) w(N) + ∑_{k < N} A(k) (w(k) - w(k+1))`. -/
theorem sum_range_mul_eq_abel (a w : ℕ → ℝ) (ha0 : a 0 = 0) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), a k * w k =
      psum a N * w N + ∑ k ∈ Finset.range N, psum a k * (w k - w (k + 1)) := by
  induction N with
  | zero => simp [psum, ha0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => psum a k * (w k - w (k + 1))),
      psum_succ]
    ring

section Abel

variable {a : ℕ → ℝ} (ha0 : a 0 = 0) {K θ : ℝ} (hθ : θ < 1)
  (hA : ∀ N : ℕ, 1 ≤ N → |psum a N| ≤ K * (N : ℝ) ^ θ)
include ha0 hθ hA

/-- The terms `A(k) (k^(-s) - (k+1)^(-s))` of the summation by parts. -/
noncomputable def abelTerm (a : ℕ → ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  psum a k * ((k : ℝ) ^ (-s) - ((k : ℝ) + 1) ^ (-s))

theorem abs_abelTerm_le {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (k : ℕ) :
    |abelTerm a s k| ≤ 2 * K * (k : ℝ) ^ (θ - 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [abelTerm, psum_zero a ha0, Real.zero_rpow (by linarith : θ - 2 ≠ 0)]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  obtain ⟨h0, h1⟩ := rpow_neg_sub_rpow_neg_le hk1 hs1 hs2
  have hAk := hA k hk
  have hK : 0 ≤ K := by
    by_contra hK
    push Not at hK
    nlinarith [Real.rpow_pos_of_pos hk0 θ, abs_nonneg (psum a k)]
  rw [abelTerm, abs_mul, abs_of_nonneg h0]
  calc |psum a k| * ((k : ℝ) ^ (-s) - ((k : ℝ) + 1) ^ (-s))
      ≤ (K * (k : ℝ) ^ θ) * (2 * (k : ℝ) ^ (-(2 : ℝ))) :=
        mul_le_mul hAk h1 h0 (by positivity)
    _ = 2 * K * (k : ℝ) ^ (θ - 2) := by
        rw [sub_eq_add_neg, Real.rpow_add hk0]; ring

omit ha0 hA in
theorem summable_rpow_sub_two : Summable (fun k : ℕ => (k : ℝ) ^ (θ - 2)) :=
  Real.summable_nat_rpow.2 (by linarith)

theorem summable_abelTerm {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) : Summable (abelTerm a s) :=
  Summable.of_norm_bounded ((summable_rpow_sub_two hθ).mul_left (2 * K))
    (fun k => by rw [Real.norm_eq_abs]; exact abs_abelTerm_le ha0 hθ hA hs1 hs2 k)

omit hθ hA in
/-- Summation by parts with `w(k) = k^(-s)`. -/
theorem sum_range_rpow_eq (s : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), a k * (k : ℝ) ^ (-s) =
      psum a N * (N : ℝ) ^ (-s) + ∑ k ∈ Finset.range N, abelTerm a s k := by
  rw [sum_range_mul_eq_abel a (fun k => (k : ℝ) ^ (-s)) ha0 N]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [abelTerm]
  push_cast
  ring

omit ha0 hθ in
/-- `A(N) N^(-s) → 0` for `s > θ`. -/
theorem tendsto_psum_mul_rpow {s : ℝ} (hs : θ < s) :
    Tendsto (fun N : ℕ => psum a N * (N : ℝ) ^ (-s)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (θ - s)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < s - θ)).comp
      tendsto_natCast_atTop_atTop
    have h2 := h.const_mul K
    rw [mul_zero] at h2
    refine h2.congr (fun N => ?_)
    simp only [Function.comp_apply, neg_sub]
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
  calc |psum a N| * (N : ℝ) ^ (-s) ≤ K * (N : ℝ) ^ θ * (N : ℝ) ^ (-s) := by
        gcongr; exact hA N hN
    _ = K * (N : ℝ) ^ (θ - s) := by
        rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf

/-- For `1 ≤ s ≤ 2`: `∑_{k ≤ N} a(k) k^(-s) → ∑_k A(k) (k^(-s) - (k+1)^(-s))`. -/
theorem tendsto_sum_rpow {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), a k * (k : ℝ) ^ (-s)) atTop
      (𝓝 (∑' k, abelTerm a s k)) := by
  have h1 := tendsto_psum_mul_rpow hA (by linarith : θ < s)
  have h2 := (summable_abelTerm ha0 hθ hA hs1 hs2).hasSum.tendsto_sum_nat
  have := h1.add h2
  rw [zero_add] at this
  exact this.congr (fun N => (sum_range_rpow_eq ha0 s N).symm)

/-- **Convergence of `∑ a(k)/k`** to `S = ∑_k A(k) (1/k - 1/(k+1))`. -/
theorem tendsto_sum_div :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, a k / k) atTop
      (𝓝 (∑' k, abelTerm a 1 k)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  refine (tendsto_sum_rpow ha0 hθ hA le_rfl one_le_two).congr (fun N => ?_)
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- `|S| ≤ 2K ∑_k k^(θ-2)`. -/
theorem abs_tsum_abelTerm_le :
    |∑' k, abelTerm a 1 k| ≤ 2 * K * ∑' k : ℕ, (k : ℝ) ^ (θ - 2) := by
  rw [← tsum_mul_left]
  calc |∑' k, abelTerm a 1 k| = ‖∑' k, abelTerm a 1 k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k, ‖abelTerm a 1 k‖ :=
        norm_tsum_le_tsum_norm (summable_abelTerm ha0 hθ hA le_rfl one_le_two).norm
    _ ≤ ∑' k : ℕ, 2 * K * (k : ℝ) ^ (θ - 2) := by
        apply Summable.tsum_le_tsum _ (summable_abelTerm ha0 hθ hA le_rfl one_le_two).norm
          ((summable_rpow_sub_two hθ).mul_left _)
        intro k; rw [Real.norm_eq_abs]; exact abs_abelTerm_le ha0 hθ hA le_rfl one_le_two k

/-- `s ↦ ∑_k A(k) (k^(-s) - (k+1)^(-s))` is continuous at `s = 1` from the right (dominated
convergence). -/
theorem tendsto_tsum_abelTerm :
    Tendsto (fun s : ℝ => ∑' k, abelTerm a s k) (𝓝[>] 1) (𝓝 (∑' k, abelTerm a 1 k)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_rpow_sub_two hθ |>.mul_left (2 * K))
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [abelTerm, psum_zero a ha0, zero_mul]; exact tendsto_const_nhds
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.const_mul
    apply Tendsto.sub
    · exact ((Real.continuousAt_const_rpow hk0).comp continuous_neg.continuousAt).tendsto
    · exact ((Real.continuousAt_const_rpow hk1).comp continuous_neg.continuousAt).tendsto
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with s hs k
    rw [Real.norm_eq_abs]
    exact abs_abelTerm_le ha0 hθ hA hs.1.le hs.2.le k

/-- **The Abelian theorem.** If `∑ a(k) k^(-s)` converges absolutely for `1 < s ≤ 2`, then
`∑_k a(k) k^(-s) → S` as `s → 1⁺`. -/
theorem tendsto_tsum_rpow (hsum : ∀ s : ℝ, 1 < s → s ≤ 2 →
      Summable (fun k : ℕ => a k * (k : ℝ) ^ (-s))) :
    Tendsto (fun s : ℝ => ∑' k : ℕ, a k * (k : ℝ) ^ (-s)) (𝓝[>] 1)
      (𝓝 (∑' k, abelTerm a 1 k)) := by
  apply (tendsto_tsum_abelTerm ha0 hθ hA).congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with s hs
  have h1 := (hsum s hs.1 hs.2.le).hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat 1] at h1
  exact tendsto_nhds_unique (tendsto_sum_rpow ha0 hθ hA hs.1.le hs.2.le) h1

end Abel

end Triples
