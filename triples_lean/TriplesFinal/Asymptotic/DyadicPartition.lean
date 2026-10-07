import TriplesFinal.Poisson.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A smooth dyadic partition of unity

With `χ(t) = 1 - s((t - 1)/(√2 - 1))` (`s` the smooth transition function), so that `χ = 1` on
`t ≤ 1` and `χ = 0` on `t ≥ √2`, put `ψ₀(t) = χ(t/√2) - χ(t)`. Then `ψ₀ ≥ 0` is smooth and
supported in `[1, 2]`, and `∑_{i ∈ ℤ} ψ₀(t/2^(i/2)) = 1` for `t > 0`, since the sum telescopes.
This is the partition of unity of the proof of Lemma 7.3 (`dyadicPartition`).

Paper: §7.3, proof of Lemma 7.3 (the paper normalises a bump function instead).
-/

namespace Triples

open scoped ContDiff
open Real

namespace Dyadic

/-- `χ(t) = 1 - s((t - 1)/(√2 - 1))`: smooth, `χ = 1` on `t ≤ 1`, `χ = 0` on `t ≥ √2`. -/
noncomputable def chi (t : ℝ) : ℝ := 1 - smoothTransition ((t - 1) / (Real.sqrt 2 - 1))

theorem sqrt_two_sub_one_pos : 0 < Real.sqrt 2 - 1 := by
  have : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem chi_eq_one {t : ℝ} (ht : t ≤ 1) : chi t = 1 := by
  unfold chi
  rw [smoothTransition.zero_of_nonpos, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) sqrt_two_sub_one_pos.le

theorem chi_eq_zero {t : ℝ} (ht : Real.sqrt 2 ≤ t) : chi t = 0 := by
  unfold chi
  rw [smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ sqrt_two_sub_one_pos]
  linarith

theorem chi_antitone : Antitone chi := by
  intro s t hst
  unfold chi
  have : (s - 1) / (Real.sqrt 2 - 1) ≤ (t - 1) / (Real.sqrt 2 - 1) :=
    div_le_div_of_nonneg_right (by linarith) sqrt_two_sub_one_pos.le
  linarith [smoothTransition.monotone this]

theorem contDiff_chi : ContDiff ℝ ∞ chi := by
  unfold chi
  apply contDiff_const.sub
  exact smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)

/-- `ψ₀(t) = χ(t/√2) - χ(t)`. -/
noncomputable def psi0 (t : ℝ) : ℝ := chi (t / Real.sqrt 2) - chi t

theorem psi0_eq_zero_of_le {t : ℝ} (ht : t ≤ 1) : psi0 t = 0 := by
  unfold psi0
  rw [chi_eq_one ht, chi_eq_one, sub_self]
  rcases le_or_gt t 0 with h | h
  · have : t / Real.sqrt 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg 2)
    linarith
  · rw [div_le_one (Real.sqrt_pos.2 (by norm_num))]
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith

theorem psi0_eq_zero_of_ge {t : ℝ} (ht : 2 ≤ t) : psi0 t = 0 := by
  unfold psi0
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs1 : Real.sqrt 2 ≤ 2 := by nlinarith
  have h1 : Real.sqrt 2 ≤ t / Real.sqrt 2 := by rw [le_div_iff₀ hs0]; linarith
  rw [chi_eq_zero h1, chi_eq_zero (by linarith), sub_self]

theorem psi0_nonneg (t : ℝ) : 0 ≤ psi0 t := by
  rcases le_or_gt t 1 with h | h
  · rw [psi0_eq_zero_of_le h]
  · unfold psi0
    have hs : t / Real.sqrt 2 ≤ t := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
    linarith [chi_antitone hs]

theorem psi0_support {t : ℝ} (ht : psi0 t ≠ 0) : 1 ≤ t ∧ t ≤ 2 := by
  constructor
  · by_contra h; exact ht (psi0_eq_zero_of_le (by linarith))
  · by_contra h; exact ht (psi0_eq_zero_of_ge (by linarith))

theorem contDiff_psi0 : ContDiff ℝ ∞ psi0 := by
  unfold psi0
  exact (contDiff_chi.comp (contDiff_id.div_const _)).sub contDiff_chi

/-- `2^((i+1)/2) = 2^(i/2) √2`. -/
theorem two_rpow_succ_half (i : ℤ) :
    (2 : ℝ) ^ (((i + 1 : ℤ) : ℝ) / 2) = (2 : ℝ) ^ ((i : ℝ) / 2) * Real.sqrt 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

/-- The telescoping sum. -/
theorem psi0_term (t : ℝ) (i : ℤ) :
    psi0 (t / (2 : ℝ) ^ ((i : ℝ) / 2)) =
      chi (t / (2 : ℝ) ^ (((i + 1 : ℤ) : ℝ) / 2)) - chi (t / (2 : ℝ) ^ ((i : ℝ) / 2)) := by
  unfold psi0
  rw [two_rpow_succ_half, div_div]

theorem hasSum_psi0 {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : ℤ => psi0 (t / (2 : ℝ) ^ ((i : ℝ) / 2))) 1 := by
  set a : ℤ → ℝ := fun i => chi (t / (2 : ℝ) ^ ((i : ℝ) / 2)) with ha
  -- `a i = 1` for large `i`, `a i = 0` for small `i`
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 2)
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (Real.sqrt 2 / t) (by norm_num : (1 : ℝ) < 2)
  have h2pos : ∀ i : ℤ, 0 < (2 : ℝ) ^ ((i : ℝ) / 2) := fun i => by positivity
  have hrpow_nat : ∀ n : ℕ, (2 : ℝ) ^ (((2 * n : ℤ) : ℝ) / 2) = 2 ^ n := by
    intro n
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hrpow_neg : ∀ n : ℕ, (2 : ℝ) ^ (((-(2 * n) : ℤ) : ℝ) / 2) = (2 ^ n)⁻¹ := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    congr 1
    push_cast
    ring
  have hmono : ∀ i j : ℤ, i ≤ j → (2 : ℝ) ^ ((i : ℝ) / 2) ≤ (2 : ℝ) ^ ((j : ℝ) / 2) := by
    intro i j hij
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have ha1 : ∀ i : ℤ, 2 * (N : ℤ) ≤ i → a i = 1 := by
    intro i hi
    simp only [ha]
    apply chi_eq_one
    rw [div_le_one (h2pos i)]
    have := hmono _ _ hi
    rw [hrpow_nat] at this
    linarith
  have ha0 : ∀ i : ℤ, i ≤ -(2 * (M : ℤ)) → a i = 0 := by
    intro i hi
    simp only [ha]
    apply chi_eq_zero
    have h1 := hmono _ _ hi
    rw [hrpow_neg] at h1
    rw [le_div_iff₀ (h2pos i)]
    have h2 : Real.sqrt 2 < t * 2 ^ M := by
      rw [div_lt_iff₀ ht] at hM; linarith
    have h3 : (2 : ℝ) ^ ((i : ℝ) / 2) * 2 ^ M ≤ 1 := by
      calc (2 : ℝ) ^ ((i : ℝ) / 2) * 2 ^ M ≤ (2 ^ M)⁻¹ * 2 ^ M := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have h4 : 0 < (2 : ℝ) ^ M := by positivity
    nlinarith [h2pos i]
  -- the sum over `[-2M, 2N)`
  set L : ℤ := -(2 * (M : ℤ)) with hL
  set n : ℕ := 2 * N + 2 * M with hn
  have hterm : ∀ i : ℤ, psi0 (t / (2 : ℝ) ^ ((i : ℝ) / 2)) = a (i + 1) - a i := by
    intro i
    rw [psi0_term]
  have hzero : ∀ i ∉ (Finset.range n).image (fun k : ℕ => L + k),
      psi0 (t / (2 : ℝ) ^ ((i : ℝ) / 2)) = 0 := by
    intro i hi
    rw [hterm]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hi
    rcases lt_or_ge i L with h | h
    · rw [ha0 i (by omega), ha0 (i + 1) (by omega), sub_self]
    · have hi' : L + n ≤ i := by
        by_contra hlt
        exact hi (i - L).toNat (by omega) (by omega)
      rw [ha1 i (by omega), ha1 (i + 1) (by omega), sub_self]
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) hzero
  convert hs using 1
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
  simp_rw [hterm]
  have htel := Finset.sum_range_sub (fun k : ℕ => a (L + k)) n
  have h' : ∀ k : ℕ, a (L + k + 1) - a (L + k) = a (L + ((k + 1 : ℕ) : ℤ)) - a (L + k) := by
    intro k; push_cast; ring_nf
  simp_rw [h']
  rw [htel]
  simp only [Nat.cast_zero, add_zero]
  rw [ha1 _ (by omega), ha0 _ (by omega)]
  norm_num

end Dyadic

/-- **A smooth dyadic partition of unity** exists. -/
noncomputable def dyadicPartition : DyadicPartition where
  ψ₀ := Dyadic.psi0
  smooth := Dyadic.contDiff_psi0
  nonneg := Dyadic.psi0_nonneg
  support := fun _ ht => Dyadic.psi0_support ht
  sum_eq_one := fun _ ht => Dyadic.hasSum_psi0 ht

end Triples
