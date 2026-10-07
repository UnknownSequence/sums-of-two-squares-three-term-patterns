import TriplesFinal.Prelim.Weight
import TriplesFinal.Basic.Jacobi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lemma 5.1: a smoothed hyperbola identity for `r(n)`

Let `s ≥ 0` and `T = 2^s T'` with `T' ≡ 1 (mod 4)`. Then
`r(T) = 8 ∑_{k ∣ T} χ(k) W(2^(s/2) k / √T)`.

Paper: §5.1, Lemma 5.1. The proof uses Jacobi's formula `r(n) = 4 ∑_{k ∣ n} χ(k)`
(`r_eq_four_mul_sum_chi`).
-/

namespace Triples

open ZMod Real

/-- `χ₄(k) ∈ {±1}` for odd `k`. -/
theorem chi_four_sq_of_odd {k : ℕ} (hk : k % 2 = 1) : χ₄ (k : ZMod 4) * χ₄ (k : ZMod 4) = 1 := by
  rw [χ₄_nat_eq_if_mod_four]
  have : k % 4 = 1 ∨ k % 4 = 3 := by omega
  rcases this with h | h <;> simp [h, hk]

/-- For `T' ≡ 1 (mod 4)` and `k ∣ T'`: `χ₄(T'/k) = χ₄(k)`. -/
theorem chi_four_div {T' k : ℕ} (hT' : T' % 4 = 1) (hk : k ∣ T') :
    χ₄ ((T' / k : ℕ) : ZMod 4) = χ₄ (k : ZMod 4) := by
  have hkodd : k % 2 = 1 := by
    obtain ⟨m, rfl⟩ := hk
    rcases Nat.even_or_odd k with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exfalso
      have : (i + i) * m = 2 * (i * m) := by ring
      omega
    · omega
  have hmul : χ₄ (k : ZMod 4) * χ₄ ((T' / k : ℕ) : ZMod 4) = 1 := by
    rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hk, χ₄_nat_one_mod_four hT']
  have hsq := chi_four_sq_of_odd hkodd
  calc χ₄ ((T' / k : ℕ) : ZMod 4)
      = χ₄ (k : ZMod 4) * χ₄ (k : ZMod 4) * χ₄ ((T' / k : ℕ) : ZMod 4) := by rw [hsq, one_mul]
    _ = χ₄ (k : ZMod 4) * (χ₄ (k : ZMod 4) * χ₄ ((T' / k : ℕ) : ZMod 4)) := by ring
    _ = χ₄ (k : ZMod 4) := by rw [hmul, mul_one]

/-- The odd divisors of `2^s T'` (with `T'` odd) are the divisors of `T'`. -/
theorem divisors_filter_odd {s T' : ℕ} (hT' : T' % 2 = 1) :
    (2 ^ s * T').divisors.filter (fun k => k % 2 = 1) = T'.divisors := by
  ext k
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hT0 : T' ≠ 0 := by omega
  constructor
  · rintro ⟨⟨hdvd, -⟩, hk⟩
    refine ⟨?_, hT0⟩
    have hcop : Nat.Coprime k (2 ^ s) := by
      apply Nat.Coprime.pow_right
      exact (Nat.odd_iff.2 hk).coprime_two_right
    exact hcop.dvd_of_dvd_mul_left hdvd
  · rintro ⟨hdvd, -⟩
    refine ⟨⟨Dvd.dvd.mul_left hdvd _, by positivity⟩, ?_⟩
    obtain ⟨m, rfl⟩ := hdvd
    rcases Nat.even_or_odd k with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exfalso
      have : (i + i) * m = 2 * (i * m) := by ring
      omega
    · omega

/-- **Lemma 5.1.** Let `s ≥ 0` and `T = 2^s T'` with `T' ≡ 1 (mod 4)`. Then
`r(T) = 8 ∑_{k ∣ T} χ(k) W(2^(s/2) k / √T)`. -/
theorem hyperbola_identity (W : HyperbolaWeight) (s : ℕ) {T' : ℕ} (hT' : T' % 4 = 1) :
    (r ((2 ^ s * T' : ℕ) : ℤ) : ℝ) =
      8 * ∑ k ∈ (2 ^ s * T').divisors,
        (χ₄ (k : ZMod 4) : ℝ) * W.W ((2 : ℝ) ^ ((s : ℝ) / 2) * k / Real.sqrt ((2 ^ s * T' : ℕ) : ℝ)) := by
  have hT'odd : T' % 2 = 1 := by omega
  have hT'pos : 0 < T' := by omega
  have hTpos : 0 < 2 ^ s * T' := by positivity
  -- step 1: Jacobi
  have hJ := r_eq_four_mul_sum_chi (2 ^ s * T') hTpos
  -- step 2: only odd divisors contribute, and they are the divisors of `T'`
  have hsum : ∀ f : ℕ → ℝ, ∑ k ∈ (2 ^ s * T').divisors, (χ₄ (k : ZMod 4) : ℝ) * f k =
      ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * f k := by
    intro f
    rw [← divisors_filter_odd (s := s) hT'odd, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with hk
    · rfl
    · have : χ₄ (k : ZMod 4) = 0 := by
        rw [χ₄_nat_eq_if_mod_four]; simp [show k % 2 = 0 by omega]
      simp [this]
  -- step 3: the argument of `W` for `k ∣ T'`
  have hsqrt : Real.sqrt ((2 ^ s * T' : ℕ) : ℝ) = (2 : ℝ) ^ ((s : ℝ) / 2) * Real.sqrt T' := by
    have h2s : Real.sqrt ((2 : ℝ) ^ s) = (2 : ℝ) ^ ((s : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      ring_nf
    push_cast
    rw [Real.sqrt_mul (by positivity), h2s]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((s : ℝ) / 2) := by positivity
  have hT'sqrt : (0 : ℝ) < Real.sqrt T' := Real.sqrt_pos.2 (by exact_mod_cast hT'pos)
  have harg : ∀ k : ℕ, (2 : ℝ) ^ ((s : ℝ) / 2) * k / Real.sqrt ((2 ^ s * T' : ℕ) : ℝ) =
      k / Real.sqrt T' := by
    intro k
    rw [hsqrt, mul_div_mul_left _ _ h2pos.ne']
  -- step 4: symmetrisation
  have hsymm : ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) =
      2 * ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * W.W (k / Real.sqrt T') := by
    have h1 : ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) =
        ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * W.W (k / Real.sqrt T') +
          ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * W.W (Real.sqrt T' / k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
      have ht : (0 : ℝ) < k / Real.sqrt T' := by positivity
      have := W.symm _ ht
      rw [inv_div] at this
      rw [← mul_add, this, mul_one]
    have h2 : ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * W.W (Real.sqrt T' / k) =
        ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) * W.W (k / Real.sqrt T') := by
      rw [← Nat.sum_div_divisors T' (fun k => (χ₄ (k : ZMod 4) : ℝ) * W.W (Real.sqrt T' / k))]
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ∣ T' := Nat.dvd_of_mem_divisors hk
      have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
      rw [chi_four_div hT' hkd]
      congr 2
      rw [Nat.cast_div hkd (by exact_mod_cast hk0.ne')]
      have hT0 : (0 : ℝ) < T' := by exact_mod_cast hT'pos
      have hs := Real.mul_self_sqrt hT0.le
      rw [div_div_eq_mul_div, div_eq_div_iff hT0.ne' hT'sqrt.ne']
      linear_combination (k : ℝ) * hs
    rw [h1, h2]; ring
  -- step 5: combine
  have hr : (r ((2 ^ s * T' : ℕ) : ℤ) : ℝ) = 4 * ∑ k ∈ T'.divisors, (χ₄ (k : ZMod 4) : ℝ) := by
    have h1 := congrArg (fun z : ℤ => (z : ℝ)) hJ
    simp only [Int.cast_mul, Int.cast_sum, Int.cast_ofNat, Int.cast_natCast] at h1
    rw [h1]
    have h2 := hsum (fun _ => 1)
    simp only [mul_one] at h2
    rw [h2]
  rw [hr, hsymm, hsum]
  simp_rw [harg]
  ring

end Triples
