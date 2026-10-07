import TriplesFinal.GoodPrimes.Data

/-!
# Properties of good primes

For `d > d₁` we have `d²/2 ≤ m_d ≤ 2d²`. For a good prime `d`: `d ≡ 1 (mod 4)`, `d ∤ B`,
`d ∤ m_d`, `H_d = 2^(-v) m_d` is an odd positive integer with `d ∤ H_d`, and `N_d = E H_d` is
neither a square nor three times a square.

Paper: §4, the paragraphs after equation (4.1) and after the definition of good primes.
-/

namespace Triples

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

theorem B_pos : 0 < P.B := P.adm.1

theorem B_odd : P.B % 2 = 1 := P.adm.2.1

theorem d₁_pos : 0 < P.d₁ := by
  have := P.B_pos
  unfold d₁; positivity

/-- For `d > d₁`: `d² ≤ 2 m_d` and `m_d ≤ 2 d²`. -/
theorem m_bounds {d : ℤ} (hd : P.d₁ < d) : d ^ 2 ≤ 2 * P.m d ∧ P.m d ≤ 2 * d ^ 2 := by
  have hB := P.B_pos
  have hc0 := abs_nonneg P.c
  have hc1 := le_abs_self P.c
  have hc2 := neg_abs_le P.c
  unfold d₁ at hd
  have hd0 : 0 < d := by linarith
  have h8c : 8 * |P.c| < d := by linarith
  have h8B : 8 * P.B < d := by linarith
  have hm : P.m d = d ^ 2 + 2 * P.c * d + P.B ^ 2 := by
    unfold m mVal c; ring
  rw [hm]
  constructor
  · nlinarith
  · nlinarith

theorem m_pos {d : ℤ} (hd : P.d₁ < d) : 0 < P.m d := by
  have h := (P.m_bounds hd).1
  have : 0 < d := by have := P.d₁_pos; linarith
  nlinarith

/-- `d ≡ d₀ (mod 2^J)` implies `d ≡ 1 (mod 4)`. -/
theorem emod_four_of_modEq {d : ℤ} (hd : d ≡ P.d₀ [ZMOD 2 ^ P.J]) : d % 4 = 1 := by
  have h1 : (2 : ℤ) ^ P.J = 4 * 2 ^ P.v := by unfold J; rw [pow_add]; ring
  have := Int.ModEq.of_mul_right (2 ^ P.v) (h1 ▸ hd)
  have h2 : d % 4 = P.d₀ % 4 := this
  rw [h2]; exact P.hd₀

variable {P}

theorem IsGood.prime {d : ℕ} (hd : P.IsGood d) : d.Prime := hd.1

theorem IsGood.modEq {d : ℕ} (hd : P.IsGood d) : (d : ℤ) ≡ P.d₀ [ZMOD 2 ^ P.J] := hd.2.1

theorem IsGood.d₁_lt {d : ℕ} (hd : P.IsGood d) : P.d₁ < d := hd.2.2.1

theorem IsGood.emod_four {d : ℕ} (hd : P.IsGood d) : (d : ℤ) % 4 = 1 :=
  P.emod_four_of_modEq hd.modEq

theorem IsGood.B_lt {d : ℕ} (hd : P.IsGood d) : P.B < d := by
  have h := hd.d₁_lt
  have := abs_nonneg P.c
  have := P.B_pos
  unfold d₁ at h; linarith

/-- A good prime does not divide `B`. -/
theorem IsGood.not_dvd_B {d : ℕ} (hd : P.IsGood d) : ¬ (d : ℤ) ∣ P.B := by
  intro h
  have := Int.le_of_dvd P.B_pos h
  have := hd.B_lt
  linarith

/-- A good prime does not divide `m_d` (because `m_d ≡ B² (mod d)`). -/
theorem IsGood.not_dvd_m {d : ℕ} (hd : P.IsGood d) : ¬ (d : ℤ) ∣ P.m d := by
  intro h
  have h1 : (d : ℤ) ∣ P.m d - P.B ^ 2 := mVal_sub_sq_dvd P.B P.A d
  have h2 : (d : ℤ) ∣ P.B ^ 2 := by
    have := dvd_sub h h1
    simpa using this
  have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.1 hd.prime
  exact hd.not_dvd_B (hp.dvd_of_dvd_pow h2)

/-- `m_d = 2^v H_d`. -/
theorem IsGood.m_eq {d : ℕ} (hd : P.IsGood d) : P.m d = 2 ^ P.v * P.H d :=
  (P.m_eq d hd.modEq).1

/-- `H_d > 0`. -/
theorem IsGood.H_pos {d : ℕ} (hd : P.IsGood d) : 0 < P.H d := by
  have h1 := P.m_pos hd.d₁_lt
  rw [hd.m_eq] at h1
  exact pos_of_mul_pos_right h1 (by positivity)

/-- `H_d` is odd. -/
theorem IsGood.H_odd {d : ℕ} (hd : P.IsGood d) : P.H d % 2 = 1 := P.H_odd d hd.modEq

/-- A good prime does not divide `H_d`. -/
theorem IsGood.not_dvd_H {d : ℕ} (hd : P.IsGood d) : ¬ (d : ℤ) ∣ P.H d := by
  intro h
  apply hd.not_dvd_m
  rw [hd.m_eq]
  exact Dvd.dvd.mul_left h _

/-- `4^(v-j) N_d = m_d`. -/
theorem IsGood.four_pow_mul_N {d : ℕ} (hd : P.IsGood d) :
    4 ^ (P.v - P.j) * P.N d = P.m d := by
  rw [hd.m_eq]
  unfold N E
  have hjv := P.j_le_v
  have h2 := P.v_add_two_le_two_j
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← mul_assoc, ← pow_add]
  congr 2
  omega

theorem four_pow_eq_sq (n : ℕ) : (4 : ℤ) ^ n = (2 ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `N_d = E H_d` is not a perfect square. -/
theorem IsGood.N_not_sq {d : ℕ} (hd : P.IsGood d) : ¬ ∃ s : ℤ, P.N d = s ^ 2 := by
  rintro ⟨s, hs⟩
  apply hd.2.2.2.1
  refine ⟨2 ^ (P.v - P.j) * s, ?_⟩
  rw [← hd.four_pow_mul_N, hs, four_pow_eq_sq]
  ring

/-- `N_d = E H_d` is not three times a perfect square. -/
theorem IsGood.N_not_three_sq {d : ℕ} (hd : P.IsGood d) : ¬ ∃ s : ℤ, P.N d = 3 * s ^ 2 := by
  rintro ⟨s, hs⟩
  apply hd.2.2.2.2
  refine ⟨2 ^ (P.v - P.j) * s, ?_⟩
  rw [← hd.four_pow_mul_N, hs, four_pow_eq_sq]
  ring

/-- `N_d > 0`. -/
theorem IsGood.N_pos {d : ℕ} (hd : P.IsGood d) : 0 < P.N d := by
  have := hd.H_pos
  have : 0 < P.E := by rcases P.E_eq with h | h <;> rw [h] <;> norm_num
  unfold N; positivity

end PatternData

end Triples
