import TriplesFinal.GoodPrimes.Properties
import TriplesFinal.Families.Split
import TriplesFinal.Families.Mult
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The weighted count `Σ_d(x)`

For a good prime `d`, a weight `F` and `x ≥ 1`,
`Σ_d(x) = ∑_{ℓ ∈ ℤ, d ∣ Eℓ² + H_d} r(T_d(ℓ)) F(T_d(ℓ)/x)` with
`T_d(ℓ) = 2^(v-2)(Eℓ² + H_d)/d = ((2^j ℓ)² + m_d)/(4d)` (equation (4.4)).

We show that `d ∣ Eℓ² + H_d` if and only if `d ∣ u² + B²` with `u = 2^j ℓ`, and that in this
case `T_d(ℓ)` is an integer with `4d T_d(ℓ) = u² + m_d` of the form `2^(v-2) T'` with
`T' ≡ 1 (mod 4)` (Proposition 3.2).

Paper: §4, equation (4.4) and the paragraph after it.
-/

namespace Triples

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `Σ_d(x) = ∑_{ℓ : d ∣ Eℓ² + H_d} r(T_d(ℓ)) F(T_d(ℓ)/x)`, equation (4.4). The sum is a
`finsum`; for the weights `F` that we use (supported in `[1/2, 1]`) only finitely many terms
are non-zero. -/
noncomputable def Sigma (F : ℝ → ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∑ᶠ (ℓ : ℤ) (_ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), (r (P.T d ℓ) : ℝ) * F ((P.T d ℓ : ℝ) / x)

variable {P}

/-- For a good prime `d`: `d ∣ Eℓ² + H_d ↔ d ∣ (2^j ℓ)² + B²`. -/
theorem IsGood.dvd_iff {d : ℕ} (hd : P.IsGood d) (ℓ : ℤ) :
    (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d ↔ (d : ℤ) ∣ (2 ^ P.j * ℓ) ^ 2 + P.B ^ 2 := by
  have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.1 hd.prime
  have h2 : ¬ (d : ℤ) ∣ 2 := by
    intro h
    have h4 := hd.emod_four
    have hle : (d : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
    have hd2 : 2 ≤ d := hd.prime.two_le
    omega
  have hpoly := P.poly_identity d ℓ hd.modEq
  have hmB : (d : ℤ) ∣ P.m d - P.B ^ 2 := mVal_sub_sq_dvd P.B P.A d
  constructor
  · intro h
    have h1 : (d : ℤ) ∣ (2 ^ P.j * ℓ) ^ 2 + P.m d := by
      rw [hpoly]; exact Dvd.dvd.mul_left h _
    have : (2 ^ P.j * ℓ) ^ 2 + P.B ^ 2 = ((2 ^ P.j * ℓ) ^ 2 + P.m d) - (P.m d - P.B ^ 2) := by
      ring
    rw [this]; exact dvd_sub h1 hmB
  · intro h
    have h1 : (d : ℤ) ∣ (2 ^ P.j * ℓ) ^ 2 + P.m d := by
      have : (2 ^ P.j * ℓ) ^ 2 + P.m d = ((2 ^ P.j * ℓ) ^ 2 + P.B ^ 2) + (P.m d - P.B ^ 2) := by
        ring
      rw [this]; exact dvd_add h hmB
    rw [hpoly] at h1
    rcases hp.dvd_or_dvd h1 with h3 | h3
    · exact absurd (hp.dvd_of_dvd_pow h3) h2
    · exact h3

/-- For a good prime `d` and `d ∣ Eℓ² + H_d`, the number `T_d(ℓ)` is an integer:
`4d T_d(ℓ) = (2^j ℓ)² + m_d`, and `T_d(ℓ) = 2^(v-2) T'` with `T' ≡ 1 (mod 4)`. -/
theorem IsGood.T_spec {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ} (hℓ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) :
    4 * d * P.T d ℓ = (2 ^ P.j * ℓ) ^ 2 + P.m d ∧
      ∃ T' : ℤ, T' % 4 = 1 ∧ P.T d ℓ = 2 ^ (P.v - 2) * T' := by
  have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.1 hd.prime
  have hdB := (hd.dvd_iff ℓ).1 hℓ
  have hu : 2 ^ P.j * ℓ ≡ 0 [ZMOD 2 ^ jOf P.v] := by
    apply Int.modEq_zero_iff_dvd.2
    exact Dvd.dvd.mul_right (dvd_refl _) _
  obtain ⟨w, hw, hwd⟩ := P.seed d (2 ^ P.j * ℓ) hd.modEq hu
  obtain ⟨T', hT'4, hT'⟩ := seed_T P.hv hp hd.emod_four hdB hw hwd
  have hd0 : (0 : ℤ) < 4 * d := by have := hd.prime.pos; positivity
  have hT : P.T d ℓ = 2 ^ (P.v - 2) * T' := by
    unfold T m
    rw [hT']
    exact Int.mul_ediv_cancel_left _ hd0.ne'
  refine ⟨?_, T', hT'4, hT⟩
  rw [hT]; unfold m; rw [hT']

/-- For a good prime `d` and `d ∣ Eℓ² + H_d`, `T_d(ℓ) ≥ 1`. -/
theorem IsGood.T_pos {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ} (hℓ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) :
    0 < P.T d ℓ := by
  obtain ⟨h1, -⟩ := hd.T_spec hℓ
  have hm := P.m_pos hd.d₁_lt
  have hd0 : (0 : ℤ) < 4 * d := by have := hd.prime.pos; positivity
  have : 0 < 4 * (d : ℤ) * P.T d ℓ := by rw [h1]; positivity
  exact pos_of_mul_pos_right this hd0.le

/-- For a good prime `d` and `d ∣ Eℓ² + H_d` with `P = T_d(ℓ) - A ≥ 1`, the numbers `P` and
`P + B` are sums of two squares (Lemmas 2.4 and 2.5). -/
theorem IsGood.split {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ} (hℓ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d)
    (hP : 1 ≤ P.T d ℓ - P.A) :
    IsSumTwoSq (P.T d ℓ - P.A) ∧ IsSumTwoSq (P.T d ℓ - P.A + P.B) := by
  obtain ⟨h1, -⟩ := hd.T_spec hℓ
  have hdp : (d : ℤ).natAbs.Prime := by simpa using hd.prime
  exact Triples.split hdp (by exact_mod_cast hd.prime.pos) hd.emod_four P.B_pos h1 hP

end PatternData

end Triples
