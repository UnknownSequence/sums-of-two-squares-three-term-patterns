import TriplesFinal.Basic.RootCount
import TriplesFinal.GoodPrimes.Properties

/-!
# Lemma 5.2(c): the roots of `ν² ≡ -m_d (mod d^i)` for a good prime `d`

For a good prime `d`, `ϱ_{m_d}(d^i) = 2` for all `i ≥ 1`. Parts (a) and (b) of Lemma 5.2 do not
depend on the pattern and are in `Basic/RootCount.lean`. We also define `f(k) = ϱ(dk)/2` for odd
`k` (equation (5.2)).

Paper: §5.2, Lemma 5.2(c) and equation (5.2).
-/

namespace Triples

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- For a good prime `d`, `(-m_d/d) = 1`, because `m_d ≡ B² (mod d)`, `d ∤ B` and
`d ≡ 1 (mod 4)`. -/
theorem IsGood.legendre_neg_m {d : ℕ} (hd : P.IsGood d) [Fact d.Prime] (hd2 : d ≠ 2) :
    legendreSym d (-P.m d) = 1 := by
  have hcong : legendreSym d (-P.m d) = legendreSym d (-1 * P.B ^ 2) := by
    unfold legendreSym
    congr 1
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).2 (mVal_sub_sq_dvd P.B P.A d)
    push_cast at h1 ⊢
    unfold PatternData.m
    linear_combination -h1
  rw [hcong, legendreSym.mul, legendreSym.at_neg_one hd2, legendreSym.sq_one']
  · have h4 : d % 4 = 1 := by
      have := hd.emod_four
      omega
    rw [ZMod.χ₄_nat_one_mod_four h4, one_mul]
  · intro h
    apply hd.not_dvd_B
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).1 h

/-- **Lemma 5.2(c).** For a good prime `d` and `i ≥ 1`, `ϱ_{m_d}(d^i) = 2`. -/
theorem IsGood.rho_pow {d : ℕ} (hd : P.IsGood d) {i : ℕ} (hi : 1 ≤ i) :
    rho (P.m d) (d ^ i) = 2 := by
  have := Fact.mk hd.prime
  have hd2 : d ≠ 2 := by
    intro h
    have := hd.emod_four
    rw [h] at this
    norm_num at this
  have h := rho_prime_pow_of_not_dvd hd2 hd.not_dvd_m hi
  rw [hd.legendre_neg_m hd2] at h
  omega

variable (P)

/-- `f(k) = ϱ(dk)/2` for odd `k` and `f(k) = 0` for even `k` (equation (5.2)). -/
noncomputable def fd (d k : ℕ) : ℝ := if k % 2 = 1 then (rho (P.m d) (d * k) : ℝ) / 2 else 0

end PatternData

end Triples
