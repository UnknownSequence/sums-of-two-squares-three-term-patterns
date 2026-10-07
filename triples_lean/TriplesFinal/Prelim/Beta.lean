import TriplesFinal.Prelim.SingularSeries
import TriplesFinal.Basic.Jacobi
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Lemma 5.3(b),(c): the factorization `χ f = χ ∗ ψ ∗ β`

Let `d` be a good prime and `m = m_d`. We work with integer-valued arithmetic functions:

* `chiAF = χ₄`, `psiAF m = ψ` (completely multiplicative);
* `fAF d k = ϱ(k')` for odd `k`, where `k'` is the largest divisor of `k` prime to `d`, and
  `fAF d k = 0` for even `k`; for a good prime this is `f(k) = ϱ(dk)/2` (`IsGood.fAF_eq`);
* `gAF d = χ f` and `betaAF d = g ∗ μχ ∗ μψ`, so that `g = χ ∗ ψ ∗ β` (`gAF_eq`), since
  `a ∗ μa = 1` for completely multiplicative `a` (`mul_pmul_moebius_eq_one`).

The function `β` is multiplicative, and its values at prime powers are those listed in the proof
of Lemma 5.3(b):

* `β(2^i) = 0` for `i ≥ 1`;
* `β(d) = -1` and `β(d^i) = 0` for `i ≥ 2`;
* for odd primes `ℓ ∤ dm`: `β(ℓ) = 0`, `β(ℓ²) = -1` and `β(ℓ^i) = 0` for `i ≥ 3`;
* for odd primes `ℓ ∣ m`: `β(ℓ^i) = χ(ℓ)^i (ϱ(ℓ^i) - ϱ(ℓ^(i-1)))` for `i ≥ 1`.

Paper: §5.3, proof of Lemma 5.3(b).
-/

namespace Triples

open ArithmeticFunction ZMod
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

section General

/-- For a completely multiplicative `a` with `a 1 = 1`: `a * (μ · a) = 1`. -/
theorem mul_pmul_moebius_eq_one {a : ArithmeticFunction ℤ} (ha1 : a 1 = 1)
    (ha : ∀ m n, a (m * n) = a m * a n) : a * (moebius : ArithmeticFunction ℤ).pmul a = 1 := by
  ext n
  rw [mul_apply]
  have h1 : ∀ x ∈ n.divisorsAntidiagonal,
      a x.1 * ((moebius : ArithmeticFunction ℤ).pmul a) x.2 = a n * (moebius x.2) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [pmul_apply, ← hx.1, ha]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have h2 : ∑ x ∈ n.divisorsAntidiagonal, (moebius x.2 : ℤ) =
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) * moebius) n := by
    rw [mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have : x.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hx
      exact hx.2 hx.1.symm
    simp [natCoe_apply, this]
  rw [h2, coe_zeta_mul_moebius]
  by_cases hn : n = 1
  · subst hn; simp [ha1]
  · simp [one_apply_ne hn]

/-- `(h * μ · a)(p^(k+1)) = h(p^(k+1)) - a(p) h(p^k)` when `a 1 = 1`. -/
theorem mul_pmul_moebius_prime_pow (h a : ArithmeticFunction ℤ) (ha1 : a 1 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (h * (moebius : ArithmeticFunction ℤ).pmul a) (p ^ (k + 1)) =
      h (p ^ (k + 1)) - a p * h (p ^ k) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal
      (fun x y => h x * ((moebius : ArithmeticFunction ℤ).pmul a) y),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∑ x ∈ Finset.range k,
      h (p ^ x) * ((moebius : ArithmeticFunction ℤ).pmul a) (p ^ (k + 1) / p ^ x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.pow_div (by omega) hp.pos, pmul_apply, moebius_apply_prime_pow hp (by omega)]
    simp only [show k + 1 - i ≠ 1 by omega, ite_false, zero_mul, mul_zero]
  rw [hzero, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos]
  simp [pmul_apply, moebius_apply_prime hp, ha1, pow_succ]
  ring

/-- `(h * μ · a)(1) = h(1)` when `a 1 = 1`. -/
theorem mul_pmul_moebius_one (h a : ArithmeticFunction ℤ) (ha1 : a 1 = 1) :
    (h * (moebius : ArithmeticFunction ℤ).pmul a) 1 = h 1 := by
  rw [mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp [pmul_apply, ha1]

end General

/-! ### The arithmetic functions `χ`, `ψ`, `f`, `g = χ f` and `β` -/

theorem chiAF_one : chiAF 1 = 1 := by simp [chiAF_apply]

theorem chiAF_mul (m n : ℕ) : chiAF (m * n) = chiAF m * chiAF n := by
  simp only [chiAF_apply, Nat.cast_mul, map_mul]

/-- `ψ` as an arithmetic function. -/
def psiAF (m : ℤ) : ArithmeticFunction ℤ := ⟨psi m, by simp [psi]⟩

theorem psiAF_apply (m : ℤ) (n : ℕ) : psiAF m n = psi m n := rfl

theorem psiAF_one (m : ℤ) : psiAF m 1 = 1 := psi_one m

theorem psiAF_mul (m : ℤ) (k n : ℕ) : psiAF m (k * n) = psiAF m k * psiAF m n := psi_mul m k n

theorem isMultiplicative_of_completely {a : ArithmeticFunction ℤ} (ha1 : a 1 = 1)
    (ha : ∀ m n, a (m * n) = a m * a n) : IsMultiplicative a :=
  ⟨ha1, fun {m n} _ => ha m n⟩

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `f(k) = ϱ(k')` for odd `k`, where `k'` is the largest divisor of `k` prime to `d`, and
`f(k) = 0` for even `k`. For a good prime `d` this agrees with `ϱ(dk)/2` (`IsGood.fAF_eq`). -/
def fAF (d : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun k => if k % 2 = 1 then (rho (P.m d) (ordCompl[d] k) : ℤ) else 0, by simp⟩

theorem fAF_apply (d k : ℕ) :
    P.fAF d k = if k % 2 = 1 then (rho (P.m d) (ordCompl[d] k) : ℤ) else 0 := rfl

/-- `g = χ f`. -/
def gAF (d : ℕ) : ArithmeticFunction ℤ := chiAF.pmul (P.fAF d)

/-- `β = g ∗ μχ ∗ μψ`, so that `g = χ ∗ ψ ∗ β`. -/
def betaAF (d : ℕ) : ArithmeticFunction ℤ :=
  P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF *
    (moebius : ArithmeticFunction ℤ).pmul (psiAF (P.m d))

theorem fAF_isMultiplicative (d : ℕ) : IsMultiplicative (P.fAF d) := by
  refine ⟨?_, fun {k n} hkn => ?_⟩
  · simp [fAF_apply, rho_one]
  · rw [fAF_apply, fAF_apply, fAF_apply]
    by_cases hk : k % 2 = 1 <;> by_cases hn : n % 2 = 1
    · have hkn2 : k * n % 2 = 1 := by rw [Nat.mul_mod, hk, hn]
      rw [ite_eq_left hkn2, ite_eq_left hk, ite_eq_left hn, Nat.ordCompl_mul]
      have hcop : Nat.Coprime (ordCompl[d] k) (ordCompl[d] n) :=
        Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd k d)
          (Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd n d) hkn)
      rw [rho_mul _ hcop]
      push_cast
      ring
    · have hkn2 : ¬ k * n % 2 = 1 := by
        rw [Nat.mul_mod]; have : n % 2 = 0 := by omega
        rw [this]; simp
      rw [ite_eq_right hkn2, ite_eq_right hn, mul_zero]
    · have hkn2 : ¬ k * n % 2 = 1 := by
        rw [Nat.mul_mod]; have : k % 2 = 0 := by omega
        rw [this]; simp
      rw [ite_eq_right hkn2, ite_eq_right hk, zero_mul]
    · have hkn2 : ¬ k * n % 2 = 1 := by
        rw [Nat.mul_mod]; have : k % 2 = 0 := by omega
        rw [this]; simp
      rw [ite_eq_right hkn2, ite_eq_right hk, zero_mul]

theorem gAF_isMultiplicative (d : ℕ) : IsMultiplicative (P.gAF d) :=
  (isMultiplicative_of_completely chiAF_one chiAF_mul).pmul (P.fAF_isMultiplicative d)

theorem betaAF_isMultiplicative (d : ℕ) : IsMultiplicative (P.betaAF d) :=
  ((P.gAF_isMultiplicative d).mul
    (isMultiplicative_moebius.pmul (isMultiplicative_of_completely chiAF_one chiAF_mul))).mul
    (isMultiplicative_moebius.pmul
      (isMultiplicative_of_completely (psiAF_one _) (psiAF_mul _)))

/-- **The factorization** `χ f = χ ∗ ψ ∗ β`. -/
theorem gAF_eq (d : ℕ) : P.gAF d = chiAF * psiAF (P.m d) * P.betaAF d := by
  unfold betaAF
  calc P.gAF d = P.gAF d * (chiAF * (moebius : ArithmeticFunction ℤ).pmul chiAF) *
        (psiAF (P.m d) * (moebius : ArithmeticFunction ℤ).pmul (psiAF (P.m d))) := by
          rw [mul_pmul_moebius_eq_one chiAF_one chiAF_mul,
            mul_pmul_moebius_eq_one (psiAF_one _) (psiAF_mul _), mul_one, mul_one]
    _ = _ := by ring

theorem gAF_apply (d n : ℕ) : P.gAF d n = chiAF n * P.fAF d n := pmul_apply

theorem gAF_one (d : ℕ) : P.gAF d 1 = 1 := (P.gAF_isMultiplicative d).map_one

theorem chiAF_pow (p k : ℕ) : chiAF (p ^ k) = chiAF p ^ k := by
  simp only [chiAF_apply, Nat.cast_pow, map_pow]

theorem chiAF_two : chiAF 2 = 0 := by
  rw [chiAF_apply]; decide

/-- `β(p^(k+1)) = H(p^(k+1)) - ψ(p) H(p^k)` with `H = g ∗ μχ`. -/
theorem betaAF_prime_pow_succ (d : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    P.betaAF d (p ^ (k + 1)) =
      (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) (p ^ (k + 1)) -
        psiAF (P.m d) p * (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) (p ^ k) :=
  mul_pmul_moebius_prime_pow _ _ (psiAF_one _) hp k

theorem gmu_prime_pow_succ (d : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) (p ^ (k + 1)) =
      P.gAF d (p ^ (k + 1)) - chiAF p * P.gAF d (p ^ k) :=
  mul_pmul_moebius_prime_pow _ _ chiAF_one hp k

theorem gmu_one (d : ℕ) : (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) 1 = 1 := by
  rw [mul_pmul_moebius_one _ _ chiAF_one, P.gAF_one]

theorem betaAF_one (d : ℕ) : P.betaAF d 1 = 1 := (P.betaAF_isMultiplicative d).map_one

/-- `β(2^(k+1)) = 0`. -/
theorem betaAF_two_pow (d k : ℕ) : P.betaAF d (2 ^ (k + 1)) = 0 := by
  have hψ2 : psiAF (P.m d) 2 = 0 := by simp [psiAF_apply, psi]
  have hg : ∀ j, P.gAF d (2 ^ (j + 1)) = 0 := by
    intro j; rw [gAF_apply, chiAF_pow, chiAF_two]; simp
  rw [P.betaAF_prime_pow_succ d Nat.prime_two, P.gmu_prime_pow_succ d Nat.prime_two, hψ2, hg,
    chiAF_two]
  ring

variable {P}

/-- For a good prime `d` and odd `k`: `ϱ(dk) = 2 ϱ(k')`, `k'` the part of `k` prime to `d`. -/
theorem IsGood.rho_d_mul {d : ℕ} (hd : P.IsGood d) {k : ℕ} (hk : k ≠ 0) :
    rho (P.m d) (d * k) = 2 * rho (P.m d) (ordCompl[d] k) := by
  have hdp := hd.prime
  set e := k.factorization d with he
  have hk' : d ^ e * ordCompl[d] k = k := Nat.ordProj_mul_ordCompl_eq_self k d
  have hcop : Nat.Coprime (d ^ (e + 1)) (ordCompl[d] k) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hdp hk)
  calc rho (P.m d) (d * k) = rho (P.m d) (d ^ (e + 1) * ordCompl[d] k) := by
        conv_lhs => rw [← hk']
        congr 1; ring
    _ = rho (P.m d) (d ^ (e + 1)) * rho (P.m d) (ordCompl[d] k) := rho_mul _ hcop
    _ = 2 * rho (P.m d) (ordCompl[d] k) := by rw [hd.rho_pow (by omega)]

/-- `f(k) = ϱ(dk)/2` (equation (5.2)). -/
theorem IsGood.fAF_eq {d : ℕ} (hd : P.IsGood d) (k : ℕ) : (P.fAF d k : ℝ) = P.fd d k := by
  rw [fAF_apply, fd]
  split_ifs with hk
  · have hk0 : k ≠ 0 := by omega
    rw [hd.rho_d_mul hk0]; push_cast; ring
  · simp

theorem IsGood.d_odd {d : ℕ} (hd : P.IsGood d) : d % 2 = 1 := by
  have := hd.emod_four; omega

theorem IsGood.d_mod_four {d : ℕ} (hd : P.IsGood d) : d % 4 = 1 := by
  have := hd.emod_four; omega

theorem IsGood.chiAF_d {d : ℕ} (hd : P.IsGood d) : chiAF d = 1 := by
  rw [chiAF_apply]; exact χ₄_nat_one_mod_four hd.d_mod_four

theorem IsGood.psiAF_d {d : ℕ} (hd : P.IsGood d) : psiAF (P.m d) d = 1 := by
  have := Fact.mk hd.prime
  have hd2 : d ≠ 2 := by have := hd.d_odd; omega
  rw [psiAF_apply, psi, ite_eq_left hd.d_odd, ← jacobiSym.legendreSym.to_jacobiSym]
  have h1 := hd.legendre_neg_m hd2
  have h2 := legendreSym.at_neg_one (p := d) hd2
  rw [χ₄_nat_one_mod_four hd.d_mod_four] at h2
  have : P.m d = (-1) * (-P.m d) := by ring
  rw [this, legendreSym.mul, h1, h2]
  norm_num

theorem IsGood.fAF_d_pow {d : ℕ} (hd : P.IsGood d) (k : ℕ) : P.fAF d (d ^ k) = 1 := by
  have hodd : d ^ k % 2 = 1 := Nat.odd_iff.1 ((Nat.odd_iff.2 hd.d_odd).pow)
  rw [fAF_apply, ite_eq_left hodd, Nat.ordCompl_self_pow hd.prime, rho_one]
  rfl

theorem IsGood.gAF_d_pow {d : ℕ} (hd : P.IsGood d) (k : ℕ) : P.gAF d (d ^ k) = 1 := by
  rw [gAF_apply, chiAF_pow, hd.chiAF_d, hd.fAF_d_pow]; simp

theorem IsGood.gmu_d_pow {d : ℕ} (hd : P.IsGood d) (k : ℕ) :
    (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) (d ^ (k + 1)) = 0 := by
  rw [P.gmu_prime_pow_succ d hd.prime, hd.gAF_d_pow, hd.gAF_d_pow, hd.chiAF_d]; ring

/-- `β(d) = -1`. -/
theorem IsGood.betaAF_d {d : ℕ} (hd : P.IsGood d) : P.betaAF d d = -1 := by
  have h := P.betaAF_prime_pow_succ d hd.prime 0
  rw [hd.gmu_d_pow, pow_zero, P.gmu_one, hd.psiAF_d, zero_add, pow_one] at h
  rw [h]; ring

/-- `β(d^(k+2)) = 0`. -/
theorem IsGood.betaAF_d_pow {d : ℕ} (hd : P.IsGood d) (k : ℕ) : P.betaAF d (d ^ (k + 2)) = 0 := by
  rw [P.betaAF_prime_pow_succ d hd.prime (k + 1), hd.gmu_d_pow, hd.gmu_d_pow]; ring

theorem IsGood.fAF_prime_pow {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d) (k : ℕ) : P.fAF d (p ^ k) = rho (P.m d) (p ^ k) := by
  have hodd : p ^ k % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hnd : ¬ d ∣ p ^ k := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hd.prime hp).1 (hd.prime.dvd_of_dvd_pow h)
    exact hpd this.symm
  rw [fAF_apply, ite_eq_left hodd,
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ hd.prime).2 (Or.inr hnd)]

theorem chiAF_sq_of_odd {p : ℕ} (hp : p % 2 = 1) : chiAF p ^ 2 = 1 := by
  rw [chiAF_apply, χ₄_nat_eq_if_mod_four]
  have : p % 2 ≠ 0 := by omega
  rw [ite_eq_right this]
  split_ifs <;> norm_num

theorem psiAF_prime {m : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    psiAF m p = legendreSym p m := by
  have hodd : p % 2 = 1 := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp2)
  rw [psiAF_apply, psi, ite_eq_left hodd, jacobiSym.legendreSym.to_jacobiSym]

/-- For an odd prime `p ∤ m`: `(-m/p) = χ(p) ψ(p)`. -/
theorem legendre_neg_eq {m : ℤ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (-m) = chiAF p * psiAF m p := by
  rw [psiAF_prime hp2, show -m = (-1) * m by ring, legendreSym.mul, legendreSym.at_neg_one hp2,
    chiAF_apply]

/-- For an odd prime `p ∤ m`: `ψ(p)² = 1`. -/
theorem psiAF_sq_of_not_dvd {m : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ (p : ℤ) ∣ m) :
    psiAF m p ^ 2 = 1 := by
  have := Fact.mk hp
  rw [psiAF_prime hp2]
  apply legendreSym.sq_one
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- For an odd prime `p ∣ m`: `ψ(p) = 0`. -/
theorem psiAF_of_dvd {m : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : (p : ℤ) ∣ m) :
    psiAF m p = 0 := by
  have := Fact.mk hp
  rw [psiAF_prime hp2, legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hpm

section NotDvd

variable {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d)
  (hpm : ¬ (p : ℤ) ∣ P.m d)
include hd hp hp2 hpd hpm

/-- For an odd prime `p ≠ d` with `p ∤ m`: `g(p^(k+1)) = χ(p)^(k+1) (1 + χ(p) ψ(p))`. -/
theorem IsGood.gAF_prime_pow_of_not_dvd (k : ℕ) :
    P.gAF d (p ^ (k + 1)) = chiAF p ^ (k + 1) * (1 + chiAF p * psiAF (P.m d) p) := by
  have := Fact.mk hp
  rw [gAF_apply, chiAF_pow, hd.fAF_prime_pow hp hp2 hpd,
    rho_prime_pow_of_not_dvd hp2 hpm (by omega), legendre_neg_eq hp2]

theorem IsGood.gmu_prime_of_not_dvd :
    (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) p = psiAF (P.m d) p := by
  have h := P.gmu_prime_pow_succ d hp 0
  rw [zero_add, pow_one, pow_zero, P.gAF_one] at h
  have hg := hd.gAF_prime_pow_of_not_dvd hp hp2 hpd hpm 0
  rw [zero_add, pow_one] at hg
  have ha := chiAF_sq_of_odd (Nat.odd_iff.1 (hp.odd_of_ne_two hp2))
  rw [h, hg]
  linear_combination psiAF (P.m d) p * ha

theorem IsGood.gmu_prime_pow_of_not_dvd (k : ℕ) :
    (P.gAF d * (moebius : ArithmeticFunction ℤ).pmul chiAF) (p ^ (k + 2)) = 0 := by
  rw [P.gmu_prime_pow_succ d hp, hd.gAF_prime_pow_of_not_dvd hp hp2 hpd hpm,
    hd.gAF_prime_pow_of_not_dvd hp hp2 hpd hpm]
  ring

/-- `β(p) = 0` for an odd prime `p ∤ dm`. -/
theorem IsGood.betaAF_prime_of_not_dvd : P.betaAF d p = 0 := by
  have h := P.betaAF_prime_pow_succ d hp 0
  rw [zero_add, pow_one, pow_zero, P.gmu_one, hd.gmu_prime_of_not_dvd hp hp2 hpd hpm] at h
  rw [h]; ring

/-- `β(p²) = -1` for an odd prime `p ∤ dm`. -/
theorem IsGood.betaAF_prime_sq_of_not_dvd : P.betaAF d (p ^ 2) = -1 := by
  have h := P.betaAF_prime_pow_succ d hp 1
  rw [hd.gmu_prime_pow_of_not_dvd hp hp2 hpd hpm 0, pow_one,
    hd.gmu_prime_of_not_dvd hp hp2 hpd hpm] at h
  rw [show p ^ 2 = p ^ (1 + 1) by norm_num, h]
  linear_combination -psiAF_sq_of_not_dvd hp hp2 hpm

/-- `β(p^(k+3)) = 0` for an odd prime `p ∤ dm`. -/
theorem IsGood.betaAF_prime_pow_of_not_dvd (k : ℕ) : P.betaAF d (p ^ (k + 3)) = 0 := by
  rw [P.betaAF_prime_pow_succ d hp (k + 2), hd.gmu_prime_pow_of_not_dvd hp hp2 hpd hpm,
    hd.gmu_prime_pow_of_not_dvd hp hp2 hpd hpm]
  ring

end NotDvd

section Dvd

variable {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : (p : ℤ) ∣ P.m d)
include hd hp hp2 hpm

omit hp hp2 in
theorem IsGood.ne_of_dvd_m : p ≠ d := by
  rintro rfl
  exact hd.not_dvd_m hpm

/-- `β(p^(k+1)) = χ(p)^(k+1) (ϱ(p^(k+1)) - ϱ(p^k))` for an odd prime `p ∣ m`. -/
theorem IsGood.betaAF_prime_pow_of_dvd (k : ℕ) :
    P.betaAF d (p ^ (k + 1)) =
      chiAF p ^ (k + 1) * ((rho (P.m d) (p ^ (k + 1)) : ℤ) - rho (P.m d) (p ^ k)) := by
  have hpd := hd.ne_of_dvd_m hpm
  rw [P.betaAF_prime_pow_succ d hp, psiAF_of_dvd hp hp2 hpm, zero_mul, sub_zero,
    P.gmu_prime_pow_succ d hp, gAF_apply, gAF_apply, chiAF_pow, chiAF_pow,
    hd.fAF_prime_pow hp hp2 hpd, hd.fAF_prime_pow hp hp2 hpd]
  ring

end Dvd

end PatternData

end Triples
