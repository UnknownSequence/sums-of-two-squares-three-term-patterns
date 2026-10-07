import TriplesFinal.Basic.AllReps
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Jacobi's two-square theorem

`r(n) = 4 ∑_{k ∣ n} χ(k)` for `n ≥ 1`, where `χ = χ₄` is the non-principal character modulo `4`.

This classical theorem (Jacobi 1829) is used in Lemma 5.1. It is not in Mathlib; we prove it
here from scratch, by the following elementary argument.

* `r(n) = ∑_{k² ∣ n} r*(n/k²)` (`Basic/AllReps.lean`), and `r*(m) = 4 ϱ₁(m)` with
  `ϱ₁(m) = #{ν mod m : ν² + 1 ≡ 0 (mod m)}` (`Basic/PrimitiveReps.lean`, using Thue's lemma).
* Hence `r(n)/4 = (ϱ₁ ∗ 𝟙_□)(n)`, where `𝟙_□` is the indicator function of the squares.
* Both `ϱ₁ ∗ 𝟙_□` and `χ₄ ∗ 1` are multiplicative, and they agree on prime powers:
  `ϱ₁(2) = 1`, `ϱ₁(2^i) = 0` for `i ≥ 2`, and `ϱ₁(p^i) = 1 + χ₄(p)` for odd `p` and `i ≥ 1`
  (Lemma 5.2(b) and the first supplementary law `(-1/p) = χ₄(p)`).

Paper: §1, Notation.
-/

namespace Triples

open ZMod

open ArithmeticFunction
open scoped ArithmeticFunction.zeta

/-- `ϱ₁(n) = #{ν mod n : ν² + 1 ≡ 0 (mod n)}` as an arithmetic function. -/
def rhoAF : ArithmeticFunction ℤ := ⟨fun n => (rho 1 n : ℤ), by simp [rho]⟩

/-- The indicator function of the (non-zero) squares. -/
def sqAF : ArithmeticFunction ℤ := ⟨fun n => if n ≠ 0 ∧ IsSquare n then 1 else 0, by simp⟩

/-- `χ₄` as an arithmetic function. -/
def chiAF : ArithmeticFunction ℤ := ⟨fun n => χ₄ (n : ZMod 4), by simp⟩

theorem rhoAF_apply (n : ℕ) : rhoAF n = rho 1 n := rfl
theorem sqAF_apply (n : ℕ) : sqAF n = if n ≠ 0 ∧ IsSquare n then 1 else 0 := rfl
theorem chiAF_apply (n : ℕ) : chiAF n = χ₄ (n : ZMod 4) := rfl

theorem isMultiplicative_rhoAF : rhoAF.IsMultiplicative := by
  refine ⟨by rw [rhoAF_apply, rho_one]; rfl, fun {m n} h => ?_⟩
  rw [rhoAF_apply, rhoAF_apply, rhoAF_apply, rho_mul 1 h]
  push_cast; ring

theorem isSquare_mul_of_coprime {m n : ℕ} (h : m.Coprime n) (hmn : IsSquare (m * n)) :
    IsSquare m ∧ IsSquare n := by
  obtain ⟨c, hc⟩ := hmn
  have hu : IsUnit (gcd m n) := by
    rw [Nat.isUnit_iff]; exact h
  have hu' : IsUnit (gcd n m) := by
    rw [Nat.isUnit_iff, gcd_comm]; exact h
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu (k := 2) (by rw [hc]; ring)
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu' (k := 2) (by rw [mul_comm, hc]; ring)
  exact ⟨⟨a, by rw [ha]; ring⟩, ⟨b, by rw [hb]; ring⟩⟩

theorem isMultiplicative_sqAF : sqAF.IsMultiplicative := by
  refine ⟨by simp [sqAF_apply], fun {m n} h => ?_⟩
  simp only [sqAF_apply]
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hn : n = 0
  · subst hn; simp
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  by_cases hsq : IsSquare (m * n)
  · obtain ⟨h1, h2⟩ := isSquare_mul_of_coprime h hsq
    simp [hm, hn, hmn, hsq, h1, h2]
  · have : ¬ (IsSquare m ∧ IsSquare n) := fun ⟨h1, h2⟩ => hsq (h1.mul h2)
    by_cases h1 : IsSquare m
    · have h2 : ¬ IsSquare n := fun h2 => this ⟨h1, h2⟩
      simp [hm, hn, hmn, hsq, h1, h2]
    · simp [hm, hn, hmn, hsq, h1]

theorem isMultiplicative_chiAF : chiAF.IsMultiplicative := by
  refine ⟨by simp [chiAF_apply], fun {m n} _ => ?_⟩
  simp only [chiAF_apply, Nat.cast_mul, map_mul]

/-- `(f * g)(p^e) = ∑_{i ≤ e} f(p^i) g(p^(e-i))`. -/
theorem mul_apply_prime_pow (f g : ArithmeticFunction ℤ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (f * g) (p ^ e) = ∑ i ∈ Finset.range (e + 1), f (p ^ i) * g (p ^ (e - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by omega) hp.pos]

theorem isSquare_prime_pow_iff {p : ℕ} (hp : p.Prime) (j : ℕ) : IsSquare (p ^ j) ↔ Even j := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact pow_ne_zero j hp.ne_zero (by simpa using hc)
    have h1 := congrArg (fun n => n.factorization p) hc
    simp only [Nat.factorization_pow, Nat.Prime.factorization_self hp, Nat.factorization_mul hc0 hc0,
      Finsupp.smul_apply, Finsupp.coe_add, Pi.add_apply, smul_eq_mul, mul_one] at h1
    exact ⟨_, h1⟩
  · rintro ⟨t, rfl⟩
    exact ⟨p ^ t, by ring⟩

theorem sqAF_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sqAF (p ^ j) = if Even j then 1 else 0 := by
  have hiff := isSquare_prime_pow_iff hp j
  by_cases h : Even j
  · simp [sqAF_apply, hp.ne_zero, hiff.2 h, h]
  · simp [sqAF_apply, mt hiff.1 h, h]

/-- `ϱ₁(2) = 1`. -/
theorem rho_one_two : rho 1 2 = 1 := by decide

/-- `ϱ₁(2^i) = 0` for `i ≥ 2`, since `ν² + 1 ≢ 0 (mod 4)`. -/
theorem rho_one_two_pow {i : ℕ} (hi : 2 ≤ i) : rho 1 (2 ^ i) = 0 := by
  unfold rho
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ν _ hν
  have h4 : (4 : ℤ) ∣ (ν : ℤ) ^ 2 + 1 := by
    refine dvd_trans ?_ hν
    have : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [this]; push_cast
    exact pow_dvd_pow 2 hi
  obtain ⟨u, hu⟩ := h4
  rcases Int.even_or_odd (ν : ℤ) with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [ht] at hu
    have : (t + t) ^ 2 + 1 = 4 * t ^ 2 + 1 := by ring
    omega
  · rw [ht] at hu
    have : (2 * t + 1) ^ 2 + 1 = 4 * (t ^ 2 + t) + 2 := by ring
    omega

/-- `ϱ₁(p) = 1 + χ₄(p)` for every prime `p`. -/
theorem rho_one_prime {p : ℕ} (hp : p.Prime) : (rho 1 p : ℤ) = 1 + χ₄ (p : ZMod 4) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [rho_one_two]; decide
  · have := Fact.mk hp
    rw [rho_prime hp2, legendreSym.at_neg_one hp2]

/-- `ϱ₁(p^(e+2)) = χ₄(p)^(e+1) (1 + χ₄(p))` for every prime `p`. -/
theorem rho_one_prime_pow_add_two {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (rho 1 (p ^ (e + 2)) : ℤ) = χ₄ (p : ZMod 4) ^ (e + 1) * (1 + χ₄ (p : ZMod 4)) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [rho_one_two_pow (by omega)]
    simp
  · have := Fact.mk hp
    rw [rho_prime_pow_of_not_dvd (m := 1) hp2 (by
        intro h
        have := Int.eq_one_of_dvd_one (by positivity) h
        exact hp.one_lt.ne' (by exact_mod_cast this)) (by omega),
      legendreSym.at_neg_one hp2]
    have hodd : p % 4 = 1 ∨ p % 4 = 3 := by
      have h2 : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
      omega
    rcases hodd with h | h
    · rw [χ₄_nat_one_mod_four h]; simp
    · rw [χ₄_nat_three_mod_four h]; simp

theorem rhoAF_mul_sqAF_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (rhoAF * sqAF) (p ^ e) = (chiAF * (ζ : ArithmeticFunction ℤ)) (p ^ e) := by
  rw [mul_apply_prime_pow _ _ hp, mul_apply_prime_pow _ _ hp]
  have hζ : ∀ i, (ζ : ArithmeticFunction ℤ) (p ^ i) = 1 := fun i => by
    simp [natCoe_apply, zeta_apply, hp.ne_zero]
  have hχ : ∀ i, chiAF (p ^ i) = χ₄ (p : ZMod 4) ^ i := fun i => by
    rw [chiAF_apply, Nat.cast_pow, map_pow]
  simp only [hζ, hχ, mul_one]
  induction e using Nat.twoStepInduction with
  | zero => simp [rhoAF_apply, sqAF_apply, rho_one]
  | one =>
    simp [Finset.sum_range_succ, rhoAF_apply, sqAF_prime_pow hp, rho_one_prime hp]
  | more e ih _ =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (fun i => _ ^ i),
      Finset.sum_range_succ (fun i => _ ^ i), ← ih]
    have hsq : ∀ i ∈ Finset.range (e + 1), rhoAF (p ^ i) * sqAF (p ^ (e + 2 - i)) =
        rhoAF (p ^ i) * sqAF (p ^ (e - i)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show e + 2 - i = (e - i) + 2 by omega, sqAF_prime_pow hp, sqAF_prime_pow hp]
      simp [Nat.even_add]
    rw [Finset.sum_congr rfl hsq, show e + 2 - (e + 1) = 1 by omega, Nat.sub_self,
      sqAF_prime_pow hp, sqAF_prime_pow hp, rhoAF_apply (p ^ (e + 2)),
      rho_one_prime_pow_add_two hp]
    simp
    ring

theorem rhoAF_mul_sqAF : rhoAF * sqAF = chiAF * (ζ : ArithmeticFunction ℤ) :=
  ((isMultiplicative_rhoAF.mul isMultiplicative_sqAF).eq_iff_eq_on_prime_powers _ _
    (isMultiplicative_chiAF.mul isMultiplicative_zeta.natCast)).2
    fun _ e hp => rhoAF_mul_sqAF_prime_pow hp e

theorem sum_rho_eq (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ n.divisors.filter (fun k => k * k ∣ n), (rho 1 (n / (k * k)) : ℤ) =
      (rhoAF * sqAF) n := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => rhoAF a * sqAF b)]
  simp only [sqAF_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun k => k * k) (fun d => Nat.sqrt d)
  · intro k hk
    simp only [Finset.mem_filter, Nat.mem_divisors] at hk ⊢
    exact ⟨⟨hk.2, hn⟩, mul_ne_zero (Nat.pos_of_dvd_of_pos hk.1.1 (Nat.pos_of_ne_zero hn)).ne'
      (Nat.pos_of_dvd_of_pos hk.1.1 (Nat.pos_of_ne_zero hn)).ne', ⟨k, rfl⟩⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨hdn, -⟩, hd0, ⟨s, rfl⟩⟩ := hd
    rw [Nat.sqrt_eq]
    exact ⟨⟨dvd_trans (dvd_mul_right s s) hdn, hn⟩, hdn⟩
  · intro k _
    exact Nat.sqrt_eq k
  · intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨-, -, ⟨s, rfl⟩⟩ := hd
    rw [Nat.sqrt_eq]
  · intro k _
    rfl

/-- **Jacobi's two-square theorem.** `r(n) = 4 ∑_{k ∣ n} χ₄(k)` for `n ≥ 1`. -/
theorem r_eq_four_mul_sum_chi (n : ℕ) (hn : 0 < n) :
    (r n : ℤ) = 4 * ∑ k ∈ n.divisors, χ₄ (k : ZMod 4) := by
  have hχ : ∑ k ∈ n.divisors, χ₄ (k : ZMod 4) = (chiAF * (ζ : ArithmeticFunction ℤ)) n := by
    rw [coe_mul_zeta_apply]; rfl
  rw [hχ, ← rhoAF_mul_sqAF, ← sum_rho_eq n hn.ne', Finset.mul_sum, r_eq_card_allReps,
    card_allReps n hn]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_filter, Nat.mem_divisors] at hk
  have hkk : 0 < k * k := Nat.pos_of_dvd_of_pos hk.2 hn
  rw [card_primReps (Nat.div_pos (Nat.le_of_dvd hn hk.2) hkk)]
  push_cast
  ring

/-- `|χ₄(k)| ≤ 1`. -/
theorem abs_chi_four_le_one (k : ℕ) : |χ₄ (k : ZMod 4)| ≤ 1 := by
  rw [χ₄_nat_eq_if_mod_four]
  split_ifs <;> simp

/-- `r(n) ≤ 4 τ(n)` for `n ≥ 1`. -/
theorem r_le_four_mul_card_divisors (n : ℕ) (hn : 0 < n) : r n ≤ 4 * n.divisors.card := by
  have h := r_eq_four_mul_sum_chi n hn
  have hle : ∑ k ∈ n.divisors, χ₄ (k : ZMod 4) ≤ n.divisors.card := by
    calc ∑ k ∈ n.divisors, χ₄ (k : ZMod 4) ≤ ∑ _k ∈ n.divisors, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro k _
          exact (abs_le.1 (abs_chi_four_le_one k)).2
      _ = n.divisors.card := by simp
  have : (r n : ℤ) ≤ 4 * n.divisors.card := by rw [h]; linarith
  exact_mod_cast this

end Triples
