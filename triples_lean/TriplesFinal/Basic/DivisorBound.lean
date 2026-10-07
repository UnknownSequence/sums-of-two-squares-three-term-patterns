import TriplesFinal.Basic.Jacobi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The divisor bound

`τ(n) ≪_ε n^ε`, and hence `r(n) ≪_ε n^ε` (by `r(n) ≤ 4τ(n)`).

The divisor bound is classical and elementary (Hardy–Wright, Theorem 315). It is proved here by
bounding each local factor of `τ(n) n^(-ε)` (`local_factor_le`); it is not an assumption.

Paper: used in Proposition 4.2, Lemma 5.2(b) and Lemma 8.4.
-/

namespace Triples

/-- The local factor at a prime: `a + 1 ≤ M p^(aε)` with `M = 1/(ε log 2) + 1`. -/
theorem local_factor_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    ((a : ℝ) + 1) ≤ (1 / (ε * Real.log 2) + 1) * (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hεl : 0 < ε * Real.log 2 := by positivity
  have h2 : 1 + (a : ℝ) * ε * Real.log 2 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * ((a : ℝ) * ε))
    nlinarith [this]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := Real.one_le_rpow (by norm_num) (by positivity)
  have h3 : (a : ℝ) ≤ (2 : ℝ) ^ ((a : ℝ) * ε) / (ε * Real.log 2) := by
    rw [le_div_iff₀ hεl]; nlinarith
  have h4 : (a : ℝ) + 1 ≤ (1 / (ε * Real.log 2) + 1) * (2 : ℝ) ^ ((a : ℝ) * ε) := by
    have e : (2 : ℝ) ^ ((a : ℝ) * ε) / (ε * Real.log 2) =
        1 / (ε * Real.log 2) * (2 : ℝ) ^ ((a : ℝ) * ε) := by ring
    nlinarith
  have hp2 : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ (p : ℝ) ^ ((a : ℝ) * ε) :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) (by positivity)
  calc (a : ℝ) + 1 ≤ (1 / (ε * Real.log 2) + 1) * (2 : ℝ) ^ ((a : ℝ) * ε) := h4
    _ ≤ (1 / (ε * Real.log 2) + 1) * (p : ℝ) ^ ((a : ℝ) * ε) := by gcongr

/-- The local factor at a large prime `p ≥ 2^(1/ε)`: `a + 1 ≤ p^(aε)`. -/
theorem local_factor_le_large {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : (2 : ℝ) ^ (1 / ε) ≤ p)
    (a : ℕ) : ((a : ℝ) + 1) ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans (by positivity) hp
  have hp' : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hp hε.le
  have ha : (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := by
    have : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    exact_mod_cast this
  calc (a : ℝ) + 1 ≤ (2 : ℝ) ^ a := ha
    _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) hp' a
    _ = (p : ℝ) ^ ((a : ℝ) * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]; ring_nf

/-- **The divisor bound.** For every `ε > 0` there is `C` with `τ(n) ≤ C n^ε` for all `n ≥ 1`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  set M : ℝ := 1 / (ε * Real.log 2) + 1 with hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : 1 ≤ M := by
    have : 0 < 1 / (ε * Real.log 2) := by positivity
    linarith
  set N₀ : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hN₀
  refine ⟨M ^ N₀, by positivity, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  -- `n^ε = ∏_p p^(a_p ε)`
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  -- the weights `c_p = M` (small primes) or `1` (large primes)
  set c : ℕ → ℝ := fun p => if (p : ℝ) < (2 : ℝ) ^ (1 / ε) then M else 1 with hc
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      c p * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    simp only [hc]
    split_ifs with h
    · exact local_factor_le hε hp2 _
    · rw [one_mul]; exact local_factor_le_large hε (not_lt.1 h) _
  have hcprod : ∏ p ∈ n.primeFactors, c p ≤ M ^ N₀ := by
    simp only [hc]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hM1
    -- the small primes lie in `range N₀`
    calc (n.primeFactors.filter (fun p : ℕ => (p : ℝ) < (2 : ℝ) ^ (1 / ε))).card
        ≤ (Finset.range N₀).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Finset.mem_range]
          have : (p : ℝ) < N₀ := lt_of_lt_of_le hp.2 (Nat.le_ceil _)
          exact_mod_cast this
      _ = N₀ := Finset.card_range N₀
  rw [Nat.card_divisors hn0, hn']
  push_cast
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (c p * (p : ℝ) ^ ((n.factorization p : ℝ) * ε)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, c p) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_mul_distrib
    _ ≤ M ^ N₀ * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
        gcongr

/-- `r(n) ≪_ε n^ε`. -/
theorem r_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (r n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := card_divisors_le_rpow hε
  refine ⟨4 * C, by positivity, fun n hn => ?_⟩
  have h1 : (r n : ℝ) ≤ 4 * n.divisors.card := by
    exact_mod_cast r_le_four_mul_card_divisors n hn
  calc (r n : ℝ) ≤ 4 * n.divisors.card := h1
    _ ≤ 4 * (C * (n : ℝ) ^ ε) := by gcongr; exact h n hn
    _ = 4 * C * (n : ℝ) ^ ε := by ring

end Triples
