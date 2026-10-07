import TriplesFinal.Prelim.Beta
import TriplesFinal.Basic.DivisorBound
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries

/-!
# Lemma 5.3(b): the bound for `β`

For a good prime `d` and `ε > 0`,
`∑_{n ≤ N} |β(n)| n^(-1/2-ε) ≤ C(ε) d^ε` for all `N` (`betaWeight_sum_le`).

The function `h(n) = |β(n)| n^(-σ)` is multiplicative, so `∑_{n ≤ N} h(n)` is at most the
product over the primes `p ≤ N` of the local sums `∑_k h(p^k)` (`sum_Icc_le_prod_tsum`, from
Mathlib's Euler products over `s`-factored numbers). The local sums are computed from the values
of `β` at prime powers (`Prelim/Beta.lean`): `1` at `p = 2`, `1 + d^(-σ)` at `p = d`,
`1 + p^(-2σ)` at odd `p ∤ dm`, and at most `2 v_p(m) + 5 ≤ (v_p(m) + 1)³` at odd `p ∣ m`
(since `ϱ(p^i) ≤ 2 p^⌊min(i, v_p(m))/2⌋`). Hence the product is at most
`2 τ(m)³ exp(∑_n n^(-2σ)) ≪_ε d^ε`.

Paper: §5.3, proof of Lemma 5.3(b).
-/

namespace Triples

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- **Euler product upper bound.** For a non-negative multiplicative `h` whose restrictions to
the powers of each prime are summable, `∑_{n ≤ N} h(n) ≤ ∏_{p ≤ N} ∑_k h(p^k)`. -/
theorem sum_Icc_le_prod_tsum {h : ℕ → ℝ} (h0 : ∀ n, 0 ≤ h n) (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → h (m * n) = h m * h n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ h (p ^ k))) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, h n ≤
      ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ∑' k : ℕ, h (p ^ k) := by
  have hsum' : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖h (p ^ k)‖) := fun hp => by
    simpa [Real.norm_of_nonneg (h0 _)] using hsum hp
  obtain ⟨-, hHas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    h1 hmul hsum' (Finset.range (N + 1))
  have hmem : ∀ n ∈ Finset.Icc 1 N, n ∈ Nat.factoredNumbers (Finset.range (N + 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Nat.mem_factoredNumbers_iff_forall_le]
    exact ⟨by omega, fun p hp _ _ => Finset.mem_range.2 (by omega)⟩
  calc ∑ n ∈ Finset.Icc 1 N, h n
      = ∑ n ∈ (Finset.Icc 1 N).subtype (· ∈ Nat.factoredNumbers (Finset.range (N + 1))), h n :=
        (Finset.sum_subtype_of_mem h hmem).symm
    _ ≤ _ := sum_le_hasSum _ (fun i _ => h0 i) hHas

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `h(n) = |β(n)| n^(-σ)`. -/
noncomputable def betaWeight (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  |(P.betaAF d n : ℝ)| * (n : ℝ) ^ (-σ)

theorem betaWeight_nonneg (d : ℕ) (σ : ℝ) (n : ℕ) : 0 ≤ P.betaWeight d σ n :=
  mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem betaWeight_one (d : ℕ) (σ : ℝ) : P.betaWeight d σ 1 = 1 := by
  simp [betaWeight, P.betaAF_one]

theorem betaWeight_mul (d : ℕ) (σ : ℝ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    P.betaWeight d σ (m * n) = P.betaWeight d σ m * P.betaWeight d σ n := by
  simp only [betaWeight, (P.betaAF_isMultiplicative d).map_mul_of_coprime hmn, Int.cast_mul,
    abs_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem betaWeight_prime_pow (d : ℕ) (σ : ℝ) (p k : ℕ) :
    P.betaWeight d σ (p ^ k) = |(P.betaAF d (p ^ k) : ℝ)| * ((p : ℝ) ^ k) ^ (-σ) := by
  rw [betaWeight, Nat.cast_pow]

/-- The Euler factor at `2` is `1`. -/
theorem tsum_betaWeight_two (d : ℕ) (σ : ℝ) : ∑' k : ℕ, P.betaWeight d σ (2 ^ k) = 1 := by
  rw [tsum_eq_single 0]
  · simp [P.betaWeight_one]
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [betaWeight, P.betaAF_two_pow]

theorem summable_betaWeight_two (d : ℕ) (σ : ℝ) : Summable (fun k : ℕ ↦ P.betaWeight d σ (2 ^ k)) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
  simp [betaWeight, P.betaAF_two_pow]

variable {P}

section Good

variable {d : ℕ} (hd : P.IsGood d) (σ : ℝ)
include hd

/-- The Euler factor at `d` is `1 + d^(-σ)`. -/
theorem IsGood.tsum_betaWeight_d :
    ∑' k : ℕ, P.betaWeight d σ (d ^ k) = 1 + (d : ℝ) ^ (-σ) := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, betaWeight, hd.betaAF_d, P.betaAF_one d]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    simp [betaWeight, hd.betaAF_d_pow]

theorem IsGood.summable_betaWeight_d : Summable (fun k : ℕ ↦ P.betaWeight d σ (d ^ k)) := by
  apply summable_of_ne_finset_zero (s := Finset.range 2)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp [betaWeight, hd.betaAF_d_pow]

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d) (hpm : ¬ (p : ℤ) ∣ P.m d)
include hp hp2 hpd hpm

/-- The Euler factor at an odd prime `p ∤ dm` is `1 + p^(-2σ)`. -/
theorem IsGood.tsum_betaWeight_of_not_dvd :
    ∑' k : ℕ, P.betaWeight d σ (p ^ k) = 1 + ((p : ℝ) ^ 2) ^ (-σ) := by
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, betaWeight, P.betaAF_one d,
      hd.betaAF_prime_of_not_dvd hp hp2 hpd hpm, hd.betaAF_prime_sq_of_not_dvd hp hp2 hpd hpm]
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp [betaWeight, hd.betaAF_prime_pow_of_not_dvd hp hp2 hpd hpm]

theorem IsGood.summable_betaWeight_of_not_dvd :
    Summable (fun k : ℕ ↦ P.betaWeight d σ (p ^ k)) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  simp [betaWeight, hd.betaAF_prime_pow_of_not_dvd hp hp2 hpd hpm]

end Good

end PatternData

/-- `∑_{k < K} r^(k - α) ≤ α + 1 + r/(1 - r)` for `0 ≤ r < 1` (truncated subtraction). -/
theorem sum_range_pow_tsub_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (α K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ (k - α) ≤ (α + 1 : ℝ) + r / (1 - r) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun k => k ≤ α)]
  have h1 : ∑ k ∈ (Finset.range K).filter (fun k => k ≤ α), r ^ (k - α) ≤ (α + 1 : ℝ) := by
    have hsub : (Finset.range K).filter (fun k => k ≤ α) ⊆ Finset.range (α + 1) := by
      intro k hk; simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega
    calc ∑ k ∈ (Finset.range K).filter (fun k => k ≤ α), r ^ (k - α)
        = ∑ k ∈ (Finset.range K).filter (fun k => k ≤ α), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_filter] at hk
          rw [show k - α = 0 by omega, pow_zero]
      _ = (((Finset.range K).filter (fun k => k ≤ α)).card : ℝ) := by simp
      _ ≤ ((Finset.range (α + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (α + 1 : ℝ) := by simp
  have h2 : ∑ k ∈ (Finset.range K).filter (fun k => ¬ k ≤ α), r ^ (k - α) ≤ r / (1 - r) := by
    have hset : (Finset.range K).filter (fun k => ¬ k ≤ α) = Finset.Ico (α + 1) K := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j : ℕ, r ^ (α + 1 + j - α) = r * r ^ j := by
      intro j; rw [show α + 1 + j - α = j + 1 by omega, pow_succ]; ring
    simp_rw [hterm, ← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.range (K - (α + 1)), r ^ j ≤ (1 - r)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hr0 hr1]
      exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hr0 j) (summable_geometric_of_lt_one hr0 hr1)
    calc r * ∑ j ∈ Finset.range (K - (α + 1)), r ^ j ≤ r * (1 - r)⁻¹ := by gcongr
      _ = r / (1 - r) := by rw [div_eq_mul_inv]
  linarith

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

section DvdM

variable {d : ℕ} (hd : P.IsGood d) {σ : ℝ} (hσ : 1 / 2 ≤ σ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hpm : (p : ℤ) ∣ P.m d)
include hd hσ hp hp2 hpm

/-- For an odd prime `p ∣ m` with `α = v_p(m)`: `|β(p^k)| p^(-kσ) ≤ 2 (1/√p)^(k - α)`. -/
theorem IsGood.betaWeight_le_of_dvd (k : ℕ) :
    P.betaWeight d σ (p ^ k) ≤ 2 * (1 / Real.sqrt p) ^ (k - padicValInt p (P.m d)) := by
  set α := padicValInt p (P.m d) with hα
  have hm0 : P.m d ≠ 0 := (P.m_pos hd.d₁_lt).ne'
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set s := Real.sqrt p with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hp0
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hp1
  have hss : s ^ 2 = p := Real.sq_sqrt hp0.le
  -- `(p^k)^(-σ) ≤ 1/s^k`
  have hpow : ((p : ℝ) ^ k) ^ (-σ) ≤ 1 / s ^ k := by
    have hpk1 : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ hp1
    calc ((p : ℝ) ^ k) ^ (-σ) ≤ ((p : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hpk1 (by linarith)
      _ = 1 / s ^ k := by
          rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
          congr 1
          rw [← hss, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq (by positivity)]
  -- `|β(p^k)| ≤ 2 p^⌊min(k, α)/2⌋`
  have hβ : |(P.betaAF d (p ^ k) : ℝ)| ≤ 2 * (p : ℝ) ^ (min k α / 2) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [P.betaAF_one d]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hd.betaAF_prime_pow_of_dvd hp hp2 hpm j]
    have hχ : |(chiAF p : ℝ)| = 1 := by
      have h2 := chiAF_sq_of_odd (Nat.odd_iff.1 (hp.odd_of_ne_two hp2))
      have : ((chiAF p : ℝ)) ^ 2 = 1 := by exact_mod_cast h2
      have h3 := abs_mul_abs_self (chiAF p : ℝ)
      nlinarith [abs_nonneg (chiAF p : ℝ), sq_abs (chiAF p : ℝ)]
    push_cast
    rw [abs_mul, abs_pow, hχ, one_pow, one_mul]
    have h1 := rho_prime_pow_le_nat hm0 hp hp2 (j + 1)
    have h0 := rho_prime_pow_le_nat hm0 hp hp2 j
    have hmono : (p : ℝ) ^ (min j α / 2) ≤ (p : ℝ) ^ (min (j + 1) α / 2) :=
      pow_le_pow_right₀ hp1 (Nat.div_le_div_right (by omega))
    have h1' : (rho (P.m d) (p ^ (j + 1)) : ℝ) ≤ 2 * (p : ℝ) ^ (min (j + 1) α / 2) := by
      exact_mod_cast h1
    have h0' : (rho (P.m d) (p ^ j) : ℝ) ≤ 2 * (p : ℝ) ^ (min (j + 1) α / 2) := by
      have : (rho (P.m d) (p ^ j) : ℝ) ≤ 2 * (p : ℝ) ^ (min j α / 2) := by exact_mod_cast h0
      linarith
    rw [abs_sub_le_iff]
    constructor <;> linarith [(Nat.cast_nonneg (rho (P.m d) (p ^ (j + 1))) : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg (rho (P.m d) (p ^ j)) : (0 : ℝ) ≤ _)]
  -- combine
  have hsplit : s ^ k = s ^ (min k α) * s ^ (k - α) := by
    rw [← pow_add]; congr 1; omega
  have he : (p : ℝ) ^ (min k α / 2) ≤ s ^ (min k α) := by
    rw [← hss, ← pow_mul]
    exact pow_le_pow_right₀ hs1 (by omega)
  rw [betaWeight_prime_pow]
  calc |(P.betaAF d (p ^ k) : ℝ)| * ((p : ℝ) ^ k) ^ (-σ)
      ≤ (2 * s ^ (min k α)) * (1 / s ^ k) := by
        apply mul_le_mul (hβ.trans (by gcongr)) hpow (Real.rpow_nonneg (by positivity) _)
          (by positivity)
    _ = 2 * (1 / s) ^ (k - α) := by
        rw [hsplit, one_div_pow]
        field_simp

/-- The Euler factor at an odd prime `p ∣ m` is at most `2 v_p(m) + 5`. -/
theorem IsGood.sum_range_betaWeight_le_of_dvd (K : ℕ) :
    ∑ k ∈ Finset.range K, P.betaWeight d σ (p ^ k) ≤ 2 * padicValInt p (P.m d) + 5 := by
  have hp3 : (3 : ℝ) ≤ p := by
    have := hp.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  set r := 1 / Real.sqrt p with hr
  have hsq : (5 / 3 : ℝ) ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hr0 : 0 ≤ r := by positivity
  have hr35 : r ≤ 3 / 5 := by
    rw [hr, div_le_iff₀ (by linarith)]
    linarith
  have hr1 : r < 1 := by linarith
  calc ∑ k ∈ Finset.range K, P.betaWeight d σ (p ^ k)
      ≤ ∑ k ∈ Finset.range K, 2 * r ^ (k - padicValInt p (P.m d)) :=
        Finset.sum_le_sum fun k _ => hd.betaWeight_le_of_dvd hσ hp hp2 hpm k
    _ = 2 * ∑ k ∈ Finset.range K, r ^ (k - padicValInt p (P.m d)) := by rw [Finset.mul_sum]
    _ ≤ 2 * ((padicValInt p (P.m d) + 1 : ℝ) + r / (1 - r)) := by
        gcongr; exact sum_range_pow_tsub_le hr0 hr1 _ _
    _ ≤ 2 * padicValInt p (P.m d) + 5 := by
        have : r / (1 - r) ≤ 3 / 2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith

theorem IsGood.summable_betaWeight_of_dvd : Summable (fun k : ℕ ↦ P.betaWeight d σ (p ^ k)) :=
  summable_of_sum_range_le (fun _ => P.betaWeight_nonneg d σ _)
    (hd.sum_range_betaWeight_le_of_dvd hσ hp hp2 hpm)

theorem IsGood.tsum_betaWeight_le_of_dvd :
    ∑' k : ℕ, P.betaWeight d σ (p ^ k) ≤ 2 * padicValInt p (P.m d) + 5 :=
  Real.tsum_le_of_sum_range_le (fun _ => P.betaWeight_nonneg d σ _)
    (hd.sum_range_betaWeight_le_of_dvd hσ hp hp2 hpm)

end DvdM

/-- The local bound `B_p` for the Euler factor of `|β(n)| n^(-σ)` at `p`. -/
noncomputable def betaLocalBound (d : ℕ) (M : ℕ) (σ : ℝ) (p : ℕ) : ℝ :=
  (if p = d then 2 else 1) * (if p ∣ M then ((M.factorization p : ℝ) + 1) ^ 3 else 1) *
    Real.exp (((p : ℝ) ^ 2) ^ (-σ))

theorem betaLocalBound_ge (d M : ℕ) (σ : ℝ) (p : ℕ) :
    1 ≤ (if p = d then (2 : ℝ) else 1) ∧
      1 ≤ (if p ∣ M then ((M.factorization p : ℝ) + 1) ^ 3 else 1) ∧
        1 ≤ Real.exp (((p : ℝ) ^ 2) ^ (-σ)) := by
  refine ⟨by split_ifs <;> norm_num, by split_ifs <;> [exact one_le_pow₀ (by linarith [(Nat.cast_nonneg (M.factorization p) : (0:ℝ) ≤ _)]); exact le_rfl], ?_⟩
  exact Real.one_le_exp (Real.rpow_nonneg (by positivity) _)

/-- Each Euler factor is at most `B_p`. -/
theorem IsGood.tsum_betaWeight_le {d : ℕ} (hd : P.IsGood d) {σ : ℝ} (hσ : 1 / 2 ≤ σ) {p : ℕ}
    (hp : p.Prime) :
    ∑' k : ℕ, P.betaWeight d σ (p ^ k) ≤ betaLocalBound d (P.m d).natAbs σ p := by
  obtain ⟨hA, hB, hC⟩ := betaLocalBound_ge d (P.m d).natAbs σ p
  have hA0 : (0 : ℝ) ≤ (if p = d then (2 : ℝ) else 1) := by linarith
  have hB0 : (0 : ℝ) ≤ (if p ∣ (P.m d).natAbs then (((P.m d).natAbs.factorization p : ℝ) + 1) ^ 3 else 1) := by linarith
  unfold betaLocalBound
  by_cases h2 : p = 2
  · subst h2
    rw [P.tsum_betaWeight_two]
    nlinarith [mul_le_mul hA hB zero_le_one hA0]
  by_cases hpd : p = d
  · subst hpd
    rw [hd.tsum_betaWeight_d]
    have hd1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have : (p : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)
    rw [ite_eq_left rfl]
    nlinarith [mul_le_mul (le_refl (2 : ℝ)) hB zero_le_one (by norm_num : (0:ℝ) ≤ 2)]
  by_cases hpm : (p : ℤ) ∣ P.m d
  · have hpM : p ∣ (P.m d).natAbs := Int.natCast_dvd.1 hpm
    have hE := hd.tsum_betaWeight_le_of_dvd hσ hp h2 hpm
    have hα : padicValInt p (P.m d) = (P.m d).natAbs.factorization p := by
      rw [padicValInt, Nat.factorization_def _ hp]
    have hM0 : (P.m d).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (P.m_pos hd.d₁_lt).ne'
    have hα1 : 1 ≤ (P.m d).natAbs.factorization p := hp.factorization_pos_of_dvd hM0 hpM
    rw [hα] at hE
    rw [ite_eq_left hpM]
    set α : ℝ := ((P.m d).natAbs.factorization p : ℝ) with hαR
    have hα1R : (1 : ℝ) ≤ α := by rw [hαR]; exact_mod_cast hα1
    have hcube : 2 * α + 5 ≤ (α + 1) ^ 3 := by
      have ht : 0 ≤ α - 1 := by linarith
      nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
    have hAC : 1 ≤ (if p = d then (2 : ℝ) else 1) * Real.exp (((p : ℝ) ^ 2) ^ (-σ)) := by
      nlinarith
    calc ∑' k : ℕ, P.betaWeight d σ (p ^ k) ≤ (α + 1) ^ 3 := by linarith
      _ ≤ (if p = d then (2 : ℝ) else 1) * (α + 1) ^ 3 * Real.exp (((p : ℝ) ^ 2) ^ (-σ)) := by
        have h0 : 0 ≤ (α + 1) ^ 3 := by positivity
        nlinarith
  · have hE := hd.tsum_betaWeight_of_not_dvd σ hp h2 hpd hpm
    rw [hE]
    have := Real.add_one_le_exp (((p : ℝ) ^ 2) ^ (-σ))
    nlinarith [mul_le_mul hA hB zero_le_one hA0]

theorem IsGood.summable_betaWeight {d : ℕ} (hd : P.IsGood d) {σ : ℝ} (hσ : 1 / 2 ≤ σ) {p : ℕ}
    (hp : p.Prime) : Summable (fun k : ℕ ↦ P.betaWeight d σ (p ^ k)) := by
  by_cases h2 : p = 2
  · subst h2; exact P.summable_betaWeight_two d σ
  by_cases hpd : p = d
  · subst hpd; exact hd.summable_betaWeight_d σ
  by_cases hpm : (p : ℤ) ∣ P.m d
  · exact hd.summable_betaWeight_of_dvd hσ hp h2 hpm
  · exact hd.summable_betaWeight_of_not_dvd σ hp h2 hpd hpm

variable (P) in
/-- **The bound for `β`** (proof of Lemma 5.3(b)): for `ε > 0`,
`∑_{n ≤ N} |β(n)| n^(-1/2-ε) ≪_ε d^ε`, uniformly in good primes `d` and in `N`. -/
theorem betaWeight_sum_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, P.IsGood d → ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, P.betaWeight d (1 / 2 + ε) n ≤ C * (d : ℝ) ^ ε := by
  set σ : ℝ := 1 / 2 + ε with hσdef
  have hσ : 1 / 2 ≤ σ := by linarith
  have hZs : Summable (fun n : ℕ => ((n : ℝ) ^ 2) ^ (-σ)) := by
    have : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ))) := Real.summable_nat_rpow.2 (by linarith)
    refine this.congr (fun n => ?_)
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
    congr 1; push_cast; ring
  set Z := ∑' n : ℕ, ((n : ℝ) ^ 2) ^ (-σ) with hZ
  obtain ⟨Cτ, hCτ, hτ⟩ := card_divisors_le_rpow (ε := ε / 6) (by positivity)
  refine ⟨2 * Cτ ^ 3 * (2 : ℝ) ^ (ε / 2) * Real.exp Z, by positivity, fun d hd N => ?_⟩
  set M := (P.m d).natAbs with hM
  have hM0 : M ≠ 0 := Int.natAbs_ne_zero.2 (P.m_pos hd.d₁_lt).ne'
  set T := (Finset.range (N + 1)).filter Nat.Prime with hT
  have h1 := sum_Icc_le_prod_tsum (P.betaWeight_nonneg d σ) (P.betaWeight_one d σ)
    (P.betaWeight_mul d σ) (fun hp => hd.summable_betaWeight hσ hp) N
  rw [← hT] at h1
  have h2 : ∏ p ∈ T, ∑' k : ℕ, P.betaWeight d σ (p ^ k) ≤ ∏ p ∈ T, betaLocalBound d M σ p := by
    apply Finset.prod_le_prod₀
    · intro p _; exact tsum_nonneg (fun k => P.betaWeight_nonneg d σ _)
    · intro p hp
      exact hd.tsum_betaWeight_le hσ (Finset.mem_filter.1 hp).2
  have h3 : ∏ p ∈ T, betaLocalBound d M σ p =
      (∏ p ∈ T, (if p = d then (2 : ℝ) else 1)) *
        (∏ p ∈ T, (if p ∣ M then ((M.factorization p : ℝ) + 1) ^ 3 else 1)) *
          ∏ p ∈ T, Real.exp (((p : ℝ) ^ 2) ^ (-σ)) := by
    unfold betaLocalBound
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hA : ∏ p ∈ T, (if p = d then (2 : ℝ) else 1) ≤ 2 := by
    rw [Finset.prod_ite_eq']
    split_ifs <;> norm_num
  have hB : ∏ p ∈ T, (if p ∣ M then ((M.factorization p : ℝ) + 1) ^ 3 else 1) ≤
      (M.divisors.card : ℝ) ^ 3 := by
    rw [← Finset.prod_filter, Nat.card_divisors hM0, Nat.cast_prod, ← Finset.prod_pow]
    push_cast
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      simp only [Finset.mem_filter, hT, Finset.mem_range] at hp
      exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hM0⟩
    · intro p _; positivity
    · intro p _ _
      exact one_le_pow₀ (by linarith [(Nat.cast_nonneg (M.factorization p) : (0:ℝ) ≤ _)])
  have hC : ∏ p ∈ T, Real.exp (((p : ℝ) ^ 2) ^ (-σ)) ≤ Real.exp Z := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    exact hZs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (by positivity) _)
  -- the divisor bound
  have hτM : (M.divisors.card : ℝ) ^ 3 ≤ Cτ ^ 3 * (2 : ℝ) ^ (ε / 2) * (d : ℝ) ^ ε := by
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 hM0
    have h := hτ M hM1
    have hMle : (M : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
      have hmb := (P.m_bounds hd.d₁_lt).2
      have hMm : ((P.m d).natAbs : ℤ) = P.m d := Int.natAbs_of_nonneg (P.m_pos hd.d₁_lt).le
      have : (M : ℤ) ≤ 2 * (d : ℤ) ^ 2 := by rw [hM, hMm]; exact hmb
      exact_mod_cast this
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc (M.divisors.card : ℝ) ^ 3 ≤ (Cτ * (M : ℝ) ^ (ε / 6)) ^ 3 := by
          gcongr
      _ = Cτ ^ 3 * (M : ℝ) ^ (ε / 2) := by
          rw [mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (ε / 6)), ← Real.rpow_mul hMpos.le]
          congr 2; push_cast; ring
      _ ≤ Cτ ^ 3 * (2 * (d : ℝ) ^ 2) ^ (ε / 2) := by
          gcongr
      _ = Cτ ^ 3 * (2 : ℝ) ^ (ε / 2) * (d : ℝ) ^ ε := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast ((d : ℝ)) 2,
            ← Real.rpow_mul hd0, show ((2 : ℕ) : ℝ) * (ε / 2) = ε by push_cast; ring]
          ring
  have hBnn : 0 ≤ ∏ p ∈ T, (if p ∣ M then ((M.factorization p : ℝ) + 1) ^ 3 else 1) :=
    Finset.prod_nonneg (fun p _ => by split_ifs <;> positivity)
  have hAnn : 0 ≤ ∏ p ∈ T, (if p = d then (2 : ℝ) else 1) :=
    Finset.prod_nonneg (fun p _ => by split_ifs <;> norm_num)
  have hCnn : 0 ≤ ∏ p ∈ T, Real.exp (((p : ℝ) ^ 2) ^ (-σ)) :=
    Finset.prod_nonneg (fun p _ => (Real.exp_pos _).le)
  calc ∑ n ∈ Finset.Icc 1 N, P.betaWeight d σ n
      ≤ ∏ p ∈ T, betaLocalBound d M σ p := h1.trans h2
    _ ≤ 2 * (Cτ ^ 3 * (2 : ℝ) ^ (ε / 2) * (d : ℝ) ^ ε) * Real.exp Z := by
        rw [h3]
        exact mul_le_mul (mul_le_mul hA (hB.trans hτM) hBnn (by norm_num)) hC hCnn
          (by positivity)
    _ = 2 * Cτ ^ 3 * (2 : ℝ) ^ (ε / 2) * Real.exp Z * (d : ℝ) ^ ε := by ring

end PatternData

end Triples
