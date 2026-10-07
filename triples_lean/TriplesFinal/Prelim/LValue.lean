import TriplesFinal.Assumptions.Assumptions
import TriplesFinal.Basic.DivisorBound
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Values of real Dirichlet `L`-functions at `s = 1`

Inputs for Lemma 5.3(d):

* `φ(n)/n = ∏_{p ∣ n} (1 - 1/p) ≥ 1/τ(n) ≫_ε n^(-ε)` (`totient_div_ge_rpow`);
* for a non-trivial quadratic Dirichlet character `χ`, `L(1, χ)` is a positive real number
  (`LFunction_one_eq_norm`): `L(x, χ) = exp(∑ χ(n) Λ(n)/(n^x log n)) > 0` for real `x > 1`,
  `L(·, χ)` is continuous, and `L(1, χ) ≠ 0`;
* Siegel's theorem (stated in `Assumptions` for *primitive* characters) extends to all real
  non-principal characters modulo `N`, with the loss `φ(N)/N` coming from the Euler factors at
  the primes dividing `N` (`norm_LFunction_one_ge`).

Paper: §5.3, proof of Lemma 5.3(d).
-/

namespace Triples

open Complex

/-- `φ(n)/n = ∏_{p ∣ n} (1 - 1/p)`. -/
theorem totient_div_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' : (((n.totient : ℚ)) : ℝ) = ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [h', mul_div_cancel_left₀ _ (by exact_mod_cast hn)]

/-- `2^ω(n) ≤ τ(n)`. -/
theorem two_pow_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors hn]
  apply Finset.pow_card_le_prod
  intro p hp
  have : n.factorization p ≠ 0 := by
    rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
  omega

/-- `φ(n)/n ≥ 1/τ(n)`. -/
theorem inv_card_divisors_le_totient_div (n : ℕ) (hn : n ≠ 0) :
    (1 : ℝ) / n.divisors.card ≤ (n.totient : ℝ) / n := by
  rw [totient_div_eq_prod n hn]
  have h2 : ((2 : ℝ) ^ n.primeFactors.card) ≤ n.divisors.card := by
    exact_mod_cast two_pow_card_primeFactors_le n hn
  calc (1 : ℝ) / n.divisors.card ≤ 1 / (2 : ℝ) ^ n.primeFactors.card := by
        apply one_div_le_one_div_of_le (by positivity) h2
    _ = ∏ _p ∈ n.primeFactors, (1 / 2 : ℝ) := by
        rw [Finset.prod_const, one_div, one_div, inv_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
        apply Finset.prod_le_prod₀
        · intro _ _; norm_num
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
            rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
          linarith

/-- `φ(n)/n ≫_ε n^(-ε)`. -/
theorem totient_div_ge_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ (-ε) ≤ (n.totient : ℝ) / n := by
  obtain ⟨C, hC, h⟩ := card_divisors_le_rpow hε
  refine ⟨1 / C, by positivity, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hτpos : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.2 ⟨1, Nat.one_mem_divisors.2 hn0⟩
  refine le_trans ?_ (inv_card_divisors_le_totient_div n hn0)
  rw [Real.rpow_neg hnpos.le]
  have hpow : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
  calc 1 / C * ((n : ℝ) ^ ε)⁻¹ = 1 / (C * (n : ℝ) ^ ε) := by field_simp
    _ ≤ 1 / (n.divisors.card : ℝ) := one_div_le_one_div_of_le hτpos (h n hn)

/-- For a quadratic Dirichlet character `χ` and real `x > 1`, `L(x, χ)` is a positive real
number (by the Euler product in the form `L(x, χ) = exp(∑ χ(n) Λ(n) / (n^x log n))`). -/
theorem LFunction_real_pos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) :
    ∃ r : ℝ, 0 < r ∧ DirichletCharacter.LFunction χ x = r := by
  have hxre : 1 < (x : ℂ).re := by simpa using hx
  rw [DirichletCharacter.LFunction_eq_LSeries χ hxre,
    ← DirichletCharacter.LSeries_eq_exp_LSeries χ hxre]
  have hreal : ∀ n : ℕ, χ n = ((χ n).re : ℂ) := by
    intro n
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ (n : ZMod N) with h | h | h <;> simp [h]
  set r : ℕ → ℝ := fun n ↦ if n = 0 then 0 else
    (χ n).re * ArithmeticFunction.vonMangoldt n / Real.log n / (n : ℝ) ^ x with hr
  refine ⟨Real.exp (∑' n, r n), Real.exp_pos _, ?_⟩
  rw [Complex.ofReal_exp, Complex.ofReal_tsum]
  congr 1
  unfold LSeries
  congr 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [r]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [r, hn, ite_false]
    rw [hreal n]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_re, Complex.ofReal_natCast]

/-- For a non-trivial quadratic Dirichlet character, `L(1, χ)` is a positive real number. -/
theorem LFunction_one_eq_norm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1)
    (hne : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = (‖DirichletCharacter.LFunction χ 1‖ : ℂ) := by
  set z := DirichletCharacter.LFunction χ 1 with hz
  have hcont : Continuous fun t : ℝ ↦ DirichletCharacter.LFunction χ (t : ℂ) :=
    (DirichletCharacter.differentiable_LFunction hne).continuous.comp Complex.continuous_ofReal
  set S : Set ℂ := {w | w.im = 0 ∧ 0 ≤ w.re} with hS_def
  have hS : IsClosed S :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hlim : Filter.Tendsto (fun t : ℝ ↦ DirichletCharacter.LFunction χ (t : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds z) := by
    have := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa [hz] using this
  have hmem : z ∈ S := by
    apply hS.mem_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨r, hr, hr'⟩ := LFunction_real_pos hχ (x := t) ht
    rw [hr']
    simp [S, hr.le]
  have h1 : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hmem.1])
  have h2 : ‖z‖ = z.re := by
    conv_lhs => rw [h1]
    rw [Complex.norm_real, Real.norm_of_nonneg hmem.2]
  rw [h2]
  exact h1

/-- **Siegel's theorem for imprimitive characters**: `|L(1, χ)| ≫_ε N^(-ε) φ(N)/N` for every
real non-principal Dirichlet character `χ` modulo `N`. (Apply Siegel's theorem to the primitive
character inducing `χ`, and compare the Euler factors at the primes dividing `N`.) -/
theorem norm_LFunction_one_ge (hS : SiegelTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      c * (N : ℝ) ^ (-ε) * ((N.totient : ℝ) / N) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  obtain ⟨c, hc, hsieg⟩ := hS ε hε
  refine ⟨c, hc, fun N _ χ hsq hne => ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ := χ.primitiveCharacter with hψ
  have hψχ : DirichletCharacter.changeLevel χ.conductor_dvd_level ψ = χ :=
    χ.changeLevel_primitiveCharacter
  have hψne : ψ ≠ 1 := by
    intro h; apply hne; rw [← hψχ, h, map_one]
  have hψsq : ψ ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    rw [map_pow, hψχ, hsq, map_one]
  have hL := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level ψ (s := 1)
    (Or.inl hψne)
  rw [hψχ] at hL
  rw [hL, norm_mul, norm_prod]
  have hsiegel := hsieg χ.conductor ψ χ.primitiveCharacter_isPrimitive hψsq hψne
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqN : (χ.conductor : ℝ) ≤ N := by
    exact_mod_cast Nat.le_of_dvd hN0 χ.conductor_dvd_level
  have hq1 : (0 : ℝ) < χ.conductor := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hpow : (N : ℝ) ^ (-ε) ≤ (χ.conductor : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hq1 hqN (by linarith)
  have hprod : (N.totient : ℝ) / N ≤
      ∏ p ∈ N.primeFactors, ‖1 - ψ p * (p : ℂ) ^ (-(1 : ℂ))‖ := by
    rw [totient_div_eq_prod N (NeZero.ne N)]
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      linarith
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have hnorm : ‖ψ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ (p : ℝ)⁻¹ := by
        rw [Complex.cpow_neg_one, norm_mul, norm_inv, Complex.norm_natCast]
        calc ‖ψ p‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ := by
              gcongr; exact DirichletCharacter.norm_le_one ψ _
          _ = (p : ℝ)⁻¹ := one_mul _
      have := norm_sub_norm_le (1 : ℂ) (ψ p * (p : ℂ) ^ (-(1 : ℂ)))
      rw [norm_one] at this
      linarith
  have hφ0 : 0 ≤ (N.totient : ℝ) / N := by positivity
  calc c * (N : ℝ) ^ (-ε) * ((N.totient : ℝ) / N)
      ≤ c * (χ.conductor : ℝ) ^ (-ε) * ((N.totient : ℝ) / N) := by gcongr
    _ ≤ ‖DirichletCharacter.LFunction ψ 1‖ *
          ∏ p ∈ N.primeFactors, ‖1 - ψ p * (p : ℂ) ^ (-(1 : ℂ))‖ :=
        mul_le_mul hsiegel hprod hφ0 (norm_nonneg _)

end Triples
