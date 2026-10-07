import TriplesFinal.GoodPrimes.Reduction
import TriplesFinal.Prelim.Hyperbola
import TriplesFinal.Prelim.LdLower
import TriplesFinal.TypeI.Theorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Set-up for the asymptotic formula (§7)

* `Cutoff`: the smooth weight `F : ℝ → [0, 1]`, supported in `[1/2, 1]` and not identically zero,
  with `c_F = ∫_0^1 F(t) t^(-1/2) dt > 0` (§4).
* `T(t) = 2^(v-2)(Et² + H)/d` for real `t`; `Φ_y(t) = F(T(t)/x) W(2^((v-2)/2) y / √T(t))`.
* The main term `ℳ_d = 8 ∑_{k odd} χ(k) ϱ(dk)/(dk) ∫ Φ_k` and the error `ℰ_d = Σ_d(x) - ℳ_d`
  (equation (7.4)).
* Equation (7.3): `Σ_d(x) = 8 ∑_{k odd} χ(k) ∑_{dk ∣ Eℓ² + H} Φ_k(ℓ)` (from Lemma 5.1).

Paper: §4 (the weight `F`) and §7.1.
-/

namespace Triples

open scoped ContDiff

/-- A smooth weight `F : ℝ → [0, 1]` supported in `[1/2, 1]` and not identically zero. -/
structure Cutoff where
  /-- the weight -/
  F : ℝ → ℝ
  smooth : ContDiff ℝ ∞ F
  nonneg : ∀ t, 0 ≤ F t
  le_one : ∀ t, F t ≤ 1
  support : ∀ t, F t ≠ 0 → 1 / 2 ≤ t ∧ t ≤ 1
  ne_zero : ∃ t, F t ≠ 0

/-- `c_F = ∫_0^1 F(t) t^(-1/2) dt`. -/
noncomputable def Cutoff.cF (F : Cutoff) : ℝ := ∫ t in (0 : ℝ)..1, F.F t * t ^ (-(1 : ℝ) / 2)

/-- `c_F > 0`. -/
theorem Cutoff.cF_pos (F : Cutoff) : 0 < F.cF := by
  obtain ⟨t₀, ht₀⟩ := F.ne_zero
  have hpos : 0 < F.F t₀ := lt_of_le_of_ne (F.nonneg t₀) (Ne.symm ht₀)
  obtain ⟨h12, h1⟩ := F.support t₀ ht₀
  have hcont : Continuous F.F := F.smooth.continuous
  -- replace `t^(-1/2)` by `max(t, 1/4)^(-1/2)`, which does not change the integral
  set g : ℝ → ℝ := fun t => F.F t * (max t (1 / 4)) ^ (-(1 : ℝ) / 2) with hg
  have hmax : ∀ t : ℝ, 0 < max t (1 / 4) := fun t => lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hgcont : Continuous g := by
    apply hcont.mul
    exact (continuous_id.max continuous_const).rpow_const (fun t => Or.inl (hmax t).ne')
  have heq : Set.EqOn (fun t => F.F t * t ^ (-(1 : ℝ) / 2)) g (Set.uIcc 0 1) := by
    intro t _
    simp only [hg]
    by_cases h : t < 1 / 2
    · have hF0 : F.F t = 0 := by
        by_contra hne
        have := (F.support t hne).1
        linarith
      simp [hF0]
    · rw [max_eq_left (by linarith)]
  have hcF : F.cF = ∫ t in (0 : ℝ)..1, g t := by
    unfold Cutoff.cF
    exact intervalIntegral.integral_congr heq
  rw [hcF]
  -- `g > 0` on an interval to the left of `t₀`
  obtain ⟨r, hr, hball⟩ := Metric.continuous_iff.1 hcont t₀ (F.F t₀ / 2) (by positivity)
  set a := max (t₀ - r / 2) (1 / 4) with ha
  have hat₀ : a < t₀ := max_lt (by linarith) (by linarith)
  have ha0 : 0 ≤ a := le_trans (by norm_num) (le_max_right _ _)
  have hgpos : ∀ t ∈ Set.Ioo a t₀, 0 < g t := by
    intro t ht
    have h1' : t₀ - r / 2 ≤ a := le_max_left _ _
    have hdist : dist t t₀ < r := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hF := hball t hdist
    rw [Real.dist_eq, abs_lt] at hF
    have hFt : 0 < F.F t := by linarith [hF.1]
    exact mul_pos hFt (Real.rpow_pos_of_pos (hmax t) _)
  have hg0 : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (F.nonneg t) (Real.rpow_nonneg (hmax t).le _)
  calc (0 : ℝ) < ∫ t in a..t₀, g t :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hgcont.intervalIntegrable _ _) hgpos hat₀
    _ ≤ ∫ t in (0 : ℝ)..1, g t :=
        intervalIntegral.integral_mono_interval ha0 hat₀.le h1
          (Filter.Eventually.of_forall hg0) (hgcont.intervalIntegrable _ _)

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `T(t) = 2^(v-2) (E t² + H_d)/d` for real `t`, so that `T(ℓ) = T_d(ℓ)`. -/
noncomputable def Treal (d : ℕ) (t : ℝ) : ℝ := 2 ^ (P.v - 2) * (P.E * t ^ 2 + P.H d) / d

/-- `Φ_y(t) = F(T(t)/x) W(2^((v-2)/2) y / √T(t))`. -/
noncomputable def Phi (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x y t : ℝ) : ℝ :=
  F.F (P.Treal d t / x) * W.W ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * y / Real.sqrt (P.Treal d t))

/-- The odd `k ≤ 2√x + 1`; for larger `k` we have `Φ_k = 0`. -/
noncomputable def kRange (x : ℝ) : Finset ℕ :=
  (Finset.range (⌈2 * Real.sqrt x⌉₊ + 1)).filter (fun k => k % 2 = 1)

/-- The main term `ℳ_d = 8 ∑_{k odd} χ(k) ϱ(dk)/(dk) ∫_ℝ Φ_k(t) dt` (equation (7.4)). -/
noncomputable def Md (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x : ℝ) : ℝ :=
  8 * ∑ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) * (rho (P.m d) (d * k) : ℝ) / (d * k) *
    ∫ t : ℝ, P.Phi F W d x k t

/-- The error term `ℰ_d = Σ_d(x) - ℳ_d` (equation (7.4)). -/
noncomputable def Ed (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x : ℝ) : ℝ :=
  P.Sigma F.F d x - P.Md F W d x

variable {P}

/-- `T(ℓ) = T_d(ℓ)` on the lattice `d ∣ Eℓ² + H_d`, and `Eℓ² + H_d = d T'`. -/
theorem IsGood.Treal_eq {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ}
    (hℓ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) : P.Treal d ℓ = (P.T d ℓ : ℝ) := by
  obtain ⟨h1, -⟩ := hd.T_spec hℓ
  have hpoly := P.poly_identity d ℓ hd.modEq
  have hv := P.hv
  have h4 : 4 * (d : ℤ) * P.T d ℓ = 2 ^ P.v * (P.E * ℓ ^ 2 + P.H d) := by rw [h1, hpoly]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have h4R : 4 * (d : ℝ) * (P.T d ℓ : ℝ) = 2 ^ P.v * ((P.E : ℝ) * (ℓ : ℝ) ^ 2 + P.H d) := by
    exact_mod_cast h4
  have h2v : (2 : ℝ) ^ P.v = 4 * 2 ^ (P.v - 2) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  unfold Treal
  rw [h2v] at h4R
  field_simp
  linarith

/-- **Equation (7.3).** `Σ_d(x) = 8 ∑_{k odd} χ(k) ∑_{ℓ ∈ ℤ, dk ∣ Eℓ² + H} Φ_k(ℓ)`. -/
theorem IsGood.Sigma_expand {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 1 ≤ x) :
    P.Sigma F.F d x = 8 * ∑ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
      ∑ᶠ (ℓ : ℤ) (_ : ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), P.Phi F W d x k ℓ := by
  classical
  have hx0 : 0 < x := by linarith
  have hF1 : ∀ t, F.F t ≠ 0 → t ≤ 1 := fun t ht => (F.support t ht).2
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.prime.ne_zero
  -- the inner sums as finite sums over `ellSet`
  have hinner : ∀ k : ℕ,
      (∑ᶠ (ℓ : ℤ) (_ : ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), P.Phi F W d x k ℓ) =
        ∑ ℓ ∈ P.ellSet d x,
          if ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d then P.Phi F W d x k ℓ else 0 := by
    intro k
    simp only [finsum_eq_if]
    apply finsum_eq_sum_of_support_subset
    intro ℓ hℓ
    rw [Function.mem_support] at hℓ
    split_ifs at hℓ with hdk
    · have hdvd : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d :=
        dvd_trans ⟨k, by push_cast; ring⟩ hdk
      have hF' : F.F (P.Treal d ℓ / x) ≠ 0 := left_ne_zero_of_mul hℓ
      have hTx : (P.T d ℓ : ℝ) ≤ x := by
        have := hF1 _ hF'
        rw [div_le_one hx0, hd.Treal_eq hdvd] at this
        exact this
      exact hd.mem_ellSet hdvd hTx
    · exact absurd rfl hℓ
  simp_rw [hinner]
  rw [hd.Sigma_eq_sum F.F hF1 hx0, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hdvd : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d := (Finset.mem_filter.1 hℓ).2
  have hTR := hd.Treal_eq hdvd
  obtain ⟨-, T', hT'4, hT⟩ := hd.T_spec hdvd
  have hTpos := hd.T_pos hdvd
  -- `Eℓ² + H = d T'` and `T' > 0`
  have hT'pos : 0 < T' := by
    have : (0 : ℤ) < 2 ^ (P.v - 2) := by positivity
    rw [hT] at hTpos
    exact pos_of_mul_pos_right hTpos this.le
  have hdT' : P.E * ℓ ^ 2 + P.H d = d * T' := by
    have h4 := hd.T_spec hdvd
    have hpoly := P.poly_identity d ℓ hd.modEq
    have hv := P.hv
    have e1 : 4 * (d : ℤ) * (2 ^ (P.v - 2) * T') = 2 ^ P.v * (P.E * ℓ ^ 2 + P.H d) := by
      rw [← hT, h4.1, hpoly]
    have h2v : (2 : ℤ) ^ P.v = 4 * 2 ^ (P.v - 2) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [h2v] at e1
    have h2pos : (4 : ℤ) * 2 ^ (P.v - 2) ≠ 0 := by positivity
    have : (4 * 2 ^ (P.v - 2)) * (P.E * ℓ ^ 2 + P.H d) = (4 * 2 ^ (P.v - 2)) * (d * T') := by
      linear_combination -e1
    exact mul_left_cancel₀ h2pos this
  -- for odd `k`: `k ∣ T ↔ dk ∣ Eℓ² + H`
  set Tn : ℕ := (P.T d ℓ).toNat with hTn
  set T'n : ℕ := T'.toNat with hT'n
  have hTnZ : (Tn : ℤ) = P.T d ℓ := Int.toNat_of_nonneg hTpos.le
  have hT'nZ : (T'n : ℤ) = T' := Int.toNat_of_nonneg hT'pos.le
  have hTn_eq : Tn = 2 ^ (P.v - 2) * T'n := by
    have : ((2 ^ (P.v - 2) * T'n : ℕ) : ℤ) = (Tn : ℤ) := by push_cast; rw [hT'nZ, hTnZ, hT]
    exact_mod_cast this.symm
  have hT'n4 : T'n % 4 = 1 := by
    have : ((T'n % 4 : ℕ) : ℤ) = 1 := by push_cast; rw [hT'nZ]; exact hT'4
    exact_mod_cast this
  have hkiff : ∀ k : ℕ, k % 2 = 1 →
      (k ∈ Tn.divisors ↔ ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) := by
    intro k hk
    have hT'n0 : 0 < T'n := by omega
    have hTn0 : Tn ≠ 0 := by rw [hTn_eq]; positivity
    rw [Nat.mem_divisors, hdT']
    constructor
    · rintro ⟨hkT, -⟩
      have hcop : Nat.Coprime k (2 ^ (P.v - 2)) :=
        Nat.Coprime.pow_right _ ((Nat.odd_iff.2 hk).coprime_two_right)
      rw [hTn_eq] at hkT
      have hkT' : k ∣ T'n := hcop.dvd_of_dvd_mul_left hkT
      have : (k : ℤ) ∣ T' := by rw [← hT'nZ]; exact_mod_cast hkT'
      push_cast
      exact mul_dvd_mul_left _ this
    · intro h
      push_cast at h
      have hkT' : (k : ℤ) ∣ T' := (mul_dvd_mul_iff_left hdZ).1 h
      have hkT'n : k ∣ T'n := by rw [← hT'nZ] at hkT'; exact_mod_cast hkT'
      refine ⟨?_, hTn0⟩
      rw [hTn_eq]
      exact Dvd.dvd.mul_left hkT'n _
  -- the term for `ℓ`
  rw [← Finset.mul_sum]
  by_cases hF0 : F.F ((P.T d ℓ : ℝ) / x) = 0
  · rw [hF0, mul_zero, eq_comm]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro k _
    split_ifs
    · simp [Phi, hTR, hF0]
    · simp
  · have hTx : (P.T d ℓ : ℝ) ≤ x := by
      have := hF1 _ hF0
      rwa [div_le_one hx0] at this
    have hhyp := hyperbola_identity W (P.v - 2) hT'n4
    rw [← hTn_eq] at hhyp
    have hrT : (r (P.T d ℓ) : ℝ) = (r ((Tn : ℕ) : ℤ) : ℝ) := by rw [hTnZ]
    rw [hrT, hhyp]
    have hexp : ((P.v - 2 : ℕ) : ℝ) / 2 = ((P.v : ℝ) - 2) / 2 := by
      rw [Nat.cast_sub P.hv]; push_cast; ring
    have hTnR : ((Tn : ℕ) : ℝ) = (P.T d ℓ : ℝ) := by exact_mod_cast hTnZ
    rw [hexp, hTnR]
    have hTpR : (0 : ℝ) < P.T d ℓ := by exact_mod_cast hTpos
    -- the weight vanishes for `k` outside `kRange x`
    have hW0 : ∀ k : ℕ, k ∉ kRange x → k % 2 = 1 →
        W.W ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * k / Real.sqrt (P.T d ℓ)) = 0 := by
      intro k hk hodd
      apply W.eq_zero
      simp only [kRange, Finset.mem_filter, Finset.mem_range, not_and] at hk
      have hk' : ⌈2 * Real.sqrt x⌉₊ + 1 ≤ k := by
        by_contra hlt; exact hk (by omega) hodd
      have h2 : 2 * Real.sqrt x ≤ k := by
        have h3 := Nat.le_ceil (2 * Real.sqrt x)
        have h4 : ((⌈2 * Real.sqrt x⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk'
        push_cast at h4
        linarith
      have hsq : Real.sqrt (P.T d ℓ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hTx
      have hsqpos : 0 < Real.sqrt (P.T d ℓ) := Real.sqrt_pos.2 hTpR
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) := by
        apply Real.one_le_rpow (by norm_num)
        have : (2 : ℝ) ≤ P.v := by exact_mod_cast P.hv
        linarith
      rw [le_div_iff₀ hsqpos]
      have hk0 : (0 : ℝ) ≤ k := by positivity
      nlinarith
    have hchi0 : ∀ k : ℕ, k % 2 = 0 → (ZMod.χ₄ (k : ZMod 4) : ℝ) = 0 := by
      intro k hk
      rw [ZMod.χ₄_nat_eq_if_mod_four]
      simp [hk]
    -- left side: restrict to `divisors ∩ kRange`
    have hL : ∑ k ∈ Tn.divisors, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          W.W ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * k / Real.sqrt (P.T d ℓ)) =
        ∑ k ∈ Tn.divisors ∩ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          W.W ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * k / Real.sqrt (P.T d ℓ)) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro k hk hkC
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · rw [hchi0 k h0, zero_mul]
      · have : k ∉ kRange x := fun h => hkC (Finset.mem_inter.2 ⟨hk, h⟩)
        rw [hW0 k this h1, mul_zero]
    -- right side: restrict to `divisors ∩ kRange`
    have hR : ∑ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          (if ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d then P.Phi F W d x k ℓ else 0) =
        ∑ k ∈ Tn.divisors ∩ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          (if ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d then P.Phi F W d x k ℓ else 0) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_right
      intro k hkK hkC
      have hodd : k % 2 = 1 := (Finset.mem_filter.1 hkK).2
      have hkD : k ∉ Tn.divisors := fun h => hkC (Finset.mem_inter.2 ⟨h, hkK⟩)
      rw [ite_eq_right (fun h => hkD ((hkiff k hodd).2 h)), mul_zero]
    have hC : ∑ k ∈ Tn.divisors ∩ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          (if ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d then P.Phi F W d x k ℓ else 0) =
        F.F ((P.T d ℓ : ℝ) / x) * ∑ k ∈ Tn.divisors ∩ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) *
          W.W ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * k / Real.sqrt (P.T d ℓ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hkD, hkK⟩ := Finset.mem_inter.1 hk
      have hodd : k % 2 = 1 := (Finset.mem_filter.1 hkK).2
      rw [ite_eq_left ((hkiff k hodd).1 hkD)]
      simp only [Phi, hTR]
      ring
    rw [hR, hC, hL]
    ring

end PatternData

end Triples
