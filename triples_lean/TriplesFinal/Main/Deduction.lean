import TriplesFinal.Asymptotic.SigmaLower
import TriplesFinal.GoodPrimes.Reduction
import TriplesFinal.GoodPrimes.BadPrimes
import TriplesFinal.Basic.DivisorBound
import TriplesFinal.Families.Reduce
import Mathlib.RingTheory.Int.Basic

/-!
# The deduction of Theorems 1.1 and 1.3 from Theorem 4.3

* `exists_cutoff`: a smooth weight `F` as in §4 exists.
* `good_primes_lower`: by the prime number theorem in arithmetic progressions and the count of
  bad primes, there are `≫ y / log y` good primes in `(y/2, y]`.
* `multWeight_bound`: by the divisor bound, `r(T) r(P(P + B)) ≪_ε x^(3ε)` for `n ≤ x`.
* `lower_from_sigma`: the conclusion of Theorem 4.3 for some `ϖ` gives
  `S_{a,b}(x) ≫ x^(1/2+δ)` for every `δ < ϖ/2` (when `a` or `b` is odd).
* `exists_odd_reduction` and `lower_general`: Lemma 2.1, applied repeatedly, reduces to the case
  that `a` or `b` is odd.

Paper: §4, deduction of Theorems 1.1 and 1.3.
-/

namespace Triples

open Filter

/-- **A smooth cutoff exists**: `F(t) = s(4(t - 1/2)) s(4(1 - t))`, with `s` the smooth
transition function. -/
theorem exists_cutoff : Nonempty Cutoff := by
  refine ⟨⟨fun t => Real.smoothTransition (4 * (t - 1 / 2)) *
    Real.smoothTransition (4 * (1 - t)), ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
  · intro t
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · intro t
    have h1 := Real.smoothTransition.le_one (4 * (t - 1 / 2))
    have h2 := Real.smoothTransition.le_one (4 * (1 - t))
    have h3 := Real.smoothTransition.nonneg (4 * (t - 1 / 2))
    have h4 := Real.smoothTransition.nonneg (4 * (1 - t))
    show Real.smoothTransition (4 * (t - 1 / 2)) * Real.smoothTransition (4 * (1 - t)) ≤ 1
    nlinarith
  · intro t ht
    have h1 : Real.smoothTransition (4 * (t - 1 / 2)) ≠ 0 := left_ne_zero_of_mul ht
    have h2 : Real.smoothTransition (4 * (1 - t)) ≠ 0 := right_ne_zero_of_mul ht
    rw [Ne, Real.smoothTransition.zero_iff_nonpos, not_le] at h1 h2
    constructor <;> linarith
  · refine ⟨3 / 4, ?_⟩
    show Real.smoothTransition (4 * (3 / 4 - 1 / 2)) * Real.smoothTransition (4 * (1 - 3 / 4)) ≠ 0
    rw [Real.smoothTransition.one_of_one_le (by norm_num),
      Real.smoothTransition.one_of_one_le (by norm_num)]
    norm_num

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `d₀` is coprime to `2^J`. -/
theorem d₀_isCoprime : IsCoprime P.d₀ ((2 ^ P.J : ℕ) : ℤ) := by
  have h2 : IsCoprime P.d₀ 2 := Int.isCoprime_two_right.2 (Int.odd_iff.2 (by have := P.hd₀; omega))
  push_cast
  exact h2.pow_right

/-- `log y ≤ 2√y`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h1 : Real.log y ≤ y ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div (by linarith) (by norm_num)
  rw [Real.sqrt_eq_rpow]
  linarith

/-- **Good primes in dyadic ranges.** There are `c > 0` and `y₀` with
`#{d good : y/2 < d ≤ y} ≥ c y / log y` for `y ≥ y₀`. -/
theorem good_primes_lower (hPNT : PrimesInAPLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      c * y / Real.log y ≤ ({d : ℕ | P.IsGood d ∧ y / 2 < d ∧ (d : ℝ) ≤ y}.ncard : ℝ) := by
  obtain ⟨c₂, hc₂, x₂, hx₂⟩ := hPNT (2 ^ P.J) P.d₀ (by positivity) P.d₀_isCoprime
  obtain ⟨C₃, y₃, hC₃⟩ := P.bad_primes_dyadic
  set Y₀ := (4 * ((C₃ : ℝ) + 1) / c₂) ^ 2 + 3 with hY₀
  refine ⟨c₂ / 2, by positivity, max (max x₂ y₃) Y₀, fun y hy => ?_⟩
  have hyx₂ : x₂ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyy₃ : y₃ ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyY : Y₀ ≤ y := le_trans (le_max_right _ _) hy
  have hy3 : 3 ≤ y := by
    have : 0 ≤ (4 * ((C₃ : ℝ) + 1) / c₂) ^ 2 := sq_nonneg _
    linarith
  have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
  set A := {p : ℕ | p.Prime ∧ y / 2 < p ∧ (p : ℝ) ≤ y ∧ (p : ℤ) ≡ P.d₀ [ZMOD ((2 ^ P.J : ℕ) : ℤ)]}
    with hAdef
  set G := {d : ℕ | P.IsGood d ∧ y / 2 < d ∧ (d : ℝ) ≤ y} with hGdef
  set Bd := {d : ℕ | y / 2 < d ∧ (d : ℝ) ≤ y ∧ d.Prime ∧ (d : ℤ) ≡ P.d₀ [ZMOD 2 ^ P.J] ∧
    ¬ P.IsGood d} with hBdef
  have hA : c₂ * y / Real.log y ≤ (A.ncard : ℝ) := hx₂ y hyx₂
  have hB : Bd.ncard ≤ C₃ := hC₃ y hyy₃
  have hsub : A ⊆ G ∪ Bd := by
    rintro p ⟨hp, hlo, hhi, hcong⟩
    by_cases hg : P.IsGood p
    · left; exact ⟨hg, hlo, hhi⟩
    · right
      refine ⟨hlo, hhi, hp, ?_, hg⟩
      have : (((2 ^ P.J : ℕ) : ℤ)) = 2 ^ P.J := by push_cast; ring
      rw [this] at hcong
      exact hcong
  have hGfin : G.Finite :=
    (Set.finite_Iic ⌊y⌋₊).subset (fun d hd => Set.mem_Iic.2 (Nat.le_floor hd.2.2))
  have hBfin : Bd.Finite :=
    (Set.finite_Iic ⌊y⌋₊).subset (fun d hd => Set.mem_Iic.2 (Nat.le_floor hd.2.1))
  have hcard : A.ncard ≤ G.ncard + C₃ :=
    ((Set.ncard_le_ncard hsub (hGfin.union hBfin)).trans (Set.ncard_union_le _ _)).trans
      (by omega)
  have hcardR : (A.ncard : ℝ) ≤ G.ncard + C₃ := by exact_mod_cast hcard
  -- `C₃ ≤ (c₂/2) y / log y`
  have hsqrt : 4 * ((C₃ : ℝ) + 1) / c₂ ≤ Real.sqrt y := by
    rw [show 4 * ((C₃ : ℝ) + 1) / c₂ = Real.sqrt ((4 * ((C₃ : ℝ) + 1) / c₂) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsy : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
  have hl := log_le_two_sqrt (y := y) (by linarith)
  have hC : (C₃ : ℝ) ≤ c₂ / 2 * y / Real.log y := by
    rw [le_div_iff₀ hlogpos]
    have hc' : 4 * ((C₃ : ℝ) + 1) ≤ c₂ * Real.sqrt y := by
      have := (div_le_iff₀ hc₂).1 hsqrt
      linarith
    have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hC0 : (0 : ℝ) ≤ C₃ := by positivity
    calc (C₃ : ℝ) * Real.log y ≤ C₃ * (2 * Real.sqrt y) := mul_le_mul_of_nonneg_left hl hC0
      _ ≤ c₂ / 2 * y := by nlinarith
  calc c₂ / 2 * y / Real.log y = c₂ * y / Real.log y - c₂ / 2 * y / Real.log y := by ring
    _ ≤ (A.ncard : ℝ) - C₃ := by linarith
    _ ≤ G.ncard := by linarith

/-- **The divisor bound for the multiplicity weight**: for `n ∈ 𝒮_{a,b}(x)` and `x` large,
`r(T) r(P(P + B)) ≤ C x^(3ε)`. -/
theorem multWeight_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (b : ℝ) ≤ x → ∀ n ∈ SSet a b x,
      (P.multWeight n : ℝ) ≤ C * x ^ (3 * ε) := by
  obtain ⟨Cr, hCr, hr⟩ := r_le_rpow hε
  refine ⟨Cr * Cr * (2 : ℝ) ^ ε * (4 : ℝ) ^ ε, by positivity, fun x hbx n hn => ?_⟩
  obtain ⟨hn1, hnx, -, -, -⟩ := hn
  have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hn1) hnx
  have hxpos : 0 < x := by linarith
  have htr := P.triple n
  have hab : (a : ℤ) < b := by exact_mod_cast P.hab
  have ha0 : (0 : ℤ) < a := by exact_mod_cast P.ha
  -- the three numbers lie in `[1, 2x]`
  have hmem : ∀ m ∈ ({(n : ℤ) + P.p₀, n + P.p₀ + P.B, n + P.p₀ + P.A} : Finset ℤ),
      1 ≤ m ∧ (m : ℝ) ≤ 2 * x := by
    intro m hm
    rw [htr] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hnR : ((n : ℤ) : ℝ) ≤ x := by exact_mod_cast hnx
    have hbR : ((b : ℤ) : ℝ) ≤ x := by exact_mod_cast hbx
    rcases hm with rfl | rfl | rfl
    · exact ⟨by exact_mod_cast hn1, by push_cast at hnR ⊢; linarith⟩
    · refine ⟨by omega, ?_⟩
      have : ((a : ℤ) : ℝ) ≤ (b : ℤ) := by exact_mod_cast hab.le
      push_cast at hnR hbR this ⊢; linarith
    · refine ⟨by omega, ?_⟩
      push_cast at hnR hbR ⊢; linarith
  obtain ⟨hT1, hT2⟩ := hmem ((n : ℤ) + P.p₀ + P.A) (by simp)
  obtain ⟨hP1, hP2⟩ := hmem ((n : ℤ) + P.p₀) (by simp)
  obtain ⟨hPB1, hPB2⟩ := hmem ((n : ℤ) + P.p₀ + P.B) (by simp)
  -- `r(T) ≤ Cr (2x)^ε`
  set T := (n : ℤ) + P.p₀ + P.A with hT
  set Pp := (n : ℤ) + P.p₀ with hPp
  have hrT : (r T : ℝ) ≤ Cr * (2 * x) ^ ε := by
    have h := hr T.toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h
    calc (r T : ℝ) ≤ Cr * ((T.toNat : ℕ) : ℝ) ^ ε := h
      _ = Cr * (T : ℝ) ^ ε := by
          congr 2
          have : ((T.toNat : ℤ) : ℝ) = (T : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
          exact_mod_cast this
      _ ≤ Cr * (2 * x) ^ ε := by
          have h0 : (0 : ℝ) ≤ T := by exact_mod_cast (show (0 : ℤ) ≤ T by omega)
          gcongr
  have hrP : (r (Pp * (Pp + P.B)) : ℝ) ≤ Cr * (4 * x ^ 2) ^ ε := by
    have hpos : 1 ≤ Pp * (Pp + P.B) := by nlinarith
    have h := hr (Pp * (Pp + P.B)).toNat (by omega)
    rw [Int.toNat_of_nonneg (by omega)] at h
    have hcast : (((Pp * (Pp + P.B)).toNat : ℕ) : ℝ) = ((Pp * (Pp + P.B) : ℤ) : ℝ) := by
      have : (((Pp * (Pp + P.B)).toNat : ℤ) : ℝ) = ((Pp * (Pp + P.B) : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      exact_mod_cast this
    rw [hcast] at h
    calc (r (Pp * (Pp + P.B)) : ℝ) ≤ Cr * ((Pp * (Pp + P.B) : ℤ) : ℝ) ^ ε := h
      _ ≤ Cr * (4 * x ^ 2) ^ ε := by
          have h0 : (0 : ℝ) ≤ ((Pp * (Pp + P.B) : ℤ) : ℝ) := by
            exact_mod_cast (show (0 : ℤ) ≤ Pp * (Pp + P.B) by omega)
          gcongr
          · push_cast
            have h1 : (1 : ℝ) ≤ (Pp : ℝ) := by exact_mod_cast hP1
            have h2 : (1 : ℝ) ≤ (Pp : ℝ) + P.B := by
              have : (1 : ℤ) ≤ Pp + P.B := hPB1
              exact_mod_cast this
            have h3 : (Pp : ℝ) ≤ 2 * x := hP2
            have h4 : (Pp : ℝ) + P.B ≤ 2 * x := by
              have : ((Pp + P.B : ℤ) : ℝ) ≤ 2 * x := hPB2
              push_cast at this; exact this
            nlinarith
  have hmw : (P.multWeight n : ℝ) = (r T : ℝ) * (r (Pp * (Pp + P.B)) : ℝ) := by
    simp only [multWeight, hT, hPp]; push_cast; ring
  rw [hmw]
  have h2x : (2 * x) ^ ε = (2 : ℝ) ^ ε * x ^ ε := Real.mul_rpow (by norm_num) hxpos.le
  have h4x : (4 * x ^ 2) ^ ε = (4 : ℝ) ^ ε * x ^ (2 * ε) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have h3x : x ^ ε * x ^ (2 * ε) = x ^ (3 * ε) := by
    rw [← Real.rpow_add hxpos]; ring_nf
  calc (r T : ℝ) * (r (Pp * (Pp + P.B)) : ℝ)
      ≤ (Cr * (2 * x) ^ ε) * (Cr * (4 * x ^ 2) ^ ε) :=
        mul_le_mul hrT hrP (by positivity) (by positivity)
    _ = Cr * Cr * (2 : ℝ) ^ ε * (4 : ℝ) ^ ε * (x ^ ε * x ^ (2 * ε)) := by
        rw [h2x, h4x]; ring
    _ = Cr * Cr * (2 : ℝ) ^ ε * (4 : ℝ) ^ ε * x ^ (3 * ε) := by rw [h3x]

/-- **From Theorem 4.3 to the lower bound for `S_{a,b}(x)`** (for `a` or `b` odd). -/
theorem lower_from_sigma (hPNT : PrimesInAPLowerBound) (F : Cutoff) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (H43 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ,
      ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ ϖ →
        c * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤ P.Sigma F.F d x)
    {δ : ℝ} (hδ : δ < ϖ / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x := by
  set δp := max δ 0 with hδp
  have hδp1 : δ ≤ δp := le_max_left _ _
  have hδp0 : 0 ≤ δp := le_max_right _ _
  have hgap : 0 < ϖ / 2 - δp := by
    rcases le_total δ 0 with h | h
    · rw [hδp, max_eq_right h]; linarith
    · rw [hδp, max_eq_left h]; linarith
  obtain ⟨ε₀, hε₀, H⟩ := H43
  set ε := min ε₀ ((ϖ / 2 - δp) / (2 * (ϖ + 4))) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεgap : ε * (2 * (ϖ + 4)) ≤ ϖ / 2 - δp := by
    have := min_le_right ε₀ ((ϖ / 2 - δp) / (2 * (ϖ + 4)))
    rwa [← hεdef, le_div_iff₀ (by positivity)] at this
  obtain ⟨c₄, hc₄, x₄, hx₄⟩ := H ε hε hεε₀
  obtain ⟨cg, hcg, yg, hyg⟩ := P.good_primes_lower hPNT
  obtain ⟨Cm, hCm, hCmb⟩ := P.multWeight_bound hε
  set η := ϖ * (1 / 2 - ε) - 3 * ε - δ with hηdef
  have hη : 0 < η := by nlinarith
  set Yg := max yg 2 with hYg
  have hYg1 : 1 ≤ Yg := le_trans (by norm_num) (le_max_right _ _)
  set x₀ := max (max x₄ (2 * ((b : ℝ) + 1))) (max (Yg ^ (1 / ϖ)) 2) with hx₀
  refine ⟨cg * c₄ * η / (Cm * ϖ), by positivity, x₀, fun x hx => ?_⟩
  have hxx₄ : x₄ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : 2 * ((b : ℝ) + 1) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxY : Yg ^ (1 / ϖ) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set y := x ^ ϖ with hydef
  have hypos : 0 < y := by positivity
  have hyY : Yg ≤ y := by
    have h1 : (Yg ^ (1 / ϖ)) ^ ϖ ≤ x ^ ϖ :=
      Real.rpow_le_rpow (by positivity) hxY hϖ.le
    rwa [← Real.rpow_mul (by linarith), one_div_mul_cancel hϖ.ne', Real.rpow_one] at h1
  have hyyg : yg ≤ y := le_trans (le_max_left _ _) hyY
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hyY
  have hlogy : Real.log y = ϖ * Real.log x := Real.log_rpow hxpos ϖ
  -- the good primes in `(y/2, y]`
  set G := {d : ℕ | P.IsGood d ∧ y / 2 < d ∧ (d : ℝ) ≤ y} with hGdef
  have hGfin : G.Finite :=
    (Set.finite_Iic ⌊y⌋₊).subset (fun d hd => Set.mem_Iic.2 (Nat.le_floor hd.2.2))
  set D := hGfin.toFinset with hDdef
  have hDgood : ∀ d ∈ D, P.IsGood d := fun d hd => ((Set.Finite.mem_toFinset _).1 hd).1
  have hDcard : cg * y / Real.log y ≤ (D.card : ℝ) := by
    rw [hDdef, ← Set.ncard_eq_toFinset_card G hGfin]
    exact hyg y hyyg
  -- lower bound for `∑ Σ_d(x)`
  have hlow : (D.card : ℝ) * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)) ≤
      ∑ d ∈ D, P.Sigma F.F d x := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hdg, hdlo, hdhi⟩ := (Set.Finite.mem_toFinset _).1 hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hdg.prime.pos
    calc c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)
        ≤ c₄ * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) := by
          have hz : -1 / 2 - ε ≤ 0 := by linarith
          have := Real.rpow_le_rpow_of_nonpos hdpos hdhi hz
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ P.Sigma F.F d x := hx₄ x hxx₄ d hdg hdhi
  -- upper bound via Proposition 4.2 and the divisor bound
  have hup : ∑ d ∈ D, P.Sigma F.F d x ≤ (S a b x : ℝ) * (Cm * x ^ (3 * ε)) := by
    have h1 := P.reduction F.nonneg F.le_one F.support D hDgood hxb
    have h2 : ∑ n ∈ (SSet_finite a b x).toFinset, (P.multWeight n : ℝ) ≤
        ∑ _n ∈ (SSet_finite a b x).toFinset, Cm * x ^ (3 * ε) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hCmb x (by linarith) n ((Set.Finite.mem_toFinset _).1 hn)
    have h3 : ∑ _n ∈ (SSet_finite a b x).toFinset, Cm * x ^ (3 * ε) =
        (S a b x : ℝ) * (Cm * x ^ (3 * ε)) := by
      rw [Finset.sum_const, nsmul_eq_mul, S, Set.ncard_eq_toFinset_card _ (SSet_finite a b x)]
    linarith
  -- combine
  have hkey : (S a b x : ℝ) * (Cm * x ^ (3 * ε)) ≥
      cg * y / Real.log y * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)) := by
    have hc0 : 0 ≤ c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε) := by positivity
    calc cg * y / Real.log y * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε))
        ≤ (D.card : ℝ) * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)) :=
          mul_le_mul_of_nonneg_right hDcard hc0
      _ ≤ _ := hlow.trans hup
  -- rewrite the lower bound as a power of `x`
  have hy1 : y * y ^ (-1 / 2 - ε) = x ^ (ϖ * (1 / 2 - ε)) := by
    have e1 : y * y ^ (-1 / 2 - ε) = y ^ ((1 : ℝ) + (-1 / 2 - ε)) := by
      rw [Real.rpow_add hypos, Real.rpow_one]
    rw [e1, hydef, ← Real.rpow_mul hxpos.le]
    congr 1; ring
  have hexp : x ^ (1 / 2 : ℝ) * x ^ (ϖ * (1 / 2 - ε)) =
      x ^ (1 / 2 + δ) * x ^ (3 * ε) * x ^ η := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos, hηdef]
    congr 1; ring
  have hlogη : η * Real.log x ≤ x ^ η := by
    have := Real.log_le_rpow_div hxpos.le hη
    rw [le_div_iff₀ hη] at this; linarith
  have hCx : 0 < Cm * x ^ (3 * ε) := by positivity
  have hfinal : cg * c₄ * η / (Cm * ϖ) * x ^ (1 / 2 + δ) * (Cm * x ^ (3 * ε)) ≤
      cg * y / Real.log y * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)) := by
    have e : cg * y / Real.log y * (c₄ * x ^ (1 / 2 : ℝ) * y ^ (-1 / 2 - ε)) =
        cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε) * x ^ η) / (ϖ * Real.log x) := by
      rw [← hexp, ← hy1, ← hlogy]; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : cg * c₄ * η / (Cm * ϖ) * x ^ (1 / 2 + δ) * (Cm * x ^ (3 * ε)) * (ϖ * Real.log x) =
        cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε)) * (η * Real.log x) := by
      field_simp [hCm.ne', hϖ.ne']
    rw [e2]
    have hcc : 0 ≤ cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε)) := by positivity
    calc cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε)) * (η * Real.log x)
        ≤ cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε)) * x ^ η :=
          mul_le_mul_of_nonneg_left hlogη hcc
      _ = cg * c₄ * (x ^ (1 / 2 + δ) * x ^ (3 * ε) * x ^ η) := by ring
  exact le_of_mul_le_mul_right (hfinal.trans hkey) hCx

end PatternData

/-- **Lemma 2.1, iterated**: for `0 < a < b` there are `k` and `0 < a' < b'` with `a'` or `b'`
odd such that `S_{a',b'}(x/2^k) ≤ S_{a,b}(x)` for all `x`. -/
theorem exists_odd_reduction : ∀ a b : ℕ, 0 < a → a < b →
    ∃ k a' b' : ℕ, 0 < a' ∧ a' < b' ∧ (a' % 2 = 1 ∨ b' % 2 = 1) ∧
      ∀ x : ℝ, S a' b' (x / 2 ^ k) ≤ S a b x := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b ha hab
    by_cases hodd : a % 2 = 1 ∨ b % 2 = 1
    · exact ⟨0, a, b, ha, hab, hodd, fun x => by simp⟩
    · have ha2 : a % 2 = 0 := by omega
      have hb2 : b % 2 = 0 := by omega
      have hae : Even a := Nat.even_iff.2 ha2
      have hbe : Even b := Nat.even_iff.2 hb2
      obtain ⟨k, a', b', ha', hab', hodd', hS⟩ :=
        ih (a / 2) (by omega) (b / 2) (by omega) (by omega)
      refine ⟨k + 1, a', b', ha', hab', hodd', fun x => ?_⟩
      have h1 := hS (x / 2)
      have h2 := S_half_le_S a b x hae hbe
      have e : x / 2 ^ (k + 1) = x / 2 / 2 ^ k := by rw [pow_succ]; ring
      rw [e]
      exact h1.trans h2

/-- **The reduction to `a` or `b` odd**: a lower bound `S ≫ x^(1/2+δ)` for all patterns with `a`
or `b` odd gives it for all patterns. -/
theorem lower_general {δ : ℝ}
    (hodd : ∀ a b : ℕ, 0 < a → a < b → (a % 2 = 1 ∨ b % 2 = 1) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x := by
  obtain ⟨k, a', b', ha', hab', hodd', hS⟩ := exists_odd_reduction a b ha hab
  obtain ⟨c, hc, x₀, hx₀⟩ := hodd a' b' ha' hab' hodd'
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨c / ((2 : ℝ) ^ k) ^ (1 / 2 + δ), by positivity, 2 ^ k * max x₀ 1, fun x hx => ?_⟩
  have hx' : max x₀ 1 ≤ x / 2 ^ k := by rw [le_div_iff₀ h2k]; linarith
  have hxpos : 0 ≤ x := by
    have : (0 : ℝ) ≤ 2 ^ k * max x₀ 1 := by positivity
    linarith
  have h1 := hx₀ (x / 2 ^ k) (le_trans (le_max_left _ _) hx')
  have e : (x / 2 ^ k) ^ (1 / 2 + δ) = x ^ (1 / 2 + δ) / ((2 : ℝ) ^ k) ^ (1 / 2 + δ) :=
    Real.div_rpow hxpos h2k.le _
  rw [e] at h1
  calc c / ((2 : ℝ) ^ k) ^ (1 / 2 + δ) * x ^ (1 / 2 + δ)
      = c * (x ^ (1 / 2 + δ) / ((2 : ℝ) ^ k) ^ (1 / 2 + δ)) := by ring
    _ ≤ S a' b' (x / 2 ^ k) := h1
    _ ≤ S a b x := by exact_mod_cast hS x

end Triples
