import TriplesFinal.Poisson.PoissonTail
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 9.1(d): the dyadic decomposition in `h`

Assume (H). Then `Ξ = ∑_{M ∈ 𝓜} (Ξ_M(ψ₂) + Ξ_M(ψ₂⁻)) + O(Δ^(k_η) (qX)^(-1))` and
`#𝓜 ≪ log(qX)`, where `𝓜 = {2^(i/2) : i ≥ -2, 2^(i/2) ≤ 2h₀}`.

By Lemma 9.1(a),(b), `Ξ = ∑_{h ≥ 1} (W_h(ψ₂) + W_h(ψ₂⁻))`, and
`∑_{M ∈ 𝓜} (Ξ_M(ψ₂) + Ξ_M(ψ₂⁻)) = ∑_{h ≥ 1} w(h) (W_h(ψ₂) + W_h(ψ₂⁻))` with
`w(h) = ∑_{M ∈ 𝓜} ψ₀(h/M)`. Here `w(h) = 1` for `1 ≤ h ≤ h₀` (`dyadic_weight_eq_one`) and
`0 ≤ w(h) ≤ 1` always, so the difference is bounded by `∑_{|h| > h₀} |W_h(ψ₂)|`, which is
Lemma 9.1(c). Finally `h₀ ≤ (qX)^(1+η)` and `qX ≥ 48 > e` give `#𝓜 ≪ log(qX)`.

Paper: §9.1, Lemma 9.1(d).
-/

namespace Triples

open MeasureTheory Filter
open scoped Real

section Dyadic

/-- The number of candidate exponents in `dyadicSet h₀`. -/
noncomputable def dyadicN (h₀ : ℝ) : ℕ := Nat.ceil (2 * (Real.log (2 * h₀) / Real.log 2) + 5)

/-- The exponents `i ≥ -2` with `2^(i/2) ≤ 2h₀`. -/
noncomputable def dyadicIdx (h₀ : ℝ) : Finset ℤ :=
  ((Finset.range (dyadicN h₀)).filter
    (fun j : ℕ => (2 : ℝ) ^ ((((j : ℤ) - 2 : ℤ) : ℝ) / 2) ≤ 2 * h₀)).image (fun j : ℕ => (j : ℤ) - 2)

theorem two_rpow_injective : Function.Injective (fun x : ℝ => (2 : ℝ) ^ x) := by
  intro a b hab
  simp only at hab
  apply le_antisymm
  · rw [← Real.rpow_le_rpow_left_iff one_lt_two, hab]
  · rw [← Real.rpow_le_rpow_left_iff one_lt_two, hab]

theorem sum_dyadicSet (h₀ : ℝ) (φ : ℝ → ℝ) :
    ∑ M ∈ dyadicSet h₀, φ M = ∑ i ∈ dyadicIdx h₀, φ ((2 : ℝ) ^ ((i : ℝ) / 2)) := by
  classical
  unfold dyadicSet dyadicIdx
  rw [Finset.filter_image, Finset.sum_image, Finset.sum_image]
  · rfl
  · intro a _ b _ hab
    simp only at hab
    omega
  · intro a _ b _ hab
    have h := two_rpow_injective hab
    have : (((a : ℤ) - 2 : ℤ) : ℝ) = (((b : ℤ) - 2 : ℤ) : ℝ) := by linarith
    have : ((a : ℤ) - 2 : ℤ) = (b : ℤ) - 2 := by exact_mod_cast this
    omega

theorem dyadic_weight_le_one (ψ₀ : DyadicPartition) (h₀ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∑ M ∈ dyadicSet h₀, ψ₀.ψ₀ (t / M) ≤ 1 := by
  rw [sum_dyadicSet h₀ (fun M => ψ₀.ψ₀ (t / M))]
  exact sum_le_hasSum _ (fun i _ => ψ₀.nonneg _) (ψ₀.sum_eq_one t ht)

theorem dyadic_weight_nonneg (ψ₀ : DyadicPartition) (h₀ t : ℝ) :
    0 ≤ ∑ M ∈ dyadicSet h₀, ψ₀.ψ₀ (t / M) :=
  Finset.sum_nonneg fun _ _ => ψ₀.nonneg _

/-- For `1 ≤ t ≤ h₀` all dyadic pieces at `t` are present: `∑_{M ∈ 𝓜} ψ₀(t/M) = 1`. -/
theorem dyadic_weight_eq_one (ψ₀ : DyadicPartition) {h₀ t : ℝ} (ht1 : 1 ≤ t) (hth : t ≤ h₀) :
    ∑ M ∈ dyadicSet h₀, ψ₀.ψ₀ (t / M) = 1 := by
  classical
  have ht : 0 < t := by linarith
  have hh₀ : 0 < h₀ := by linarith
  rw [sum_dyadicSet h₀ (fun M => ψ₀.ψ₀ (t / M))]
  refine ((hasSum_sum_of_ne_finset_zero ?_).unique (ψ₀.sum_eq_one t ht)).symm.symm
  intro i hi
  by_contra hne
  apply hi
  obtain ⟨h1, h2⟩ := ψ₀.support _ hne
  have hpos : 0 < (2 : ℝ) ^ ((i : ℝ) / 2) := by positivity
  rw [le_div_iff₀ hpos, one_mul] at h1
  rw [div_le_iff₀ hpos] at h2
  -- `2^(i/2) ≥ t/2 ≥ 1/2`, so `i ≥ -2`
  have hi2 : -2 ≤ i := by
    have : (2 : ℝ) ^ ((-1 : ℝ)) ≤ (2 : ℝ) ^ ((i : ℝ) / 2) := by
      rw [Real.rpow_neg_one]; linarith
    rw [Real.rpow_le_rpow_left_iff one_lt_two] at this
    have : (-2 : ℝ) ≤ i := by linarith
    exact_mod_cast this
  -- `2^(i/2) ≤ t ≤ h₀`, so `i ≤ 2 log h₀ / log 2`
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hile : (i : ℝ) / 2 * Real.log 2 ≤ Real.log h₀ := by
    rw [← Real.log_rpow two_pos]
    exact Real.log_le_log hpos (h1.trans hth)
  rw [dyadicIdx, Finset.mem_image]
  refine ⟨(i + 2).toNat, ?_, by omega⟩
  rw [Finset.mem_filter, Finset.mem_range]
  have hcast : ((((i + 2).toNat : ℕ) : ℤ) - 2 : ℤ) = i := by omega
  rw [hcast]
  refine ⟨?_, by linarith⟩
  -- `(i + 2).toNat < dyadicN h₀`
  unfold dyadicN
  rw [← Nat.cast_lt (α := ℝ)]
  refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
  have hcast2 : (((i + 2).toNat : ℕ) : ℝ) = (i : ℝ) + 2 := by
    have : (((i + 2).toNat : ℕ) : ℤ) = i + 2 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  rw [hcast2, Real.log_mul two_ne_zero hh₀.ne', add_div, div_self hlog2.ne']
  have : (i : ℝ) ≤ 2 * (Real.log h₀ / Real.log 2) := by
    rw [mul_div_assoc', le_div_iff₀ hlog2]; linarith
  linarith

/-- `#𝓜 ≤ max(2 log(2h₀)/log 2 + 6, 0)`. -/
theorem card_dyadicSet_le (h₀ : ℝ) :
    ((dyadicSet h₀).card : ℝ) ≤ max (2 * (Real.log (2 * h₀) / Real.log 2) + 6) 0 := by
  have h1 : (dyadicSet h₀).card ≤ dyadicN h₀ := by
    unfold dyadicSet
    exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp [dyadicN]))
  refine (Nat.cast_le.2 h1).trans ?_
  unfold dyadicN
  set x := 2 * (Real.log (2 * h₀) / Real.log 2) + 5
  by_cases hx : 0 ≤ x
  · have := Nat.ceil_lt_add_one hx
    exact le_trans (by linarith) (le_max_left _ (0 : ℝ))
  · push Not at hx
    rw [Nat.ceil_eq_zero.2 hx.le, Nat.cast_zero]
    exact le_max_right _ _

/-- **Lemma 9.1(d).** `Ξ = ∑_{M ∈ 𝓜} (Ξ_M(ψ₂) + Ξ_M(ψ₂⁻)) + O(Δ^(k_η) (qX)^(-1))`, and
`#𝓜 ≪ log(qX)`. -/
theorem poisson_d (ψ₀ : DyadicPartition) {η : ℝ} (hη : 0 < η) (Cν : ℕ → ℝ) :
    ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ‖Xi E H d κ X K ψ₁ ψ₂ - ∑ M ∈ dyadicSet (h₀ E d X K η),
          (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M)‖ ≤
        C * Δ ^ (⌈4 / η⌉₊ + 2) * (((4 * E * d : ℕ) : ℝ) * X)⁻¹ ∧
      ((dyadicSet (h₀ E d X K η)).card : ℝ) ≤ C * Real.log (((4 * E * d : ℕ) : ℝ) * X) := by
  classical
  obtain ⟨Cc, hCc⟩ := poisson_c hη Cν
  refine ⟨max Cc (8 + 2 * (1 + η) / Real.log 2), fun E H d κ Δ X K ψ₁ ψ₂ hH => ?_⟩
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hd0 : 0 < d := hH.hd.pos
  have hH0 : 0 < H := hH.hH
  have hX1 : 1 ≤ X := by
    refine le_trans ?_ hH.hX
    rw [Real.one_le_sqrt]
    have : 1 ≤ E * H := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hX : 0 < X := by linarith
  have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  set k := ⌈4 / η⌉₊ + 2
  set Q : ℝ := ((4 * E * d : ℕ) : ℝ) * X with hQ
  have hq48 : (48 : ℝ) ≤ ((4 * E * d : ℕ) : ℝ) := by
    have hE4 : 4 ≤ E := by rcases hH.hE with h | h <;> omega
    have : 48 ≤ 4 * E * d := by have := hH.hd3; nlinarith
    exact_mod_cast this
  have hQ48 : 48 ≤ Q := by rw [hQ]; nlinarith
  have hQpos : 0 < Q := by linarith
  have hΔ : 0 ≤ Δ := le_trans zero_le_one hH.hΔ
  set h0 := h₀ E d X K η with hh0
  have hh0pos : 0 < h0 := by rw [hh0]; unfold h₀; positivity
  constructor
  · -- the error term
    set W : ℤ → ℂ := fun h => Wh E H d κ X K ψ₁ ψ₂ h with hW
    obtain ⟨hsumm, hhas⟩ := poisson_a hH
    set F : ℤ → ℂ := Set.indicator {h : ℤ | h ≠ 0} W with hF
    have hFsum : HasSum F (Xi E H d κ X K ψ₁ ψ₂) :=
      (hasSum_subtype_iff_indicator (s := {h : ℤ | h ≠ 0})).1 hhas
    have hF0 : F 0 = 0 := by simp [hF]
    have hFn : ∀ n : ℤ, n ≠ 0 → F n = W n := fun n hn => by simp [hF, hn]
    -- the sum over `n ≥ 1` of `G(n) = F(n) + F(-n)`
    set G : ℕ → ℂ := fun n => F n + F (-n) with hG
    have hGsum : HasSum G (Xi E H d κ X K ψ₁ ψ₂) := by
      have := hFsum.nat_add_neg
      rw [hF0, add_zero] at this
      exact this
    have hG0 : G 0 = 0 := by simp [hG, hF0]
    -- `Ξ_M(ψ₂) + Ξ_M(ψ₂⁻) = ∑_n ψ₀(n/M) G(n)`
    have hT : ∀ M ∈ dyadicSet h0, HasSum (fun n : ℕ => (ψ₀.ψ₀ (n / M) : ℂ) * G n)
        (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M) := by
      intro M hM
      have hMpos : 0 < M := by
        unfold dyadicSet at hM
        rw [Finset.mem_filter, Finset.mem_image] at hM
        obtain ⟨⟨j, -, rfl⟩, -⟩ := hM
        positivity
      have hsupp : ∀ n ∉ Finset.Icc 1 ⌊2 * M⌋₊, (ψ₀.ψ₀ (n / M) : ℂ) * G n = 0 := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        by_cases hn0 : n = 0
        · rw [hn0, hG0, mul_zero]
        · have : ψ₀.ψ₀ (n / M) = 0 := by
            by_contra hne
            obtain ⟨-, h2⟩ := ψ₀.support _ hne
            rw [div_le_iff₀ hMpos] at h2
            exact hn ⟨Nat.one_le_iff_ne_zero.2 hn0, Nat.le_floor (by linarith)⟩
          rw [this]; simp
      have hfin : HasSum (fun n : ℕ => (ψ₀.ψ₀ (n / M) : ℂ) * G n)
          (∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, (ψ₀.ψ₀ (n / M) : ℂ) * G n) :=
        hasSum_sum_of_ne_finset_zero hsupp
      convert hfin using 1
      unfold XiM
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn0 : (n : ℤ) ≠ 0 := by have := hn.1; omega
      have hnn : (-(n : ℤ)) ≠ 0 := by omega
      simp only [hG, hFn _ hn0, hFn _ hnn, hW, Wh_neg]
      ring
    have hwG : HasSum (fun n : ℕ => (∑ M ∈ dyadicSet h0, (ψ₀.ψ₀ (n / M) : ℂ)) * G n)
        (∑ M ∈ dyadicSet h0, (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M +
          XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M)) := by
      simp_rw [Finset.sum_mul]
      exact hasSum_sum hT
    have hdiff := hGsum.sub hwG
    -- the comparison function `b(h) = |W_h| 1_{|h| > h₀}`
    set b : ℤ → ℝ := Set.indicator {h : ℤ | h0 < |(h : ℝ)|} (fun h => ‖W h‖) with hb
    have hbsumm : Summable b := by
      have h1 : Summable (Set.indicator {h : ℤ | h ≠ 0} (fun h => ‖W h‖)) :=
        (summable_subtype_iff_indicator (s := {h : ℤ | h ≠ 0})).1 hsumm
      refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) h1
      · exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
      · by_cases hh : h0 < |(h : ℝ)|
        · have hne : h ≠ 0 := by rintro rfl; simp at hh; linarith
          rw [hb, Set.indicator_of_mem (show h ∈ {h : ℤ | h0 < |(h : ℝ)|} from hh),
            Set.indicator_of_mem (show h ∈ {h : ℤ | h ≠ 0} from hne)]
        · rw [hb, Set.indicator_of_notMem (show h ∉ {h : ℤ | h0 < |(h : ℝ)|} from hh)]
          exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    have hb0 : b 0 = 0 := by
      rw [hb, Set.indicator_of_notMem]; simp; linarith
    have hbsum := hbsumm.hasSum.nat_add_neg
    rw [hb0, add_zero] at hbsum
    have hbound := hdiff.norm_le_of_bounded hbsum (fun n => ?_)
    · have htsum : ∑' h : ℤ, b h ≤ Cc * Δ ^ k * Q⁻¹ := by
        rw [hb, ← tsum_subtype]
        exact hCc E H d κ Δ X K ψ₁ ψ₂ hH
      calc _ ≤ ∑' h : ℤ, b h := by rw [sub_eq_add_neg] at hbound ⊢; exact hbound
        _ ≤ Cc * Δ ^ k * Q⁻¹ := htsum
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · -- the pointwise bound `|(1 - w(n)) G(n)| ≤ b(n) + b(-n)`
      have hb_nn : ∀ h, 0 ≤ b h := fun h => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
      rw [← one_sub_mul, norm_mul]
      by_cases hn0 : n = 0
      · rw [hn0, hG0, norm_zero, mul_zero]; exact add_nonneg (hb_nn _) (hb_nn _)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0
      by_cases hnh : (n : ℝ) ≤ h0
      · have := dyadic_weight_eq_one ψ₀ hn1 hnh
        have e : (∑ M ∈ dyadicSet h0, (ψ₀.ψ₀ (n / M) : ℂ)) = 1 := by
          rw [← Complex.ofReal_sum, this, Complex.ofReal_one]
        rw [e, sub_self, norm_zero, zero_mul]; exact add_nonneg (hb_nn _) (hb_nn _)
      · push Not at hnh
        have hw0 := dyadic_weight_nonneg ψ₀ h0 n
        have hw1 := dyadic_weight_le_one ψ₀ h0 (t := n) (by linarith)
        have e : ‖1 - (∑ M ∈ dyadicSet h0, (ψ₀.ψ₀ (n / M) : ℂ))‖ ≤ 1 := by
          rw [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_le]
          constructor <;> linarith
        have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
        have hbn : b n = ‖W n‖ := by
          rw [hb, Set.indicator_of_mem]
          show h0 < |((n : ℤ) : ℝ)|
          rw [Int.cast_natCast, abs_of_nonneg (by positivity)]; exact hnh
        have hbn' : b (-n) = ‖W (-n)‖ := by
          rw [hb, Set.indicator_of_mem]
          show h0 < |((-(n : ℤ) : ℤ) : ℝ)|
          rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (by positivity)]; exact hnh
        rw [hbn, hbn']
        calc ‖1 - (∑ M ∈ dyadicSet h0, (ψ₀.ψ₀ (n / M) : ℂ))‖ * ‖G n‖ ≤ 1 * ‖G n‖ :=
              mul_le_mul_of_nonneg_right e (norm_nonneg _)
          _ = ‖F n + F (-n)‖ := one_mul _
          _ ≤ ‖F n‖ + ‖F (-n)‖ := norm_add_le _ _
          _ = ‖W n‖ + ‖W (-n)‖ := by
              rw [hFn _ hnz, hFn _ (by omega)]
  · -- the number of dyadic pieces
    have hlogQ : 1 ≤ Real.log Q := by
      rw [Real.le_log_iff_exp_le hQpos]
      have := Real.exp_one_lt_three
      linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    -- `h₀ ≤ Q^(1+η)`
    have hh0le : h0 ≤ Q ^ (1 + η) := by
      rw [hh0]; unfold h₀
      rw [Real.rpow_add hQpos, Real.rpow_one, ← hQ]
      rw [mul_div_assoc, mul_comm (Q ^ η)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_iff₀ hX]
      have := hH.hKq
      rw [← hQ] at this
      nlinarith
    have hlogh : Real.log (2 * h0) ≤ Real.log 2 + (1 + η) * Real.log Q := by
      rw [Real.log_mul two_ne_zero hh0pos.ne', ← Real.log_rpow hQpos]
      have := Real.log_le_log hh0pos hh0le
      linarith
    refine (card_dyadicSet_le h0).trans ?_
    have hC : 0 ≤ 8 + 2 * (1 + η) / Real.log 2 := by positivity
    apply max_le
    · calc 2 * (Real.log (2 * h0) / Real.log 2) + 6
          ≤ 2 * ((Real.log 2 + (1 + η) * Real.log Q) / Real.log 2) + 6 := by gcongr
        _ = 8 + 2 * (1 + η) / Real.log 2 * Real.log Q := by field_simp; ring
        _ ≤ (8 + 2 * (1 + η) / Real.log 2) * Real.log Q := by nlinarith
        _ ≤ max Cc (8 + 2 * (1 + η) / Real.log 2) * Real.log Q := by
            gcongr; exact le_max_right _ _
    · exact mul_nonneg (le_trans hC (le_max_right _ _)) (by linarith)

end Dyadic

end Triples
