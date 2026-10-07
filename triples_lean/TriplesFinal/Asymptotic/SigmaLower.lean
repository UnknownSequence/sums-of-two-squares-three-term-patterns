import TriplesFinal.Asymptotic.Formula
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theorem 4.3: the lower bound for `Σ_d(x)`

Let `0 < ϖ < ϖ_θ = (1 - 2θ)/(5 - 6θ)`. There is `ε₀ > 0` such that for `0 < ε ≤ ε₀` and
`x ≥ x₀(a, b, ϖ, ε)`, `Σ_d(x) ≫_ε x^(1/2) d^(-1/2-ε)` for every good prime `d ≤ x^ϖ`.
With Theorem 6.1(b), the same holds for `0 < ϖ < ϖ'_θ = (1 - 2θ)/(5 - 4θ)`.

This follows from Proposition 7.1 and Lemma 5.3(d): the main term is `≫ x^(1/2) d^(-1/2-ε)`,
and the error terms are smaller by a factor `x^(-1/4+ε) d^(1+2ε) + x^(-1/4+θ/2+ε) d^(5/4-3θ/2+ε)`,
which is `o(1)` for `d ≤ x^ϖ` and `ε` small.

Paper: §4, Theorem 4.3; proof at the end of §7.
-/

namespace Triples

open Filter Topology

/-- `ϖ_θ = (1 - 2θ)/(5 - 6θ)`. -/
noncomputable def varpiA (θ : ℝ) : ℝ := (1 - 2 * θ) / (5 - 6 * θ)

/-- `ϖ'_θ = (1 - 2θ)/(5 - 4θ)`. -/
noncomputable def varpiB (θ : ℝ) : ℝ := (1 - 2 * θ) / (5 - 4 * θ)

/-- For `α < 0` and `δ > 0`, `x^α ≤ δ` for all large `x`. -/
theorem exists_rpow_le {α δ : ℝ} (hα : α < 0) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → x ^ α ≤ δ := by
  have h := tendsto_rpow_neg_atTop (y := -α) (by linarith)
  rw [neg_neg] at h
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (h.eventually (ge_mem_nhds hδ))
  exact ⟨max x₀ 1, by positivity, fun x hx => hx₀ x (le_trans (le_max_left _ _) hx)⟩

/-- The deduction of a lower bound from an asymptotic formula (the proof of Theorem 4.3). -/
theorem lower_of_asymptotic {good : ℕ → Prop} {S M : ℕ → ℝ → ℝ} {C c₁ ϖ θ β ε x₁ : ℝ}
    (hc₁ : 0 < c₁) (_hϖ0 : 0 ≤ ϖ) (hϖ4 : ϖ ≤ 1 / 4)
    (h1 : -1 / 4 + ε + ϖ * (1 + 2 * ε) < 0)
    (h2 : -1 / 4 + θ / 2 + ε + ϖ * (β + 1 / 2 + ε) < 0)
    (hε : 0 ≤ ε) (hβ : 0 ≤ β + 1 / 2 + ε)
    (hasym : ∀ x : ℝ, x₁ ≤ x → ∀ d : ℕ, good d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |S d x - M d x| ≤ C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
        x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β))
    (hmain : ∀ x : ℝ, 1 ≤ x → ∀ d : ℕ, good d → 1 ≤ d →
      c₁ * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤ M d x) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, good d → 1 ≤ d → (d : ℝ) ≤ x ^ ϖ →
      c₁ / 2 * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤ S d x := by
  set α₁ := -1 / 4 + ε + ϖ * (1 + 2 * ε) with hα₁
  set α₂ := -1 / 4 + θ / 2 + ε + ϖ * (β + 1 / 2 + ε) with hα₂
  set δ := c₁ / (4 * (|C| + 1)) with hδ
  have hC1 : 0 < |C| + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  obtain ⟨y₁, -, hy₁⟩ := exists_rpow_le h1 hδ0
  obtain ⟨y₂, -, hy₂⟩ := exists_rpow_le h2 hδ0
  refine ⟨max (max x₁ 1) (max y₁ y₂), fun x hx d hd hd1 hdx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxy₁ : y₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxy₂ : y₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd14 : (d : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    hdx.trans (Real.rpow_le_rpow_of_exponent_le hx1 hϖ4)
  have hA := hasym x hxx₁ d hd hd14
  have hM := hmain x hx1 d hd hd1
  set X := x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) with hX
  have hX0 : 0 < X := by positivity
  have hd_pow : ∀ e : ℝ, 0 ≤ e → (d : ℝ) ^ e ≤ x ^ (ϖ * e) := by
    intro e he
    calc (d : ℝ) ^ e ≤ (x ^ ϖ) ^ e := Real.rpow_le_rpow hdpos.le hdx he
      _ = x ^ (ϖ * e) := by rw [← Real.rpow_mul hxpos.le]
  -- the first error term
  have hT1 : x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) ≤ X * x ^ α₁ := by
    have e1 : X * (x ^ (-1 / 4 + ε) * (d : ℝ) ^ (1 + 2 * ε)) =
        x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) := by
      rw [hX]
      calc x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) * (x ^ (-1 / 4 + ε) * (d : ℝ) ^ (1 + 2 * ε))
          = (x ^ (1 / 2 : ℝ) * x ^ (-1 / 4 + ε)) *
              ((d : ℝ) ^ (-1 / 2 - ε) * (d : ℝ) ^ (1 + 2 * ε)) := by ring
        _ = x ^ ((1 / 2 : ℝ) + (-1 / 4 + ε)) * (d : ℝ) ^ ((-1 / 2 - ε) + (1 + 2 * ε)) := by
            rw [← Real.rpow_add hxpos, ← Real.rpow_add hdpos]
        _ = x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) := by ring_nf
    rw [← e1]
    have : x ^ (-1 / 4 + ε) * (d : ℝ) ^ (1 + 2 * ε) ≤ x ^ α₁ := by
      calc x ^ (-1 / 4 + ε) * (d : ℝ) ^ (1 + 2 * ε)
          ≤ x ^ (-1 / 4 + ε) * x ^ (ϖ * (1 + 2 * ε)) := by
            gcongr
            exact hd_pow _ (by linarith)
        _ = x ^ α₁ := by rw [← Real.rpow_add hxpos, hα₁]; try ring_nf
    exact mul_le_mul_of_nonneg_left this hX0.le
  -- the second error term
  have hT2 : x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β ≤ X * x ^ α₂ := by
    have e2 : X * (x ^ (-1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (β + 1 / 2 + ε)) =
        x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β := by
      rw [hX]
      calc x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) *
            (x ^ (-1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (β + 1 / 2 + ε))
          = (x ^ (1 / 2 : ℝ) * x ^ (-1 / 4 + θ / 2 + ε)) *
              ((d : ℝ) ^ (-1 / 2 - ε) * (d : ℝ) ^ (β + 1 / 2 + ε)) := by ring
        _ = x ^ ((1 / 2 : ℝ) + (-1 / 4 + θ / 2 + ε)) *
              (d : ℝ) ^ ((-1 / 2 - ε) + (β + 1 / 2 + ε)) := by
            rw [← Real.rpow_add hxpos, ← Real.rpow_add hdpos]
        _ = x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β := by ring_nf
    rw [← e2]
    have : x ^ (-1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (β + 1 / 2 + ε) ≤ x ^ α₂ := by
      calc x ^ (-1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (β + 1 / 2 + ε)
          ≤ x ^ (-1 / 4 + θ / 2 + ε) * x ^ (ϖ * (β + 1 / 2 + ε)) := by
            gcongr
            exact hd_pow _ hβ
        _ = x ^ α₂ := by rw [← Real.rpow_add hxpos, hα₂]; try ring_nf
    exact mul_le_mul_of_nonneg_left this hX0.le
  -- combine
  have hx₁le := hy₁ x hxy₁
  have hx₂le := hy₂ x hxy₂
  have herr : |S d x - M d x| ≤ c₁ / 2 * X := by
    calc |S d x - M d x|
        ≤ C * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
            x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β) := hA
      _ ≤ |C| * (X * x ^ α₁ + X * x ^ α₂) := by
          have h0 : 0 ≤ x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
              x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β := by positivity
          calc C * _ ≤ |C| * (x ^ (1 / 4 + ε) * (d : ℝ) ^ (1 / 2 + ε) +
                x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ β) :=
                mul_le_mul_of_nonneg_right (le_abs_self C) h0
            _ ≤ |C| * (X * x ^ α₁ + X * x ^ α₂) := by
                gcongr
      _ ≤ |C| * (X * δ + X * δ) := by gcongr
      _ = X * (2 * |C| * δ) := by ring
      _ ≤ X * (c₁ / 2) := by
          apply mul_le_mul_of_nonneg_left _ hX0.le
          rw [hδ]
          rw [show 2 * |C| * (c₁ / (4 * (|C| + 1))) = c₁ / 2 * (|C| / (|C| + 1)) by
            field_simp; ring]
          have : |C| / (|C| + 1) ≤ 1 := by
            rw [div_le_one hC1]; linarith
          nlinarith
      _ = c₁ / 2 * X := by ring
  have := (abs_le.1 herr).1
  calc c₁ / 2 * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) = c₁ * X - c₁ / 2 * X := by rw [hX]; ring
    _ ≤ M d x - c₁ / 2 * X := by
        have : c₁ * X ≤ M d x := by rw [hX, ← mul_assoc]; exact hM
        linarith
    _ ≤ S d x := by linarith

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- The main term of Proposition 7.1 is `≥ c₁ x^(1/2) d^(-1/2-ε)` (by Lemma 5.3(d)). -/
theorem main_lower (hA : ArithmeticAssumptions) (F : Cutoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ x : ℝ, 1 ≤ x → ∀ d : ℕ, P.IsGood d → 1 ≤ d →
      c₁ * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤
        32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d) := by
  obtain ⟨c, hc, hL⟩ := P.Ld_lower hA hε
  have hcF := F.cF_pos
  refine ⟨32 * F.cF * c / 2 ^ P.j, by positivity, fun x hx d hd hd1 => ?_⟩
  have hxpos : 0 < x := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsqrt : Real.sqrt (x / d) = x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hxpos.le hdpos.le, div_eq_mul_inv,
      ← Real.rpow_neg hdpos.le]
    norm_num
  have hdε : (d : ℝ) ^ (-1 / 2 - ε) = (d : ℝ) ^ (-ε) * (d : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add hdpos]; ring_nf
  rw [hsqrt, hdε]
  have hLd := hL d hd
  have h2 : (0 : ℝ) < 2 ^ P.j := by positivity
  have hx12 : 0 < x ^ (1 / 2 : ℝ) := by positivity
  have hd12 : 0 < (d : ℝ) ^ (-1 / 2 : ℝ) := by positivity
  calc 32 * F.cF * c / 2 ^ P.j * x ^ (1 / 2 : ℝ) * ((d : ℝ) ^ (-ε) * (d : ℝ) ^ (-1 / 2 : ℝ))
      = 32 * F.cF / 2 ^ P.j * (c * (d : ℝ) ^ (-ε)) * (x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 : ℝ)) := by
        ring
    _ ≤ 32 * F.cF / 2 ^ P.j * P.Ld d * (x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 : ℝ)) := by
        gcongr
    _ = 32 * F.cF * P.Ld d / 2 ^ P.j * (x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 : ℝ)) := by ring

/-- `ϖ_θ ≤ 1/5`. -/
theorem varpiA_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) : varpiA θ ≤ 1 / 5 := by
  unfold varpiA
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- `ϖ'_θ ≤ 1/5`. -/
theorem varpiB_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) : varpiB θ ≤ 1 / 5 := by
  unfold varpiB
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Theorem 4.3** (with Theorem 6.1(a)). -/
theorem sigma_lower_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsAt θ)
    (F : Cutoff) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ : ϖ < varpiA θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ ϖ →
        c * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤ P.Sigma F.F d x := by
  have hϖ5 : ϖ < 1 / 5 := lt_of_lt_of_le hϖ (varpiA_le hθ0 hθ)
  -- `ϖ (5/4 - 3θ/2) < 1/4 - θ/2`
  have hkey : ϖ * (5 / 4 - 3 * θ / 2) < 1 / 4 - θ / 2 := by
    have h56 : 0 < 5 - 6 * θ := by linarith
    unfold varpiA at hϖ
    rw [lt_div_iff₀ h56] at hϖ
    linarith
  set g₁ := (1 / 4 - ϖ) / (2 * (1 + 2 * ϖ)) with hg₁
  set g₂ := (1 / 4 - θ / 2 - ϖ * (5 / 4 - 3 * θ / 2)) / (2 * (1 + ϖ)) with hg₂
  have hg₁0 : 0 < g₁ := by apply div_pos <;> linarith
  have hg₂0 : 0 < g₂ := by apply div_pos <;> linarith
  refine ⟨min (1 / 200) (min g₁ g₂), by positivity, fun ε hε hεle => ?_⟩
  have hε200 : ε ≤ 1 / 200 := le_trans hεle (min_le_left _ _)
  have hεg₁ : ε ≤ g₁ := le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεg₂ : ε ≤ g₂ := le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨C, x₁, hasym⟩ := P.asymptotic_a hθ0 hθ hA F hε (by linarith)
  obtain ⟨c₁, hc₁, hmain⟩ := P.main_lower hA.arith F hε
  have h1 : -1 / 4 + ε + ϖ * (1 + 2 * ε) < 0 := by
    have : ε * (2 * (1 + 2 * ϖ)) ≤ 1 / 4 - ϖ := by
      rw [hg₁] at hεg₁; rwa [le_div_iff₀ (by linarith)] at hεg₁
    nlinarith
  have h2 : -1 / 4 + θ / 2 + ε + ϖ * ((3 / 4 - 3 * θ / 2) + 1 / 2 + ε) < 0 := by
    have : ε * (2 * (1 + ϖ)) ≤ 1 / 4 - θ / 2 - ϖ * (5 / 4 - 3 * θ / 2) := by
      rw [hg₂] at hεg₂; rwa [le_div_iff₀ (by linarith)] at hεg₂
    nlinarith
  obtain ⟨x₀, hx₀⟩ := lower_of_asymptotic (good := P.IsGood) (S := fun d x => P.Sigma F.F d x)
    (M := fun d x => 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d))
    hc₁ hϖ0.le (by linarith) h1 h2 hε.le (by linarith) hasym hmain
  refine ⟨c₁ / 2, by positivity, x₀, fun x hx d hd hdx => ?_⟩
  exact hx₀ x hx d hd hd.prime.one_lt.le hdx

/-- **Theorem 4.3** (with Theorem 6.1(b); without Pascadi's inequality). -/
theorem sigma_lower_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsDIAt θ)
    (F : Cutoff) {ϖ : ℝ} (hϖ0 : 0 < ϖ) (hϖ : ϖ < varpiB θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ ϖ →
        c * x ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-1 / 2 - ε) ≤ P.Sigma F.F d x := by
  have hϖ5 : ϖ < 1 / 5 := lt_of_lt_of_le hϖ (varpiB_le hθ0 hθ)
  have hkey : ϖ * (5 / 4 - θ) < 1 / 4 - θ / 2 := by
    have h54 : 0 < 5 - 4 * θ := by linarith
    unfold varpiB at hϖ
    rw [lt_div_iff₀ h54] at hϖ
    linarith
  set g₁ := (1 / 4 - ϖ) / (2 * (1 + 2 * ϖ)) with hg₁
  set g₂ := (1 / 4 - θ / 2 - ϖ * (5 / 4 - θ)) / (2 * (1 + ϖ)) with hg₂
  have hg₁0 : 0 < g₁ := by apply div_pos <;> linarith
  have hg₂0 : 0 < g₂ := by apply div_pos <;> linarith
  refine ⟨min (1 / 200) (min g₁ g₂), by positivity, fun ε hε hεle => ?_⟩
  have hε200 : ε ≤ 1 / 200 := le_trans hεle (min_le_left _ _)
  have hεg₁ : ε ≤ g₁ := le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεg₂ : ε ≤ g₂ := le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨C, x₁, hasym⟩ := P.asymptotic_b hθ0 hθ hA F hε (by linarith)
  obtain ⟨c₁, hc₁, hmain⟩ := P.main_lower hA.arith F hε
  have h1 : -1 / 4 + ε + ϖ * (1 + 2 * ε) < 0 := by
    have : ε * (2 * (1 + 2 * ϖ)) ≤ 1 / 4 - ϖ := by
      rw [hg₁] at hεg₁; rwa [le_div_iff₀ (by linarith)] at hεg₁
    nlinarith
  have h2 : -1 / 4 + θ / 2 + ε + ϖ * ((3 / 4 - θ) + 1 / 2 + ε) < 0 := by
    have : ε * (2 * (1 + ϖ)) ≤ 1 / 4 - θ / 2 - ϖ * (5 / 4 - θ) := by
      rw [hg₂] at hεg₂; rwa [le_div_iff₀ (by linarith)] at hεg₂
    nlinarith
  obtain ⟨x₀, hx₀⟩ := lower_of_asymptotic (good := P.IsGood) (S := fun d x => P.Sigma F.F d x)
    (M := fun d x => 32 * F.cF * P.Ld d / 2 ^ P.j * Real.sqrt (x / d))
    hc₁ hϖ0.le (by linarith) h1 h2 hε.le (by linarith) hasym hmain
  refine ⟨c₁ / 2, by positivity, x₀, fun x hx d hd hdx => ?_⟩
  exact hx₀ x hx d hd hd.prime.one_lt.le hdx

end PatternData

end Triples
