import TriplesFinal.Analysis.MeasureTools
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Abstract spectral families

The proof of Theorem 6.1 treats the discrete spectrum (the Maass forms `u_j`) and the continuous
spectrum (the Eisenstein series `E_𝔰(·, 1/2 + ir)`) in the same way. We formalize this with an
abstract **spectral family**: a measure space `(Ω, ν)` of spectral points `x`, with a spectral
parameter `t(x) ∈ ℝ ∪ i(0, 1/2)`, Fourier coefficients `ρ(x, n)` and Heegner sums `U(x)`. The
discrete spectrum is the counting measure on the index set of the `u_j`; the continuous spectrum
is `(1/4π) dr` on `{cusps} × ℝ`.

The hypotheses on a family are the large sieve inequality (Lemma 10.2, `SpecFam.LS`), the Heegner
side (Lemma 10.7, `SpecFam.HS`), and the large sieve inequalities for the exceptional spectrum
(Lemma 10.5 for part (a), `SpecFam.ExcA`; Lemma 10.3 for part (b), `SpecFam.ExcB`).
-/

namespace Triples

open MeasureTheory
open scoped ContDiff

/-- An abstract spectral family. -/
structure SpecFam where
  /-- the spectral points -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the spectral measure -/
  ν : Measure Ω
  /-- the spectral parameter -/
  t : Ω → ℂ
  /-- the Fourier coefficients at `∞` -/
  ρ : Ω → ℕ → ℂ
  /-- the Heegner sums `U(x) = ∑_i u_x(z_i)` -/
  U : Ω → ℂ
  meas_t : Measurable t
  meas_ρ : ∀ n, Measurable fun x => ρ x n
  meas_U : Measurable U
  t_mem : ∀ x, (t x).im = 0 ∨ ((t x).re = 0 ∧ 0 < (t x).im ∧ (t x).im < 1 / 2)
  finite_ball : ∀ T : ℝ, ν {x | ‖t x‖ ≤ T} ≠ ⊤
  intρ : ∀ (n : ℕ) (T : ℝ), IntegrableOn (fun x => ‖ρ x n‖ ^ 2) {x | ‖t x‖ ≤ T} ν
  intU : ∀ T : ℝ, IntegrableOn (fun x => ‖U x‖ ^ 2) {x | ‖t x‖ ≤ T} ν
  /-- `cosh(πt)` is bounded below (for the exceptional spectrum this is `θ_j ≤ θ < 1/2`) -/
  ch_lb : ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ (Complex.cosh (Real.pi * t x)).re

attribute [instance] SpecFam.mΩ

namespace SpecFam

variable (F : SpecFam)

/-- The ball `{x : ‖t(x)‖ ≤ T}`. -/
def ball (T : ℝ) : Set F.Ω := {x | ‖F.t x‖ ≤ T}

/-- The exceptional points `{x : Im t(x) > 0}`. -/
def exc : Set F.Ω := {x | 0 < (F.t x).im}

theorem measurableSet_ball (T : ℝ) : MeasurableSet (F.ball T) :=
  measurableSet_le F.meas_t.norm measurable_const

theorem measurableSet_exc : MeasurableSet F.exc :=
  measurableSet_lt measurable_const (Complex.measurable_im.comp F.meas_t)

theorem exc_subset_ball {T : ℝ} (hT : 1 / 2 ≤ T) : F.exc ⊆ F.ball T := by
  intro x hx
  have hx' : 0 < (F.t x).im := hx
  rcases F.t_mem x with h | ⟨hre, _, hlt⟩
  · linarith
  · show ‖F.t x‖ ≤ T
    have : F.t x = Complex.I * ((F.t x).im : ℂ) := Complex.ext (by simp [hre]) (by simp)
    rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx']
    linarith

/-- A spectral point is real or exceptional. -/
theorem real_of_not_exc {x : F.Ω} (h : x ∉ F.exc) : (F.t x).im = 0 := by
  rcases F.t_mem x with h' | ⟨_, hpos, _⟩
  · exact h'
  · exact absurd hpos h

theorem eq_re_of_not_exc {x : F.Ω} (h : x ∉ F.exc) : F.t x = ((F.t x).re : ℂ) :=
  Complex.ext (by simp) (by simp [F.real_of_not_exc h])

theorem im_nonneg (x : F.Ω) : 0 ≤ (F.t x).im := by
  rcases F.t_mem x with h | ⟨_, h, _⟩ <;> linarith

theorem im_lt_half (x : F.Ω) : (F.t x).im < 1 / 2 := by
  rcases F.t_mem x with h | ⟨_, _, h⟩ <;> linarith

theorem abs_im_le_half (x : F.Ω) : |(F.t x).im| ≤ 1 / 2 := by
  rw [abs_of_nonneg (F.im_nonneg x)]; exact (F.im_lt_half x).le

theorem norm_eq_abs_re_of_not_exc {x : F.Ω} (h : x ∉ F.exc) : ‖F.t x‖ = |(F.t x).re| := by
  rw [F.eq_re_of_not_exc h, Complex.norm_real, Real.norm_eq_abs]; simp

/-- A point outside the ball of radius `1/2` is real. -/
theorem not_exc_of_lt {x : F.Ω} {T : ℝ} (hT : 1 / 2 ≤ T) (h : T < ‖F.t x‖) : x ∉ F.exc :=
  fun hx => absurd (F.exc_subset_ball hT hx) (not_le.2 h)

/-- The weight `cosh(πt)` (its real part; it is `cos(πθ)` for `t = iθ`). -/
noncomputable def ch (x : F.Ω) : ℝ := (Complex.cosh (Real.pi * F.t x)).re

theorem measurable_ch : Measurable F.ch := by
  unfold ch
  exact Complex.measurable_re.comp (Complex.continuous_cosh.measurable.comp
    (measurable_const.mul F.meas_t))

theorem ch_of_not_exc {x : F.Ω} (h : x ∉ F.exc) : F.ch x = Real.cosh (Real.pi * (F.t x).re) := by
  unfold ch
  rw [F.eq_re_of_not_exc h]
  rw [show (Real.pi : ℂ) * (((F.t x).re : ℝ) : ℂ) = ((Real.pi * (F.t x).re : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh, Complex.ofReal_re]
  simp

theorem ch_of_exc {x : F.Ω} (h : x ∈ F.exc) : F.ch x = Real.cos (Real.pi * (F.t x).im) := by
  unfold ch
  have hx' : 0 < (F.t x).im := h
  rcases F.t_mem x with h0 | ⟨hre, _, _⟩
  · linarith
  · have : F.t x = Complex.I * ((F.t x).im : ℂ) := Complex.ext (by simp [hre]) (by simp)
    rw [this]
    rw [show (Real.pi : ℂ) * (Complex.I * (((F.t x).im : ℝ) : ℂ)) =
        ((Real.pi * (F.t x).im : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, Complex.ofReal_re]
    simp

theorem ch_pos (x : F.Ω) : 0 < F.ch x := by
  by_cases h : x ∈ F.exc
  · rw [F.ch_of_exc h]
    apply Real.cos_pos_of_mem_Ioo
    have h1 := F.im_nonneg x
    have h2 := F.im_lt_half x
    have hpi := Real.pi_pos
    constructor <;> nlinarith
  · rw [F.ch_of_not_exc h]; exact Real.cosh_pos _

/-- `cosh(πt) ≤ cosh(πT)` on the ball of radius `T ≥ 0`. -/
theorem ch_le {x : F.Ω} {T : ℝ} (hx : x ∈ F.ball T) : F.ch x ≤ Real.cosh (Real.pi * T) := by
  have hx' : ‖F.t x‖ ≤ T := hx
  by_cases h : x ∈ F.exc
  · rw [F.ch_of_exc h]
    exact (Real.cos_le_one _).trans (Real.one_le_cosh _)
  · rw [F.ch_of_not_exc h, Real.cosh_le_cosh]
    rw [F.norm_eq_abs_re_of_not_exc h] at hx'
    have hT : 0 ≤ T := le_trans (abs_nonneg _) hx'
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_left hx' Real.pi_pos.le

/-! ### The hypotheses -/

/-- **The large sieve inequality** (Lemma 10.2) for the family, at level `q`. -/
def LS (q : ℝ) (C : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ T : ℝ, 1 ≤ T → ∀ M : ℝ, 1 / 2 ≤ M → ∀ a : ℕ → ℂ,
    (∀ n, a n ≠ 0 → M < n ∧ (n : ℝ) ≤ 2 * M) →
    ∫ x in F.ball T, ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * F.ρ x n‖ ^ 2 / F.ch x ∂F.ν ≤
      C η * (T ^ 2 + M ^ (1 + η) / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2

/-- **The Heegner side** (Lemma 10.7) for the family, with pair count `P`. -/
def HS (P : ℝ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∫ x in F.ball T, ‖F.U x‖ ^ 2 ∂F.ν ≤ 256 / Real.pi * T ^ 2 * P

/-- **Pascadi's inequality with smooth weights** (Lemma 10.5) for the exceptional points. -/
def ExcA (q θ η C' : ℝ) : Prop :=
  ∀ (M Y LG CG : ℝ), 1 / 2 ≤ M → 1 ≤ Y → 1 ≤ LG → 0 < CG →
    ∀ G : ℝ → ℂ, ContDiff ℝ ∞ G → (∀ t, G t ≠ 0 → 1 ≤ t ∧ t ≤ 2) →
    (∀ k ≤ 3, ∀ t, ‖iteratedDeriv k G t‖ ≤ CG * LG ^ k) →
    ∫ x in F.exc, Y ^ (2 * (F.t x).im) *
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (n / M) * F.ρ x n‖ ^ 2 ∂F.ν ≤
      C' * CG ^ 2 * LG ^ 3 * (q * M) ^ η * (1 + Y / max M q) ^ (2 * θ) * (1 + M / q) * M

/-- **The large sieve inequality for the exceptional spectrum** (Lemma 10.3). -/
def ExcB (q η C : ℝ) : Prop :=
  ∀ M : ℝ, 1 / 2 ≤ M → ∀ Y : ℝ, 1 ≤ Y → Y ≤ max 1 (q / M) → ∀ a : ℕ → ℂ,
    (∀ n, a n ≠ 0 → M < n ∧ (n : ℝ) ≤ 2 * M) →
    ∫ x in F.exc, Y ^ (2 * (F.t x).im) *
        ‖∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, a n * F.ρ x n‖ ^ 2 ∂F.ν ≤
      C * (q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2

/-- The exceptional parameters are at most `θ`. -/
def ExcBound (θ : ℝ) : Prop := ∀ x, 0 < (F.t x).im → (F.t x).im ≤ θ

/-! ### Integrability -/

theorem sq_norm_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ n ∈ S, f n‖ ^ 2 ≤ S.card * ∑ n ∈ S, ‖f n‖ ^ 2 := by
  have h1 : ‖∑ n ∈ S, f n‖ ≤ ∑ n ∈ S, ‖f n‖ := norm_sum_le _ _
  have h2 : (∑ n ∈ S, ‖f n‖) ^ 2 ≤ S.card * ∑ n ∈ S, ‖f n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖f n‖)
    simpa using this
  calc ‖∑ n ∈ S, f n‖ ^ 2 ≤ (∑ n ∈ S, ‖f n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- `x ↦ ∑_{n ∈ S} ‖ρ(x, n)‖²` is integrable on balls. -/
theorem integrableOn_sum_sq_ρ (S : Finset ℕ) (T : ℝ) :
    IntegrableOn (fun x => ∑ n ∈ S, ‖F.ρ x n‖ ^ 2) (F.ball T) F.ν :=
  integrable_finsetSum _ fun n _ => F.intρ n T

/-- `x ↦ ‖∑_{n ∈ S} c(x, n) ρ(x, n)‖²` is integrable on balls for bounded measurable `c`. -/
theorem integrableOn_sq_sum (S : Finset ℕ) {c : F.Ω → ℕ → ℂ}
    (hc : ∀ n, Measurable fun x => c x n) {B : ℝ} (hB : ∀ x n, ‖c x n‖ ≤ B) (T : ℝ) :
    IntegrableOn (fun x => ‖∑ n ∈ S, c x n * F.ρ x n‖ ^ 2) (F.ball T) F.ν := by
  have hdom : IntegrableOn (fun x => S.card * (B ^ 2 * ∑ n ∈ S, ‖F.ρ x n‖ ^ 2)) (F.ball T) F.ν :=
    ((F.integrableOn_sum_sq_ρ S T).const_mul _).const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have : Measurable fun x => ‖∑ n ∈ S, c x n * F.ρ x n‖ ^ 2 :=
      (Finset.measurable_sum _ fun n _ => (hc n).mul (F.meas_ρ n)).norm.pow_const 2
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine (sq_norm_sum_le S _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [norm_mul, mul_pow]
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB x n)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB x n) 2)
      (sq_nonneg _)

/-- With a bounded measurable weight. -/
theorem integrableOn_weight_sq_sum (S : Finset ℕ) {c : F.Ω → ℕ → ℂ}
    (hc : ∀ n, Measurable fun x => c x n) {B : ℝ} (hB : ∀ x n, ‖c x n‖ ≤ B) (T : ℝ)
    {w : F.Ω → ℝ} (hw : Measurable w) {W : ℝ} (hW : ∀ x ∈ F.ball T, ‖w x‖ ≤ W) :
    IntegrableOn (fun x => w x * ‖∑ n ∈ S, c x n * F.ρ x n‖ ^ 2) (F.ball T) F.ν := by
  have h := F.integrableOn_sq_sum S hc hB T
  refine (h.const_mul W).mono' (hw.aestronglyMeasurable.mul h.1) ?_
  refine (ae_restrict_iff' (F.measurableSet_ball T)).2 (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_right (hW x hx) (sq_nonneg _)

theorem integrableOn_sq_U (T : ℝ) : IntegrableOn (fun x => ‖F.U x‖ ^ 2) (F.ball T) F.ν :=
  F.intU T

theorem finite_ball' (T : ℝ) : F.ν (F.ball T) < ⊤ := (F.finite_ball T).lt_top

/-- `f/cosh(πt)` is integrable when `f` is. -/
theorem integrableOn_div_ch {S : Set F.Ω} {f : F.Ω → ℝ} (hf : IntegrableOn f S F.ν) :
    IntegrableOn (fun x => f x / F.ch x) S F.ν := by
  obtain ⟨c, hc, hcx⟩ := F.ch_lb
  have hm : AEStronglyMeasurable (fun x => f x / F.ch x) (F.ν.restrict S) :=
    hf.1.div₀ F.measurable_ch.aestronglyMeasurable
  refine (hf.norm.const_mul c⁻¹).mono' hm (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (F.ch_pos x), Real.norm_eq_abs]
  calc |f x| / F.ch x ≤ |f x| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc (hcx x)
    _ = c⁻¹ * |f x| := by rw [div_eq_inv_mul]

end SpecFam

end Triples
