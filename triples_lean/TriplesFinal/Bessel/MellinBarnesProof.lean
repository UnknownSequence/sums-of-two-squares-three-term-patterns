import TriplesFinal.Bessel.GammaBounds
import TriplesFinal.Bessel.Continuity
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup


/-!
# Lemma 11.2: the Mellin–Barnes formula for `K_{it}`

For real `t ≠ 0` and `y > 0`,
`K_{it}(y) = ½ Γ(it) (y/2)^(-it) + ½ Γ(-it) (y/2)^(it) + (1/2π) ∫ G_t(-3/2 + iξ) y^(3/2 - iξ) dξ`.

The proof:
* **`Γ` in the strip** `-3/4 ≤ Re s ≤ 1/4`: by Phragmén–Lindelöf applied to
  `Γ(s+1) e^(-iπs/2)/(s+2)`, with Stirling's bound on `Re s = -3/4` (`StirlingBound`) on both
  boundary lines (via `Γ(s+1) = sΓ(s)`) and `|Γ(s)| ≤ Γ(Re s)` for the growth condition, one
  gets `|Γ(s)| ≪ e^(-π|Im s|/2)` for `|Im s| ≥ 1` (`norm_Gamma_strip`). Hence `G_t` decays in
  the strip `-3/2 ≤ Re w ≤ 1/2` (`norm_Gt_strip`) and is integrable on `Re w = 1/2`.
* **Mellin inversion** on `Re w = 1/2` (Mathlib's `mellinInv_mellin_eq`), using the Mellin
  transform of `K_{it}` (`BesselMellin`) and the continuity of `K_{it}`.
* **The contour shift** to `Re w = -3/2`: `G_t(w) y^(-w) = (2/(it)) (P(w)/(w - it) - P(w)/(w + it))`
  with `P(w) = 2^(w-2) Γ((w+it)/2 + 1) Γ((w-it)/2 + 1) y^(-w)` holomorphic on `Re w > -2`; the
  function `h = (2/(it)) (dslope P (it) - dslope P (-it))` is holomorphic there, Cauchy's theorem
  on rectangles and the decay on the horizontal sides give `∫_(1/2) h = ∫_(-3/2) h`, and the
  principal parts contribute `∫ (1/(1/2 + iu) - 1/(-3/2 + iu)) du = 2π` (computed with `arctan`
  and `log`). The residues `(2/(it)) P(±it)` are `½ Γ(±it) (y/2)^(∓it)`.

Paper: §11, Lemma 11.2.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

/-! ### Bounds for `Γ` in the strip `-3/4 ≤ Re s ≤ 1/4` -/

/-- `|Γ(s)| ≤ Γ(Re s)` for `Re s > 0`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx : (0 : ℝ) < x := hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

/-- `Γ(σ) ≤ Γ(1/4) + Γ(5/4)` for `1/4 ≤ σ ≤ 5/4`. -/
theorem Gamma_le_of_mem {σ : ℝ} (h1 : 1 / 4 ≤ σ) (h2 : σ ≤ 5 / 4) :
    Real.Gamma σ ≤ Real.Gamma (1 / 4) + Real.Gamma (5 / 4) := by
  have hc := Real.convexOn_Gamma
  have h : Real.Gamma ((5 / 4 - σ) • (1 / 4 : ℝ) + (σ - 1 / 4) • (5 / 4 : ℝ)) ≤
      (5 / 4 - σ) • Real.Gamma (1 / 4) + (σ - 1 / 4) • Real.Gamma (5 / 4) :=
    hc.2 (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0) (by norm_num : (5 / 4 : ℝ) ∈ Ioi 0)
      (by linarith) (by linarith) (by ring)
  simp only [smul_eq_mul] at h
  rw [show (5 / 4 - σ) * (1 / 4 : ℝ) + (σ - 1 / 4) * (5 / 4) = σ by ring] at h
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have g2 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 5 / 4)
  nlinarith

theorem differentiableAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have := congrArg Complex.re hm
  simp at this
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

theorem norm_exp_neg_I_pi (s : ℂ) :
    ‖Complex.exp (-(I * Real.pi * s / 2))‖ = Real.exp (Real.pi * s.im / 2) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

/-- **Phragmén–Lindelöf** for `Γ(s+1) e^(-iπs/2)/(s+2)` on `-3/4 ≤ Re s ≤ 1/4`. -/
theorem norm_Gamma_strip_aux (hS : StirlingBound) :
    ∃ C : ℝ, ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 1 / 4 →
      ‖Complex.Gamma (s + 1) * Complex.exp (-(I * Real.pi * s / 2)) / (s + 2)‖ ≤ C := by
  obtain ⟨CS, hCS⟩ := hS
  set f : ℂ → ℂ := fun s => Complex.Gamma (s + 1) * Complex.exp (-(I * Real.pi * s / 2)) / (s + 2)
    with hf
  have hdiff : DifferentiableOn ℂ f {s : ℂ | -1 < s.re} := by
    intro s hs
    have hs : -1 < s.re := hs
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div
    · apply DifferentiableAt.mul
      · exact (differentiableAt_Gamma_of_re_pos (s := s + 1) (by simp; linarith)).comp s
          (differentiableAt_id.add_const 1)
      · fun_prop
    · fun_prop
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  -- the boundary values
  have hstir : ∀ z : ℂ, z.re = -3 / 4 →
      ‖Complex.Gamma z‖ ≤ CS * (1 + |z.im|) ^ (-(5 : ℝ) / 4) * Real.exp (-Real.pi * |z.im| / 2) := by
    intro z hz
    have hz' : z = -3 / 4 + I * z.im := by apply Complex.ext <;> simp [hz]
    rw [hz']
    have := hCS z.im
    simpa using this
  have hS0 : 0 ≤ CS := by
    have h1 := (norm_nonneg _).trans (hstir (-3 / 4) (by norm_num))
    have h2 : 0 < (1 + |((-3 / 4 : ℂ)).im|) ^ (-(5 : ℝ) / 4) *
        Real.exp (-Real.pi * |((-3 / 4 : ℂ)).im| / 2) := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg h2
    rw [← mul_assoc] at this
    linarith
  have hexp1 : ∀ τ : ℝ, Real.exp (-Real.pi * |τ| / 2) * Real.exp (Real.pi * τ / 2) ≤ 1 := by
    intro τ
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.2
    have := le_abs_self τ
    nlinarith [Real.pi_pos]
  refine ⟨CS, fun s hs1 hs2 => ?_⟩
  apply PhragmenLindelof.vertical_strip (a := -3 / 4) (b := 1 / 4) (f := f) _ _ _ _ hs1 hs2
  · -- `f` is differentiable on a neighbourhood of the closed strip
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num)]
    exact hdiff.mono fun z hz => by
      simp only [mem_preimage, mem_Icc] at hz
      show -1 < z.re
      linarith [hz.1]
  · -- the growth condition
    refine ⟨1, by linarith [Real.pi_gt_three], 2, ?_⟩
    refine IsBigO.of_bound (Real.Gamma (1 / 4) + Real.Gamma (5 / 4)) ?_
    refine eventually_inf_principal.2 (Eventually.of_forall fun z hz => ?_)
    simp only [mem_preimage, mem_Ioo] at hz
    have hz2 : 0 < ‖z + 2‖ := norm_pos_iff.2 (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)
    have hz2' : 1 ≤ ‖z + 2‖ := by
      have := Complex.re_le_norm (z + 2)
      simp at this; linarith
    have hΓ : ‖Complex.Gamma (z + 1)‖ ≤ Real.Gamma (1 / 4) + Real.Gamma (5 / 4) := by
      refine (norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
      exact Gamma_le_of_mem (by simp; linarith) (by simp; linarith)
    have hM0 : 0 ≤ Real.Gamma (1 / 4) + Real.Gamma (5 / 4) := (norm_nonneg _).trans hΓ
    have he : Real.exp (Real.pi * z.im / 2) ≤ Real.exp (2 * Real.exp (1 * |z.im|)) := by
      apply Real.exp_le_exp.2
      have h1 := le_abs_self z.im
      have h2 := Real.add_one_le_exp |z.im|
      have h3 : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
      have h4 := abs_nonneg z.im
      rw [one_mul]
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 h3) h4]
    simp only [hf, norm_div, norm_mul, norm_exp_neg_I_pi]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, div_le_iff₀ hz2]
    calc ‖Complex.Gamma (z + 1)‖ * Real.exp (Real.pi * z.im / 2)
        ≤ (Real.Gamma (1 / 4) + Real.Gamma (5 / 4)) * Real.exp (2 * Real.exp (1 * |z.im|)) :=
          mul_le_mul hΓ he (Real.exp_pos _).le hM0
      _ ≤ (Real.Gamma (1 / 4) + Real.Gamma (5 / 4)) * Real.exp (2 * Real.exp (1 * |z.im|)) *
            ‖z + 2‖ := le_mul_of_one_le_right (by positivity) hz2'
  · -- the left boundary `Re z = -3/4`
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; norm_num at hz
    simp only [hf, norm_div, norm_mul, norm_exp_neg_I_pi]
    rw [Complex.Gamma_add_one z hz0, norm_mul]
    have hz2 : 0 < ‖z + 2‖ := norm_pos_iff.2 (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)
    have hzz : ‖z‖ ≤ ‖z + 2‖ := by
      have hsq : ‖z‖ ^ 2 ≤ ‖z + 2‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp [hz]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
    rw [div_le_iff₀ hz2]
    have h1 := hstir z hz
    have h2 : (1 + |z.im|) ^ (-(5 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.im]) (by norm_num)
    have h3 := hexp1 z.im
    have hG : ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2) ≤ CS := by
      calc ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2)
          ≤ CS * (1 + |z.im|) ^ (-(5 : ℝ) / 4) * Real.exp (-Real.pi * |z.im| / 2) *
              Real.exp (Real.pi * z.im / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = CS * (1 + |z.im|) ^ (-(5 : ℝ) / 4) *
              (Real.exp (-Real.pi * |z.im| / 2) * Real.exp (Real.pi * z.im / 2)) := by ring
        _ ≤ CS * 1 * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h2 hS0) h3 (by positivity) (by positivity)
        _ = CS := by ring
    calc ‖z‖ * ‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2)
        = ‖z‖ * (‖Complex.Gamma z‖ * Real.exp (Real.pi * z.im / 2)) := by ring
      _ ≤ ‖z + 2‖ * CS := mul_le_mul hzz hG (by positivity) (norm_nonneg _)
      _ = CS * ‖z + 2‖ := by ring
  · -- the right boundary `Re z = 1/4`
    intro z hz
    set u := z - 1 with hu
    have hu1 : u.re = -3 / 4 := by rw [hu]; simp [hz]; norm_num
    have hu0 : u ≠ 0 := by intro h; rw [h] at hu1; norm_num at hu1
    have hu10 : u + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hu1] at this; norm_num at this
    have ez : z + 1 = u + 1 + 1 := by rw [hu]; ring
    have ez2 : z + 2 = u + 3 := by rw [hu]; ring
    have hzim : z.im = u.im := by rw [hu]; simp
    simp only [hf, norm_div, norm_mul, norm_exp_neg_I_pi]
    rw [ez, Complex.Gamma_add_one _ hu10, Complex.Gamma_add_one _ hu0, ez2, hzim, norm_mul,
      norm_mul]
    have hu3 : 0 < ‖u + 3‖ := norm_pos_iff.2 (by
      intro h; have := congrArg Complex.re h; simp [hu1] at this; norm_num at this)
    have huu : ‖u + 1‖ ≤ ‖u + 3‖ := by
      have hsq : ‖u + 1‖ ^ 2 ≤ ‖u + 3‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        simp [hu1]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
    have hun : ‖u‖ ≤ 1 + |u.im| := by
      calc ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
        _ ≤ 1 + |u.im| := by rw [hu1]; norm_num
    rw [div_le_iff₀ hu3]
    have h1 := hstir u hu1
    have h3 := hexp1 u.im
    have hpow : (1 + |u.im|) * (1 + |u.im|) ^ (-(5 : ℝ) / 4) ≤ 1 := by
      have e : (1 + |u.im|) * (1 + |u.im|) ^ (-(5 : ℝ) / 4) = (1 + |u.im|) ^ (-(1 : ℝ) / 4) := by
        rw [show (-(1 : ℝ) / 4) = 1 + (-(5 : ℝ) / 4) by norm_num,
          Real.rpow_add (by positivity), Real.rpow_one]
      rw [e]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg u.im]) (by norm_num)
    have hG : ‖u‖ * ‖Complex.Gamma u‖ * Real.exp (Real.pi * u.im / 2) ≤ CS := by
      calc ‖u‖ * ‖Complex.Gamma u‖ * Real.exp (Real.pi * u.im / 2)
          ≤ (1 + |u.im|) * (CS * (1 + |u.im|) ^ (-(5 : ℝ) / 4) *
              Real.exp (-Real.pi * |u.im| / 2)) * Real.exp (Real.pi * u.im / 2) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul hun h1 (norm_nonneg _) (by positivity)
        _ = CS * ((1 + |u.im|) * (1 + |u.im|) ^ (-(5 : ℝ) / 4)) *
              (Real.exp (-Real.pi * |u.im| / 2) * Real.exp (Real.pi * u.im / 2)) := by ring
        _ ≤ CS * 1 * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hS0) h3 (by positivity) (by positivity)
        _ = CS := by ring
    calc ‖u + 1‖ * (‖u‖ * ‖Complex.Gamma u‖) * Real.exp (Real.pi * u.im / 2)
        = ‖u + 1‖ * (‖u‖ * ‖Complex.Gamma u‖ * Real.exp (Real.pi * u.im / 2)) := by ring
      _ ≤ ‖u + 3‖ * CS := mul_le_mul huu hG (by positivity) (norm_nonneg _)
      _ = CS * ‖u + 3‖ := by ring

/-- `|Γ(s)| ≤ C e^(-π|Im s|/2)` for `-3/4 ≤ Re s ≤ 1/4` and `|Im s| ≥ 1`. -/
theorem norm_Gamma_strip (hS : StirlingBound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 1 / 4 → 1 ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * Real.exp (-Real.pi * |s.im| / 2) := by
  obtain ⟨C, hC⟩ := norm_Gamma_strip_aux hS
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by norm_num) (by norm_num))
  have key : ∀ s : ℂ, -3 / 4 ≤ s.re → s.re ≤ 1 / 4 → 1 ≤ s.im →
      ‖Complex.Gamma s‖ ≤ 3 * C * Real.exp (-Real.pi * s.im / 2) := by
    intro s h1 h2 h3
    have hs0 : s ≠ 0 := fun h => by rw [h] at h3; simp at h3; linarith
    have hf := hC s h1 h2
    rw [Complex.Gamma_add_one s hs0, norm_div, norm_mul, norm_mul, norm_exp_neg_I_pi] at hf
    have hs2 : 0 < ‖s + 2‖ := norm_pos_iff.2 (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)
    have hsn : 1 ≤ ‖s‖ := h3.trans ((le_abs_self _).trans (Complex.abs_im_le_norm s))
    have hs2le : ‖s + 2‖ ≤ 3 * ‖s‖ := by
      calc ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
        _ = ‖s‖ + 2 := by simp
        _ ≤ 3 * ‖s‖ := by linarith
    rw [div_le_iff₀ hs2] at hf
    have h4 : ‖s‖ * (‖Complex.Gamma s‖ * Real.exp (Real.pi * s.im / 2)) ≤ ‖s‖ * (3 * C) := by
      calc ‖s‖ * (‖Complex.Gamma s‖ * Real.exp (Real.pi * s.im / 2))
          = ‖s‖ * ‖Complex.Gamma s‖ * Real.exp (Real.pi * s.im / 2) := by ring
        _ ≤ C * ‖s + 2‖ := hf
        _ ≤ C * (3 * ‖s‖) := mul_le_mul_of_nonneg_left hs2le hC0
        _ = ‖s‖ * (3 * C) := by ring
    have h5 : ‖Complex.Gamma s‖ * Real.exp (Real.pi * s.im / 2) ≤ 3 * C :=
      le_of_mul_le_mul_left h4 (by linarith)
    have h6 : Real.exp (Real.pi * s.im / 2) * Real.exp (-Real.pi * s.im / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc ‖Complex.Gamma s‖
        = ‖Complex.Gamma s‖ * Real.exp (Real.pi * s.im / 2) * Real.exp (-Real.pi * s.im / 2) := by
          rw [mul_assoc, h6, mul_one]
      _ ≤ 3 * C * Real.exp (-Real.pi * s.im / 2) :=
          mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
  refine ⟨3 * C, by positivity, fun s h1 h2 h3 => ?_⟩
  rcases le_or_gt 0 s.im with him | him
  · rw [abs_of_nonneg him] at h3 ⊢
    exact key s h1 h2 h3
  · rw [abs_of_neg him] at h3 ⊢
    have := key ((starRingEnd ℂ) s) (by simpa using h1) (by simpa using h2) (by simpa using h3)
    rw [Complex.Gamma_conj, Complex.norm_conj] at this
    simpa using this

/-! ### Bounds for `G_t` -/

theorem norm_two_cpow_sub (w : ℂ) : ‖(2 : ℂ) ^ (w - 2)‖ = (2 : ℝ) ^ (w.re - 2) := by
  have := norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (w - 2)
  push_cast at this
  rw [this]; simp

theorem abs_le_half_add_half (a t : ℝ) : |a| ≤ |(a + t) / 2| + |(a - t) / 2| := by
  rw [abs_div, abs_div, abs_two]
  have := abs_add_le (a + t) (a - t)
  rw [show a + t + (a - t) = 2 * a by ring, abs_mul, abs_two] at this
  linarith

/-- Decay of `G_t` in the strip `-3/2 ≤ Re w ≤ 1/2`. -/
theorem norm_Gt_strip (hS : StirlingBound) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 1 / 2 → |t| + 2 ≤ |w.im| →
      ‖Gt t w‖ ≤ C * Real.exp (-Real.pi * |w.im| / 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_strip hS
  refine ⟨C ^ 2, by positivity, fun w h1 h2 h3 => ?_⟩
  have e1 : ((w + I * t) / 2).re = w.re / 2 := by simp
  have e2 : ((w + I * t) / 2).im = (w.im + t) / 2 := by simp
  have e3 : ((w - I * t) / 2).re = w.re / 2 := by simp
  have e4 : ((w - I * t) / 2).im = (w.im - t) / 2 := by simp
  have ht1 : 1 ≤ |(w.im + t) / 2| := by
    rw [abs_div, abs_two]
    have := abs_add_le (w.im + t) (-t)
    rw [show w.im + t + -t = w.im by ring, abs_neg] at this
    linarith
  have ht2 : 1 ≤ |(w.im - t) / 2| := by
    rw [abs_div, abs_two]
    have := abs_add_le (w.im - t) t
    rw [show w.im - t + t = w.im by ring] at this
    linarith
  have g1 := hC ((w + I * t) / 2) (by rw [e1]; linarith) (by rw [e1]; linarith)
    (by rw [e2]; exact ht1)
  have g2 := hC ((w - I * t) / 2) (by rw [e3]; linarith) (by rw [e3]; linarith)
    (by rw [e4]; exact ht2)
  rw [e2] at g1
  rw [e4] at g2
  have h2pow : (2 : ℝ) ^ (w.re - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hexp : Real.exp (-Real.pi * |(w.im + t) / 2| / 2) *
      Real.exp (-Real.pi * |(w.im - t) / 2| / 2) ≤ Real.exp (-Real.pi * |w.im| / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left (abs_le_half_add_half w.im t) Real.pi_pos.le
    linarith
  unfold Gt
  rw [norm_mul, norm_mul, norm_two_cpow_sub]
  calc (2 : ℝ) ^ (w.re - 2) * ‖Complex.Gamma ((w + I * t) / 2)‖ *
        ‖Complex.Gamma ((w - I * t) / 2)‖
      ≤ 1 * (C * Real.exp (-Real.pi * |(w.im + t) / 2| / 2)) *
          (C * Real.exp (-Real.pi * |(w.im - t) / 2| / 2)) :=
        mul_le_mul (mul_le_mul h2pow g1 (norm_nonneg _) zero_le_one) g2 (norm_nonneg _)
          (by positivity)
    _ = C ^ 2 * (Real.exp (-Real.pi * |(w.im + t) / 2| / 2) *
          Real.exp (-Real.pi * |(w.im - t) / 2| / 2)) := by ring
    _ ≤ C ^ 2 * Real.exp (-Real.pi * |w.im| / 2) := mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `G_t(1/2 + iξ) ≪ e^(-π|ξ|/2)`. -/
theorem norm_Gt_half (hS : StirlingBound) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      ‖Gt t ((1 / 2 : ℝ) + ξ * I)‖ ≤ C * Real.exp (-Real.pi * |ξ| / 2) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gt_strip hS t
  set B := Real.Gamma (1 / 4) ^ 2 * Real.exp (Real.pi * (|t| + 2) / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max C B, le_max_of_le_left hC0, fun ξ => ?_⟩
  set w : ℂ := (1 / 2 : ℝ) + ξ * I with hw
  have hwre : w.re = 1 / 2 := by simp [hw]
  have hwim : w.im = ξ := by simp [hw]
  rcases le_or_gt (|t| + 2) |ξ| with hξ | hξ
  · have := hC w (by rw [hwre]; norm_num) (by rw [hwre]) (by rw [hwim]; exact hξ)
    rw [hwim] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have g : ∀ s : ℂ, s.re = 1 / 4 → ‖Complex.Gamma s‖ ≤ Real.Gamma (1 / 4) := by
      intro s hs
      have := norm_Gamma_le_Gamma_re (s := s) (by rw [hs]; norm_num)
      rwa [hs] at this
    have hG : ‖Gt t w‖ ≤ Real.Gamma (1 / 4) ^ 2 := by
      unfold Gt
      rw [norm_mul, norm_mul, norm_two_cpow_sub, hwre]
      have g1 := g ((w + I * t) / 2) (by simp [hwre]; norm_num)
      have g2 := g ((w - I * t) / 2) (by simp [hwre]; norm_num)
      have h2pow : (2 : ℝ) ^ ((1 / 2 : ℝ) - 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
      calc (2 : ℝ) ^ ((1 / 2 : ℝ) - 2) * ‖Complex.Gamma ((w + I * t) / 2)‖ *
            ‖Complex.Gamma ((w - I * t) / 2)‖
          ≤ 1 * Real.Gamma (1 / 4) * Real.Gamma (1 / 4) :=
            mul_le_mul (mul_le_mul h2pow g1 (norm_nonneg _) zero_le_one) g2 (norm_nonneg _)
              (by positivity)
        _ = Real.Gamma (1 / 4) ^ 2 := by ring
    have he : 1 ≤ Real.exp (Real.pi * (|t| + 2) / 2) * Real.exp (-Real.pi * |ξ| / 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hξ.le Real.pi_pos.le
      linarith
    calc ‖Gt t w‖ ≤ Real.Gamma (1 / 4) ^ 2 * 1 := by rw [mul_one]; exact hG
      _ ≤ Real.Gamma (1 / 4) ^ 2 *
            (Real.exp (Real.pi * (|t| + 2) / 2) * Real.exp (-Real.pi * |ξ| / 2)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = B * Real.exp (-Real.pi * |ξ| / 2) := by rw [hB]; ring
      _ ≤ max C B * Real.exp (-Real.pi * |ξ| / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem exp_neg_pi_abs_le (ξ : ℝ) : Real.exp (-Real.pi * |ξ| / 2) ≤ (1 + ξ ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.pi * |ξ| / 2) (by positivity)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi2 : 9 ≤ Real.pi ^ 2 := by nlinarith
  have hξ : ξ ^ 2 = |ξ| ^ 2 := (sq_abs ξ).symm
  have h1 : 1 + ξ ^ 2 ≤ Real.exp (Real.pi * |ξ| / 2) := by
    have h3 : 9 * |ξ| ^ 2 ≤ Real.pi ^ 2 * |ξ| ^ 2 :=
      mul_le_mul_of_nonneg_right hpi2 (sq_nonneg _)
    have h4 : 0 ≤ Real.pi * |ξ| / 2 := by positivity
    nlinarith
  rw [show -Real.pi * |ξ| / 2 = -(Real.pi * |ξ| / 2) by ring, Real.exp_neg]
  exact inv_anti₀ (by positivity) h1

theorem continuous_Gt_half (t : ℝ) : Continuous (fun ξ : ℝ => Gt t ((1 / 2 : ℝ) + ξ * I)) := by
  unfold Gt
  apply Continuous.mul
  · apply Continuous.mul
    · exact Continuous.const_cpow (by fun_prop) (Or.inl two_ne_zero)
    · rw [continuous_iff_continuousAt]
      intro ξ
      apply ContinuousAt.comp (g := Complex.Gamma)
      · exact (differentiableAt_Gamma_of_re_pos (by norm_num)).continuousAt
      · fun_prop
  · rw [continuous_iff_continuousAt]
    intro ξ
    apply ContinuousAt.comp (g := Complex.Gamma)
    · exact (differentiableAt_Gamma_of_re_pos (by norm_num)).continuousAt
    · fun_prop

theorem integrable_Gt_half (hS : StirlingBound) (t : ℝ) :
    Integrable (fun ξ : ℝ => Gt t ((1 / 2 : ℝ) + ξ * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Gt_half hS t
  refine (integrable_inv_one_add_sq.const_mul C).mono' (continuous_Gt_half t).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  exact (hC ξ).trans (mul_le_mul_of_nonneg_left (exp_neg_pi_abs_le ξ) hC0)

/-! ### The principal parts -/

theorem tendsto_log_ratio {l : Filter ℝ} (hl : Tendsto (fun u : ℝ => u ^ 2) l atTop) :
    Tendsto (fun u : ℝ => (Real.log (9 / 4 + u ^ 2) - Real.log (1 / 4 + u ^ 2)) / 2) l (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => 1 / 4 + u ^ 2) l atTop := tendsto_atTop_add_const_left _ _ hl
  have h3 : Tendsto (fun u : ℝ => 1 + 2 / (1 / 4 + u ^ 2)) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop h1)
  have h4 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h3).div_const 2
  rw [Real.log_one, zero_div] at h4
  refine h4.congr (fun u => ?_)
  simp only [Function.comp]
  have hp : (0 : ℝ) < 1 / 4 + u ^ 2 := by positivity
  have hq : (0 : ℝ) < 9 / 4 + u ^ 2 := by positivity
  rw [← Real.log_div hq.ne' hp.ne']
  congr 2
  field_simp
  ring

/-- The integrand `1/(1/2 + iu) - 1/(-3/2 + iu)` is integrable. -/
theorem integrable_principal_aux :
    Integrable (fun u : ℝ => 1 / ((1 / 2 : ℂ) + u * I) - 1 / ((-3 / 2 : ℂ) + u * I)) := by
  set g : ℝ → ℂ := fun u => 1 / ((1 / 2 : ℂ) + u * I) - 1 / ((-3 / 2 : ℂ) + u * I) with hg
  have hA : ∀ u : ℝ, (1 / 2 : ℂ) + u * I ≠ 0 := by
    intro u h; have := congrArg Complex.re h; simp at this
  have hB : ∀ u : ℝ, (-3 / 2 : ℂ) + u * I ≠ 0 := by
    intro u h; have := congrArg Complex.re h; norm_num at this
  have hgb : ∀ u : ℝ, ‖g u‖ ≤ 8 * (1 + u ^ 2)⁻¹ := by
    intro u
    have e : g u = -2 / (((1 / 2 : ℂ) + u * I) * ((-3 / 2 : ℂ) + u * I)) := by
      simp only [hg]
      rw [div_sub_div _ _ (hA u) (hB u)]
      congr 1
      ring
    have nA : ‖(1 / 2 : ℂ) + u * I‖ ^ 2 = 1 / 4 + u ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have nB : ‖(-3 / 2 : ℂ) + u * I‖ ^ 2 = 9 / 4 + u ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hAB : ‖(1 / 2 : ℂ) + u * I‖ ≤ ‖(-3 / 2 : ℂ) + u * I‖ := by
      apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      rw [nA, nB]; linarith
    have hA0 : 0 < ‖(1 / 2 : ℂ) + u * I‖ := norm_pos_iff.2 (hA u)
    have hB0 : 0 < ‖(-3 / 2 : ℂ) + u * I‖ := norm_pos_iff.2 (hB u)
    rw [e, norm_div, norm_mul, norm_neg, div_le_iff₀ (by positivity)]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have hu : (0 : ℝ) < 1 + u ^ 2 := by positivity
    calc (2 : ℝ) = 8 * (1 + u ^ 2)⁻¹ * ((1 + u ^ 2) / 4) := by field_simp; ring
      _ ≤ 8 * (1 + u ^ 2)⁻¹ * ‖(1 / 2 : ℂ) + u * I‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [nA]; nlinarith [sq_nonneg u]
      _ ≤ 8 * (1 + u ^ 2)⁻¹ * (‖(1 / 2 : ℂ) + u * I‖ * ‖(-3 / 2 : ℂ) + u * I‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [sq]; exact mul_le_mul_of_nonneg_left hAB (norm_nonneg _)
  have hcont : Continuous g := by
    simp only [hg]
    apply Continuous.sub
    · exact continuous_const.div (by fun_prop) hA
    · exact continuous_const.div (by fun_prop) hB
  have hint : Integrable g :=
    (integrable_inv_one_add_sq.const_mul 8).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall hgb)
  exact hint

/-- `∫ (1/(1/2 + iu) - 1/(-3/2 + iu)) du = 2π`. -/
theorem integral_principal_aux :
    ∫ u : ℝ, (1 / ((1 / 2 : ℂ) + u * I) - 1 / ((-3 / 2 : ℂ) + u * I)) = 2 * Real.pi := by
  set g : ℝ → ℂ := fun u => 1 / ((1 / 2 : ℂ) + u * I) - 1 / ((-3 / 2 : ℂ) + u * I) with hg
  set F : ℝ → ℂ := fun u => ((Real.arctan (2 * u) + Real.arctan (2 * u / 3) : ℝ) : ℂ) +
    I * (((Real.log (9 / 4 + u ^ 2) - Real.log (1 / 4 + u ^ 2)) / 2 : ℝ) : ℂ) with hF
  have hA : ∀ u : ℝ, (1 / 2 : ℂ) + u * I ≠ 0 := by
    intro u h; have := congrArg Complex.re h; simp at this
  have hB : ∀ u : ℝ, (-3 / 2 : ℂ) + u * I ≠ 0 := by
    intro u h; have := congrArg Complex.re h; norm_num at this
  have key : ∀ u : ℝ, g u = (((1 / 2) / (1 / 4 + u ^ 2) + (3 / 2) / (9 / 4 + u ^ 2) : ℝ) : ℂ) +
      I * ((-u / (1 / 4 + u ^ 2) + u / (9 / 4 + u ^ 2) : ℝ) : ℂ) := by
    intro u
    have hp : (1 / 4 + u ^ 2 : ℝ) ≠ 0 := by positivity
    have hq : (9 / 4 + u ^ 2 : ℝ) ≠ 0 := by positivity
    have hp' : ((1 / 4 + u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
    have hq' : ((9 / 4 + u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
    have hp'' : (1 / 4 + (u : ℂ) ^ 2) ≠ 0 := by
      rw [show (1 / 4 + (u : ℂ) ^ 2) = ((1 / 4 + u ^ 2 : ℝ) : ℂ) by push_cast; ring]; exact hp'
    have hq'' : (9 / 4 + (u : ℂ) ^ 2) ≠ 0 := by
      rw [show (9 / 4 + (u : ℂ) ^ 2) = ((9 / 4 + u ^ 2 : ℝ) : ℂ) by push_cast; ring]; exact hq'
    have eA : 1 / ((1 / 2 : ℂ) + u * I) = ((1 / 2 : ℂ) - u * I) / ((1 / 4 + u ^ 2 : ℝ) : ℂ) := by
      rw [div_eq_div_iff (hA u) hp']
      push_cast
      linear_combination (u : ℂ) ^ 2 * Complex.I_sq
    have eB : 1 / ((-3 / 2 : ℂ) + u * I) = ((-3 / 2 : ℂ) - u * I) / ((9 / 4 + u ^ 2 : ℝ) : ℂ) := by
      rw [div_eq_div_iff (hB u) hq']
      push_cast
      linear_combination (u : ℂ) ^ 2 * Complex.I_sq
    simp only [hg, eA, eB]
    push_cast
    field_simp
    ring
  have hderiv : ∀ u : ℝ, HasDerivAt F (g u) u := by
    intro u
    have h1 := ((hasDerivAt_id' u).const_mul (2 : ℝ)).arctan
    have h2 := (((hasDerivAt_id' u).const_mul (2 : ℝ)).div_const 3).arctan
    have hp : (0 : ℝ) < 1 / 4 + u ^ 2 := by positivity
    have hq : (0 : ℝ) < 9 / 4 + u ^ 2 := by positivity
    have h3 := ((hasDerivAt_pow 2 u).const_add (9 / 4 : ℝ)).log hq.ne'
    have h4 := ((hasDerivAt_pow 2 u).const_add (1 / 4 : ℝ)).log hp.ne'
    have h5 := ((h1.add h2).ofReal_comp).add (((h3.sub h4).div_const 2).ofReal_comp.const_mul I)
    convert h5 using 1
    have eX : (1 / 2) / (1 / 4 + u ^ 2) + (3 / 2) / (9 / 4 + u ^ 2) =
        1 / (1 + (2 * u) ^ 2) * (2 * 1) + 1 / (1 + (2 * u / 3) ^ 2) * (2 * 1 / 3) := by
      field_simp; ring
    have eY : -u / (1 / 4 + u ^ 2) + u / (9 / 4 + u ^ 2) =
        (((2 : ℕ) : ℝ) * u ^ (2 - 1) / (9 / 4 + u ^ 2) -
          ((2 : ℕ) : ℝ) * u ^ (2 - 1) / (1 / 4 + u ^ 2)) / 2 := by
      norm_num
      field_simp
      ring
    rw [key u, eX, eY]
  have hint : Integrable g := integrable_principal_aux
  have htop : Tendsto F atTop (𝓝 (((Real.pi / 2 + Real.pi / 2 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) := by
    have ha1 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))
    have ha2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      ((tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2)).atTop_div_const
        (by norm_num : (0 : ℝ) < 3))
    have hl := tendsto_log_ratio (l := atTop) (tendsto_pow_atTop two_ne_zero)
    exact ((Complex.continuous_ofReal.tendsto _).comp (ha1.add ha2)).add
      (((Complex.continuous_ofReal.tendsto _).comp hl).const_mul I)
  have hbot : Tendsto F atBot (𝓝 (((-(Real.pi / 2) + -(Real.pi / 2) : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) := by
    have ha1 := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.const_mul_atBot (two_pos : (0 : ℝ) < 2))
    have ha2 := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      ((tendsto_id.const_mul_atBot (two_pos : (0 : ℝ) < 2)).atBot_div_const
        (by norm_num : (0 : ℝ) < 3))
    have hsq : Tendsto (fun u : ℝ => u ^ 2) atBot atTop := by
      have := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).comp (tendsto_abs_atBot_atTop (G := ℝ))
      refine this.congr (fun u => ?_)
      simp [sq_abs]
    have hl := tendsto_log_ratio (l := atBot) hsq
    exact ((Complex.continuous_ofReal.tendsto _).comp (ha1.add ha2)).add
      (((Complex.continuous_ofReal.tendsto _).comp hl).const_mul I)
  rw [integral_of_hasDerivAt_of_tendsto hderiv hint hbot htop]
  push_cast
  ring

/-- `∫ (1/(1/2 + iξ - iγ) - 1/(-3/2 + iξ - iγ)) dξ = 2π`. -/
theorem integral_principal (γ : ℝ) :
    ∫ ξ : ℝ, (1 / ((1 / 2 : ℂ) + ξ * I - I * γ) - 1 / ((-3 / 2 : ℂ) + ξ * I - I * γ)) =
      2 * Real.pi := by
  have := integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => 1 / ((1 / 2 : ℂ) + u * I) - 1 / ((-3 / 2 : ℂ) + u * I)) γ
  rw [integral_principal_aux] at this
  rw [← this]
  congr 1
  funext ξ
  have e1 : (1 / 2 : ℂ) + ((ξ - γ : ℝ) : ℂ) * I = 1 / 2 + ξ * I - I * γ := by push_cast; ring
  have e2 : (-3 / 2 : ℂ) + ((ξ - γ : ℝ) : ℂ) * I = -3 / 2 + ξ * I - I * γ := by push_cast; ring
  simp only [e1, e2]

theorem integrable_principal (γ : ℝ) :
    Integrable (fun ξ : ℝ => 1 / ((1 / 2 : ℂ) + ξ * I - I * γ) - 1 / ((-3 / 2 : ℂ) + ξ * I - I * γ)) := by
  refine (integrable_principal_aux.comp_sub_right γ).congr (Eventually.of_forall fun ξ => ?_)
  have e1 : (1 / 2 : ℂ) + ((ξ - γ : ℝ) : ℂ) * I = 1 / 2 + ξ * I - I * γ := by push_cast; ring
  have e2 : (-3 / 2 : ℂ) + ((ξ - γ : ℝ) : ℂ) * I = -3 / 2 + ξ * I - I * γ := by push_cast; ring
  simp only [e1, e2]

/-- `((y/2)^z = y^z 2^(-z)`. -/
theorem half_cpow {y : ℝ} (hy : 0 < y) (z : ℂ) :
    ((y / 2 : ℝ) : ℂ) ^ z = (y : ℂ) ^ z * (2 : ℂ) ^ (-z) := by
  have h1 : ((y / 2 : ℝ) : ℂ) = (y : ℂ) * ((2⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.mul_cpow_ofReal_nonneg hy.le (by norm_num) z]
  congr 1
  have harg : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow _ _ (by simpa using harg)]
  norm_num

/-! ### The contour shift -/

/-- `P(w) = 2^(w-2) Γ((w+it)/2 + 1) Γ((w-it)/2 + 1) y^(-w)`, holomorphic on `Re w > -2`. -/
noncomputable def Pmb (t y : ℝ) (w : ℂ) : ℂ :=
  (2 : ℂ) ^ (w - 2) * Complex.Gamma ((w + I * t) / 2 + 1) * Complex.Gamma ((w - I * t) / 2 + 1) *
    (y : ℂ) ^ (-w)

theorem differentiableOn_Pmb (t : ℝ) {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (Pmb t y) {w : ℂ | -2 < w.re} := by
  intro w hw
  have hw : -2 < w.re := hw
  apply DifferentiableAt.differentiableWithinAt
  have h2 : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (w - 2)) w :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - 2) w).const_cpow (Or.inl two_ne_zero)
  have hg1 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((w + I * t) / 2 + 1)) w :=
    (differentiableAt_Gamma_of_re_pos (by simp; linarith)).comp w (by fun_prop)
  have hg2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((w - I * t) / 2 + 1)) w :=
    (differentiableAt_Gamma_of_re_pos (by simp; linarith)).comp w (by fun_prop)
  have hy' : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ (-w)) w :=
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => -w) w).const_cpow
      (Or.inl (by exact_mod_cast hy.ne'))
  exact ((h2.mul hg1).mul hg2).mul hy'

/-- `h(w) = (2/(it)) (dslope P (it) w - dslope P (-it) w)`: `G_t(w) y^(-w)` with its poles at
`±it` removed. -/
noncomputable def hmb (t y : ℝ) (w : ℂ) : ℂ :=
  2 / (I * t) * (dslope (Pmb t y) (I * t) w - dslope (Pmb t y) (-(I * t)) w)

theorem differentiableOn_hmb (t : ℝ) {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (hmb t y) {w : ℂ | -2 < w.re} := by
  have hU : IsOpen {w : ℂ | -2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : DifferentiableOn ℂ (dslope (Pmb t y) (I * t)) {w : ℂ | -2 < w.re} :=
    (differentiableOn_dslope (hU.mem_nhds (by simp))).2 (differentiableOn_Pmb t hy)
  have h2 : DifferentiableOn ℂ (dslope (Pmb t y) (-(I * t))) {w : ℂ | -2 < w.re} :=
    (differentiableOn_dslope (hU.mem_nhds (by simp))).2 (differentiableOn_Pmb t hy)
  exact (h1.sub h2).const_mul (2 / (I * t))

theorem hmb_eq (t : ℝ) (ht : t ≠ 0) (y : ℝ) {w : ℂ} (hw1 : w ≠ I * t) (hw2 : w ≠ -(I * t)) :
    hmb t y w = Gt t w * (y : ℂ) ^ (-w) -
      2 / (I * t) * (Pmb t y (I * t) / (w - I * t) - Pmb t y (-(I * t)) / (w + I * t)) := by
  have hw1' : w - I * t ≠ 0 := sub_ne_zero.2 hw1
  have hw2' : w + I * t ≠ 0 := by
    intro h; apply hw2; linear_combination h
  have hs1 : (w + I * t) / 2 ≠ 0 := div_ne_zero hw2' two_ne_zero
  have hs2 : (w - I * t) / 2 ≠ 0 := div_ne_zero hw1' two_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hIt : I * (t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero ht'
  have hP : Pmb t y w = (w + I * t) / 2 * ((w - I * t) / 2) * (Gt t w * (y : ℂ) ^ (-w)) := by
    unfold Pmb Gt
    rw [Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs2]
    ring
  unfold hmb
  rw [dslope_of_ne _ hw1, dslope_of_ne _ hw2, slope_def_field, slope_def_field, hP,
    sub_neg_eq_add]
  field_simp
  ring

/-- The horizontal sides of the rectangle. -/
theorem norm_hmb_horiz (hS : StirlingBound) {t : ℝ} (ht : t ≠ 0) {y : ℝ} (hy : 0 < y) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ T : ℝ, |t| + 2 ≤ |T| → ∀ x : ℝ, -3 / 2 ≤ x → x ≤ 1 / 2 →
      ‖hmb t y (x + T * I)‖ ≤ C₁ * Real.exp (-Real.pi * |T| / 2) + C₂ / (|T| - |t|) := by
  obtain ⟨CG, hCG0, hCG⟩ := norm_Gt_strip hS t
  set Y₀ := y ^ (3 / 2 : ℝ) + y ^ (-(1 / 2) : ℝ) with hY₀
  have hY₀0 : 0 ≤ Y₀ := by positivity
  set P₁ := ‖Pmb t y (I * t)‖
  set P₂ := ‖Pmb t y (-(I * t))‖
  refine ⟨CG * Y₀, 2 / |t| * (P₁ + P₂), by positivity, by positivity,
    fun T hT x hx1 hx2 => ?_⟩
  set w : ℂ := x + T * I with hw
  have hwre : w.re = x := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hTt : |t| < |T| := by linarith
  have hTt0 : 0 < |T| - |t| := by linarith
  have hd1 : |T| - |t| ≤ ‖w - I * t‖ := by
    have h1 := Complex.abs_im_le_norm (w - I * t)
    have h2 : (w - I * t).im = T - t := by simp [hwim]
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub T t
    linarith
  have hd2 : |T| - |t| ≤ ‖w + I * t‖ := by
    have h1 := Complex.abs_im_le_norm (w + I * t)
    have h2 : (w + I * t).im = T + t := by simp [hwim]
    rw [h2] at h1
    have := abs_sub_abs_le_abs_sub T (-t)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hw1 : w ≠ I * t := by
    intro h; rw [h] at hd1; simp at hd1; linarith
  have hw2 : w ≠ -(I * t) := by
    intro h; rw [h] at hd2; simp at hd2; linarith
  rw [hmb_eq t ht y hw1 hw2]
  have hG := hCG w (by rw [hwre]; exact hx1) (by rw [hwre]; exact hx2) (by rw [hwim]; exact hT)
  rw [hwim] at hG
  have hyx : ‖(y : ℂ) ^ (-w)‖ ≤ Y₀ := by
    rw [norm_cpow_eq_rpow_re_of_pos hy, Complex.neg_re, hwre]
    rcases le_or_gt 1 y with h1 | h1
    · have : y ^ (-x) ≤ y ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      have : 0 ≤ y ^ (-(1 / 2) : ℝ) := by positivity
      linarith
    · have : y ^ (-x) ≤ y ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hy h1.le (by linarith)
      have : 0 ≤ y ^ (3 / 2 : ℝ) := by positivity
      linarith
  have hc : ‖(2 : ℂ) / (I * t)‖ = 2 / |t| := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    simp
  have ht0 : 0 < |t| := abs_pos.2 ht
  have hfrac1 : ‖Pmb t y (I * t) / (w - I * t)‖ ≤ P₁ / (|T| - |t|) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hTt0 hd1
  have hfrac2 : ‖Pmb t y (-(I * t)) / (w + I * t)‖ ≤ P₂ / (|T| - |t|) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hTt0 hd2
  calc ‖Gt t w * (y : ℂ) ^ (-w) - 2 / (I * t) *
        (Pmb t y (I * t) / (w - I * t) - Pmb t y (-(I * t)) / (w + I * t))‖
      ≤ ‖Gt t w * (y : ℂ) ^ (-w)‖ + ‖2 / (I * t) *
          (Pmb t y (I * t) / (w - I * t) - Pmb t y (-(I * t)) / (w + I * t))‖ := norm_sub_le _ _
    _ ≤ CG * Real.exp (-Real.pi * |T| / 2) * Y₀ + 2 / |t| * (P₁ / (|T| - |t|) + P₂ / (|T| - |t|)) := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul hG hyx (norm_nonneg _) (by positivity)
        · rw [norm_mul, hc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (norm_sub_le _ _).trans (add_le_add hfrac1 hfrac2)
    _ = CG * Y₀ * Real.exp (-Real.pi * |T| / 2) + 2 / |t| * (P₁ + P₂) / (|T| - |t|) := by
        field_simp

/-- The integral of `h` over the vertical sides of the rectangle `[-3/2, 1/2] × ℝ` vanishes
(Cauchy's theorem, the horizontal sides tending to `0`). -/
theorem integral_hmb_diff (hS : StirlingBound) {t : ℝ} (ht : t ≠ 0) {y : ℝ} (hy : 0 < y)
    (hD : Integrable (fun s : ℝ => hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I))) :
    ∫ s : ℝ, (hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I)) = 0 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hb⟩ := norm_hmb_horiz hS ht hy
  have hcont : ∀ σ : ℝ, -2 < σ → Continuous (fun s : ℝ => hmb t y (σ + s * I)) := by
    intro σ hσ
    refine (differentiableOn_hmb t hy).continuousOn.comp_continuous (by fun_prop) (fun s => ?_)
    show -2 < ((σ : ℂ) + s * I).re
    simpa using hσ
  -- Cauchy's theorem on the rectangle `[-3/2, 1/2] × [-T, T]`
  have hrect : ∀ T : ℝ, I * (∫ s in (-T)..T,
      (hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I))) =
      (∫ x in (-3 / 2 : ℝ)..(1 / 2), hmb t y (x + T * I)) -
        (∫ x in (-3 / 2 : ℝ)..(1 / 2), hmb t y (x + (-T : ℝ) * I)) := by
    intro T
    have H : DifferentiableOn ℂ (hmb t y)
        ([[(⟨-3 / 2, -T⟩ : ℂ).re, (⟨1 / 2, T⟩ : ℂ).re]] ×ℂ
          [[(⟨-3 / 2, -T⟩ : ℂ).im, (⟨1 / 2, T⟩ : ℂ).im]]) := by
      refine (differentiableOn_hmb t hy).mono ?_
      intro p hp
      rw [Complex.mem_reProdIm] at hp
      have h1 := hp.1
      simp only [Set.uIcc_of_le (by norm_num : (-3 / 2 : ℝ) ≤ 1 / 2), Set.mem_Icc] at h1
      show -2 < p.re
      linarith [h1.1]
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (hmb t y)
      ⟨-3 / 2, -T⟩ ⟨1 / 2, T⟩ H
    dsimp only at h
    rw [intervalIntegral.integral_sub ((hcont (1 / 2) (by norm_num)).intervalIntegrable _ _)
      ((hcont (-3 / 2) (by norm_num)).intervalIntegrable _ _)]
    simp only [smul_eq_mul] at h
    linear_combination h
  have hV : Tendsto (fun T : ℝ => ∫ s in (-T)..T,
      (hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I))) atTop
      (𝓝 (∫ s : ℝ, (hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I)))) :=
    intervalIntegral_tendsto_integral hD tendsto_neg_atTop_atBot tendsto_id
  -- the horizontal sides tend to `0`
  have hexp : Tendsto (fun T : ℝ => Real.exp (-Real.pi * |T| / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => Real.pi / 2 * |T|) atTop atTop :=
      (tendsto_abs_atTop_atTop (G := ℝ)).const_mul_atTop (by positivity)
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr (fun T => ?_)
    simp only [Function.comp]
    ring_nf
  have hfrac : Tendsto (fun T : ℝ => C₂ / (|T| - |t|)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_atTop_add_const_right _ (-|t|) (tendsto_abs_atTop_atTop (G := ℝ))).congr
      (fun T => (sub_eq_add_neg _ _).symm)
  have hbound : Tendsto (fun T : ℝ => (C₁ * Real.exp (-Real.pi * |T| / 2) + C₂ / (|T| - |t|)) *
      |1 / 2 - (-3 / 2 : ℝ)|) atTop (𝓝 0) := by
    have := ((hexp.const_mul C₁).add hfrac).mul_const (|1 / 2 - (-3 / 2 : ℝ)|)
    simpa using this
  have htop : Tendsto (fun T : ℝ => ∫ x in (-3 / 2 : ℝ)..(1 / 2), hmb t y (x + T * I)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (|t| + 2)] with T hT
    have hT' : |t| + 2 ≤ |T| := hT.trans (le_abs_self T)
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    exact hb T hT' x hx.1.le hx.2
  have hbot : Tendsto (fun T : ℝ => ∫ x in (-3 / 2 : ℝ)..(1 / 2), hmb t y (x + (-T : ℝ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (|t| + 2)] with T hT
    have hT' : |t| + 2 ≤ |-T| := by rw [abs_neg]; exact hT.trans (le_abs_self T)
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have := hb (-T) hT' x hx.1.le hx.2
    rwa [abs_neg] at this
  have hlim1 : Tendsto (fun T : ℝ => I * ∫ s in (-T)..T,
      (hmb t y ((1 / 2 : ℝ) + s * I) - hmb t y ((-3 / 2 : ℝ) + s * I))) atTop (𝓝 0) := by
    have := htop.sub hbot
    rw [sub_zero] at this
    exact this.congr (fun T => (hrect T).symm)
  have hlim2 := hV.const_mul I
  have := tendsto_nhds_unique hlim2 hlim1
  exact (mul_eq_zero.1 this).resolve_left I_ne_zero

/-- **Lemma 11.2** (the Mellin–Barnes formula for `K_{it}`). -/
theorem mellin_barnes (hB : BesselAssumptions) {t : ℝ} (ht : t ≠ 0) {y : ℝ} (hy : 0 < y) :
    Integrable (fun ξ : ℝ => Gt t (-3 / 2 + I * ξ) * (y : ℂ) ^ (-(-3 / 2 + I * ξ))) ∧
      besselK (I * t) y =
        (1 / 2 : ℂ) * Complex.Gamma (I * t) * ((y / 2 : ℝ) : ℂ) ^ (-(I * t)) +
          (1 / 2 : ℂ) * Complex.Gamma (-(I * t)) * ((y / 2 : ℝ) : ℂ) ^ (I * t) +
          (1 / (2 * Real.pi) : ℂ) *
            ∫ ξ : ℝ, Gt t (-3 / 2 + I * ξ) * (y : ℂ) ^ (-(-3 / 2 + I * ξ)) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hIt : I * (t : ℂ) ≠ 0 := mul_ne_zero I_ne_zero ht'
  -- the integrands on the lines `Re w = 1/2` and `Re w = -3/2`
  set A₁ : ℝ → ℂ := fun ξ => Gt t ((1 / 2 : ℝ) + ξ * I) * (y : ℂ) ^ (-((1 / 2 : ℝ) + ξ * I))
    with hA₁
  set A₂ : ℝ → ℂ := fun ξ => Gt t (-3 / 2 + I * ξ) * (y : ℂ) ^ (-(-3 / 2 + I * ξ)) with hA₂
  have hint1 : Integrable A₁ := by
    refine ((integrable_Gt_half hB.stirling t).norm.mul_const (y ^ (-(1 / 2) : ℝ))).mono'
      ((continuous_Gt_half t).mul (Continuous.const_cpow (by fun_prop) (Or.inl hy0))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => le_of_eq ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
    congr 2
    simp
  have hint2 : Integrable A₂ := by
    refine ((integrable_Gt hB t).norm.mul_const (y ^ (3 / 2 : ℝ))).mono'
      ((continuous_Gt_line.comp (Continuous.prodMk (continuous_const (y := t)) continuous_id)).mul
        (Continuous.const_cpow (by fun_prop) (Or.inl hy0))).aestronglyMeasurable
      (Eventually.of_forall fun ξ => le_of_eq ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
    congr 2
    simp
    norm_num
  refine ⟨hint2, ?_⟩
  -- Mellin inversion on `Re w = 1/2`
  set K : ℝ → ℂ := besselK (I * t) with hK
  have hmellin : ∀ w : ℂ, 0 < w.re → mellin K w = Gt t w := by
    intro w hw
    have h := hB.besselMellin t w hw
    have e : mellin K w = ∫ y in Ioi (0 : ℝ), besselK (I * t) y * (y : ℂ) ^ (w - 1) := by
      unfold mellin
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [smul_eq_mul, mul_comm]
    rw [e, h]
    rfl
  have hw₁ : ∀ ξ : ℝ, 0 < (((1 / 2 : ℝ) : ℂ) + ξ * I).re := fun ξ => by simp
  have hGne : Gt t ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    unfold Gt
    have hΓ : ∀ s : ℂ, 0 < s.re → Complex.Gamma s ≠ 0 := by
      intro s hs
      apply Complex.Gamma_ne_zero
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      linarith
    refine mul_ne_zero (mul_ne_zero ?_ (hΓ _ (by simp))) (hΓ _ (by simp))
    rw [Complex.cpow_def_of_ne_zero two_ne_zero]
    exact Complex.exp_ne_zero _
  have hconv : MellinConvergent K ((1 / 2 : ℝ) : ℂ) := by
    by_contra hcon
    have h0 : mellin K ((1 / 2 : ℝ) : ℂ) = 0 := integral_undef hcon
    rw [hmellin _ (by simp)] at h0
    exact hGne h0
  have hvert : VerticalIntegrable (mellin K) (1 / 2 : ℝ) := by
    refine (integrable_Gt_half hB.stirling t).congr (Eventually.of_forall fun ξ => ?_)
    exact (hmellin _ (hw₁ ξ)).symm
  have hcontK : ContinuousAt K y :=
    (continuousOn_besselK (ν := I * t) (by simp)).continuousAt (Ioi_mem_nhds hy)
  have hinv := mellinInv_mellin_eq (1 / 2 : ℝ) K hy hconv hvert hcontK
  have hKA : K y = (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, A₁ ξ := by
    rw [← hinv]
    unfold mellinInv
    rw [Complex.real_smul]
    congr 1
    · push_cast; ring
    · congr 1
      funext ξ
      rw [smul_eq_mul, hmellin _ (hw₁ ξ), mul_comm]
  -- the contour shift
  set Pp := Pmb t y (I * t) with hPpd
  set Pm := Pmb t y (-(I * t)) with hPmd
  have hDeq : ∀ ξ : ℝ, hmb t y ((1 / 2 : ℝ) + ξ * I) - hmb t y ((-3 / 2 : ℝ) + ξ * I) =
      A₁ ξ - A₂ ξ - 2 / (I * t) *
        (Pp * (1 / ((1 / 2 : ℂ) + ξ * I - I * t) - 1 / ((-3 / 2 : ℂ) + ξ * I - I * t)) -
          Pm * (1 / ((1 / 2 : ℂ) + ξ * I - I * ((-t : ℝ) : ℂ)) -
            1 / ((-3 / 2 : ℂ) + ξ * I - I * ((-t : ℝ) : ℂ)))) := by
    intro ξ
    have hne : ∀ w : ℂ, w.re ≠ 0 → w ≠ I * t ∧ w ≠ -(I * t) := by
      intro w hw
      constructor
      · intro h; rw [h] at hw; simp at hw
      · intro h; rw [h] at hw; simp at hw
    obtain ⟨h11, h12⟩ := hne (((1 / 2 : ℝ) : ℂ) + ξ * I) (by simp)
    obtain ⟨h21, h22⟩ := hne (((-3 / 2 : ℝ) : ℂ) + ξ * I) (by simp)
    rw [hmb_eq t ht y h11 h12, hmb_eq t ht y h21 h22]
    have e2 : ((-3 / 2 : ℝ) : ℂ) + ξ * I = -3 / 2 + I * ξ := by push_cast; ring
    rw [e2, hA₁, hA₂]
    push_cast
    ring
  have hf₁ : Integrable (fun a : ℝ =>
      1 / ((1 / 2 : ℂ) + a * I - I * t) - 1 / ((-3 / 2 : ℂ) + a * I - I * t)) :=
    integrable_principal t
  have hf₂ : Integrable (fun a : ℝ => 1 / ((1 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ)) -
      1 / ((-3 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ))) :=
    integrable_principal (-t)
  have hA12 : Integrable (fun a : ℝ => A₁ a - A₂ a) := hint1.sub hint2
  have hPP : Integrable (fun a : ℝ =>
      Pp * (1 / ((1 / 2 : ℂ) + a * I - I * t) - 1 / ((-3 / 2 : ℂ) + a * I - I * t)) -
        Pm * (1 / ((1 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ)) -
          1 / ((-3 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ)))) :=
    (hf₁.const_mul Pp).sub (hf₂.const_mul Pm)
  have hRHS : Integrable (fun a : ℝ => A₁ a - A₂ a - 2 / (I * t) *
      (Pp * (1 / ((1 / 2 : ℂ) + a * I - I * t) - 1 / ((-3 / 2 : ℂ) + a * I - I * t)) -
        Pm * (1 / ((1 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ)) -
          1 / ((-3 / 2 : ℂ) + a * I - I * ((-t : ℝ) : ℂ))))) :=
    hA12.sub (hPP.const_mul _)
  have hD : Integrable (fun ξ : ℝ =>
      hmb t y ((1 / 2 : ℝ) + ξ * I) - hmb t y ((-3 / 2 : ℝ) + ξ * I)) :=
    hRHS.congr (Eventually.of_forall fun ξ => (hDeq ξ).symm)
  have h0 := integral_hmb_diff hB.stirling ht hy hD
  have hI : ∫ ξ : ℝ, (hmb t y ((1 / 2 : ℝ) + ξ * I) - hmb t y ((-3 / 2 : ℝ) + ξ * I)) =
      (∫ ξ, A₁ ξ) - (∫ ξ, A₂ ξ) -
        2 / (I * t) * (Pp * (2 * Real.pi) - Pm * (2 * Real.pi)) := by
    rw [integral_congr_ae (Eventually.of_forall hDeq), integral_sub hA12 (hPP.const_mul _),
      integral_sub hint1 hint2, integral_const_mul,
      integral_sub (hf₁.const_mul Pp) (hf₂.const_mul Pm),
      integral_const_mul, integral_const_mul, integral_principal t, integral_principal (-t)]
  have hz : (∫ ξ, A₁ ξ) - (∫ ξ, A₂ ξ) -
      2 / (I * t) * (Pp * (2 * Real.pi) - Pm * (2 * Real.pi)) = 0 := hI.symm.trans h0
  -- the residues
  have h4 : (2 : ℂ) ^ (2 : ℂ) = 4 := by norm_num
  have hPp : 2 / (I * t) * Pp = 1 / 2 * Complex.Gamma (I * t) * ((y / 2 : ℝ) : ℂ) ^ (-(I * t)) := by
    rw [hPpd]
    unfold Pmb
    rw [show (I * (t : ℂ) + I * t) / 2 + 1 = I * t + 1 by ring,
      show (I * (t : ℂ) - I * t) / 2 + 1 = 1 by ring,
      Complex.Gamma_add_one _ hIt, Complex.Gamma_one, half_cpow hy, neg_neg,
      Complex.cpow_sub _ _ two_ne_zero, h4]
    field_simp
    ring
  have hPm : -(2 / (I * t) * Pm) =
      1 / 2 * Complex.Gamma (-(I * t)) * ((y / 2 : ℝ) : ℂ) ^ (I * t) := by
    rw [hPmd]
    unfold Pmb
    rw [show (-(I * (t : ℂ)) + I * t) / 2 + 1 = 1 by ring,
      show (-(I * (t : ℂ)) - I * t) / 2 + 1 = -(I * t) + 1 by ring,
      Complex.Gamma_add_one _ (neg_ne_zero.2 hIt), Complex.Gamma_one, half_cpow hy, neg_neg,
      Complex.cpow_sub _ _ two_ne_zero, h4]
    field_simp
    ring
  have hπ : (1 / (2 * (Real.pi : ℂ))) * (2 * Real.pi) = 1 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  show K y = _
  rw [hKA]
  have hA : (∫ ξ, A₁ ξ) = (∫ ξ, A₂ ξ) + 2 / (I * t) * (Pp * (2 * Real.pi) - Pm * (2 * Real.pi)) := by
    linear_combination hz
  rw [hA]
  linear_combination hPp + hPm + (2 / (I * t) * (Pp - Pm)) * hπ

end Triples
