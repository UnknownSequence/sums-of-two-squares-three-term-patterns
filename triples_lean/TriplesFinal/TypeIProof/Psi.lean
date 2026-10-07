import TriplesFinal.Bessel.Mh
import TriplesFinal.Bessel.Integral
import TriplesFinal.Bessel.GammaBounds
import TriplesFinal.Bessel.MellinBarnesProof
import TriplesFinal.Poisson.HeegnerPoincare
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Bessel transform of `g_h`

* `|K_ν(y)| ≤ (2/y₀) e^(-y₀/2)` for `y ≥ y₀ > 0` and `|Re ν| ≤ 1/2` (the integrability of
  `e^(-y cosh σ + νσ)` and the continuity of `K_ν` on `(0, ∞)` are in `Bessel/Continuity.lean`);
* `ǧ_h(t) = (X/K) Y^(-1/2) Ψ_h(t)` with `Ψ_h(t) = ∫_{1/2}^{1} w₁(s) a_h(s) K_{it}(2πhYs) ds`
  (`besselTransform_gh`, equation (10.2) of the paper: the substitution `y = Ys`);
* on the spectrum `𝒥₀` (`|Im t| ≤ 1/2`), the truncated integral representation of `K_{it}`
  (Lemma 11.1) gives `Ψ_h(t) = ½ ∫∫_{|σ| ≤ ℓ} w₁ a_h e^(-2πhYs cosh σ) e^(itσ) + O(e^(-y₀e^ℓ/2))`
  (`PsiH_J0`);
* on `𝒥₁` (real `t ≠ 0`), the Mellin–Barnes formula (Lemma 11.2) integrated against `w₁ a_h`
  gives `Ψ_h(t) = ½Γ(it)(πhY)^(-it) M_h(it) + ½Γ(-it)(πhY)^(it) M_h(-it) + (1/2π) ∫ G_t(w)
  (2πhY)^(-w) M_h(w) dξ` on `Re w = -3/2` (`PsiH_J1`).

Paper: §10.2 (equation (10.2)) and §§12.2–12.4.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

/-- `|K_ν(y)| ≤ (2/y₀) e^(-y₀/2)` for `y ≥ y₀ > 0` and `|Re ν| ≤ 1/2`. -/
theorem norm_besselK_le {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {y y₀ : ℝ} (hy₀ : 0 < y₀) (hy : y₀ ≤ y) :
    ‖besselK ν y‖ ≤ 2 / y₀ * Real.exp (-(y₀ / 2)) := by
  have h := besselK_tail hν (V := 1) le_rfl hy₀ hy
  rw [Real.log_one, mul_one] at h
  have hs : {σ : ℝ | 0 < |σ|} = {0}ᶜ := by
    ext σ; simp [abs_pos]
  rw [hs, restrict_compl_singleton] at h
  exact h

/-! ### The Bessel transform of `g_h` -/

/-- `Ψ_h(t) = ∫_{1/2}^{1} w₁(s) a_h(s) K_{it}(2πhYs) ds`. -/
noncomputable def PsiH (ψ₁ ψ₂ : ℝ → ℂ) (X K Y h : ℝ) (t : ℂ) : ℂ :=
  ∫ s in (1 / 2 : ℝ)..1, gMh ψ₁ ψ₂ X K h s * besselK (I * t) (2 * Real.pi * h * Y * s)

/-- `g_h(Ys) = ψ₁(1/s) (Xs/K) a_h(s)` for `s > 0`, with `Y = √N/(EK)`. -/
theorem gh_Ypar_mul {E H : ℕ} (hE : 0 < E) (hH : 0 < H) {X K : ℝ} (hK : 0 < K)
    (ψ₁ ψ₂ : ℝ → ℂ) (h : ℕ) {s : ℝ} (hs : 0 < s) :
    gh E H X K ψ₁ ψ₂ h (Ypar E H K * s) =
      ψ₁ (1 / s) * ((X * s / K : ℝ) : ℂ) * ah ψ₂ X K h s := by
  have hN : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  unfold gh Ypar ah
  have e1 : Real.sqrt ((E * H : ℕ) : ℝ) /
      (E * K * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K) * s)) = 1 / s := by
    field_simp
  have e2 : (E : ℝ) * X * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K) * s) /
      Real.sqrt ((E * H : ℕ) : ℝ) = X * s / K := by
    field_simp
  have e3 : (E : ℝ) * ((h : ℤ) : ℝ) * X * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K) * s) /
      Real.sqrt ((E * H : ℕ) : ℝ) = h * X * s / K := by
    push_cast
    field_simp
  rw [e1, e2, e3]

theorem Ypar_pos {E H : ℕ} (hE : 0 < E) (hH : 0 < H) {K : ℝ} (hK : 0 < K) : 0 < Ypar E H K := by
  unfold Ypar
  have : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- **The Bessel transform of `g_h`**: `ǧ_h(t) = (X/K) Y^(-1/2) Ψ_h(t)` (substituting `y = Ys`). -/
theorem besselTransform_gh {E H : ℕ} (hE : 0 < E) (hH : 0 < H) {X K : ℝ} (hK : 0 < K)
    {ψ₁ ψ₂ : ℝ → ℂ} (hs₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (h : ℕ) (t : ℂ) :
    besselTransform (gh E H X K ψ₁ ψ₂ h) h t =
      ((X / K * Ypar E H K ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * PsiH ψ₁ ψ₂ X K (Ypar E H K) h t := by
  set Y := Ypar E H K with hYdef
  have hY : 0 < Y := Ypar_pos hE hH hK
  unfold besselTransform
  set F : ℝ → ℂ := fun y => gh E H X K ψ₁ ψ₂ h y *
    besselK (I * t) (2 * Real.pi * |((h : ℤ) : ℝ)| * y) * (y : ℂ) ^ (-(3 : ℂ) / 2) with hF
  have hsub := integral_comp_mul_left_Ioi' F 0 hY
  rw [mul_zero] at hsub
  rw [← hsub]
  -- the integrand after the substitution
  have hpt : ∀ s ∈ Ioi (0 : ℝ), Y • F (Y * s) =
      ((X / K * Y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (gMh ψ₁ ψ₂ X K h s * besselK (I * t) (2 * Real.pi * h * Y * s)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    simp only [hF]
    rw [hYdef, gh_Ypar_mul hE hH hK ψ₁ ψ₂ h hs0, ← hYdef]
    have habs : |((h : ℤ) : ℝ)| = h := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg h)
    rw [habs]
    have hcpow : ((Y * s : ℝ) : ℂ) ^ (-(3 : ℂ) / 2) =
        (((Y * s) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast; ring_nf
    push_cast at hcpow ⊢
    rw [hcpow]
    unfold gMh w1
    have hreal : Y * (X * s / K) * (Y * s) ^ (-(3 / 2 : ℝ)) =
        X / K * Y ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) := by
      rw [Real.mul_rpow hY.le hs0.le]
      have e1 : Y * Y ^ (-(3 / 2 : ℝ)) = Y ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' hY.le (by norm_num)]; norm_num
      have e2 : s * s ^ (-(3 / 2 : ℝ)) = s ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' hs0.le (by norm_num)]; norm_num
      calc Y * (X * s / K) * (Y ^ (-(3 / 2 : ℝ)) * s ^ (-(3 / 2 : ℝ)))
          = X / K * (Y * Y ^ (-(3 / 2 : ℝ))) * (s * s ^ (-(3 / 2 : ℝ))) := by ring
        _ = _ := by rw [e1, e2]
    have hreal' : ((Y : ℂ) * ((X : ℂ) * (s : ℂ) / (K : ℂ)) *
        (((Y * s) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) =
        (((X / K * Y ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) := by
      rw [← hreal]; push_cast; ring
    rw [Complex.real_smul]
    calc (Y : ℂ) * (ψ₁ (1 / s) * ((X : ℂ) * (s : ℂ) / (K : ℂ)) * ah ψ₂ X K (h : ℝ) s *
          besselK (I * t) (2 * Real.pi * h * (Y * s)) * (((Y * s) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))
        = ((Y : ℂ) * ((X : ℂ) * (s : ℂ) / (K : ℂ)) * (((Y * s) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) *
          (ψ₁ (1 / s) * ah ψ₂ X K (h : ℝ) s * besselK (I * t) (2 * Real.pi * h * (Y * s))) := by
          ring
      _ = _ := by
          rw [hreal']
          push_cast
          rw [show (2 : ℝ) * Real.pi * h * (Y * s) = 2 * Real.pi * h * Y * s by ring]
          ring
  rw [← integral_smul, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  congr 1
  -- the integral over `(0, ∞)` is the integral over `[1/2, 1]`
  unfold PsiH
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  have hsub' : Icc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := fun s hs => by
    simp only [mem_Icc] at hs; simp only [mem_Ioi]; linarith
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub' ?_
  intro s hs
  by_cases hg : gMh ψ₁ ψ₂ X K h s = 0
  · rw [hg, zero_mul]
  · exact absurd (gMh_support hs₁ X K h hg) (fun h' => hs.2 ⟨h'.1, h'.2⟩)

/-- `s ↦ g(s) K_{it}(2πhYs)` is continuous on `[1/2, 1]`. -/
theorem continuousOn_gMh_besselK {ψ₁ ψ₂ : ℝ → ℂ} (hψ₁ : ContDiff ℝ ∞ ψ₁)
    (hs₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hψ₂ : Continuous ψ₂)
    (hs₂ : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {X K Y h : ℝ} (hY : 0 < Y) (hh : 0 < h) {ν : ℂ}
    (hν : |ν.re| ≤ 1 / 2) :
    ContinuousOn (fun s => gMh ψ₁ ψ₂ X K h s * besselK ν (2 * Real.pi * h * Y * s))
      (Icc (1 / 2 : ℝ) 1) := by
  apply ContinuousOn.mul (contDiff_gMh hψ₁ hs₁ hψ₂ hs₂ X K h).continuous.continuousOn
  apply (continuousOn_besselK hν).comp (by fun_prop)
  intro s hs
  simp only [mem_Icc] at hs
  simp only [mem_Ioi]
  have : 0 < s := by linarith
  positivity

/-- `K_ν(y) = ½ ∫_{-ℓ}^{ℓ} e^(-y cosh σ + νσ) dσ + ½ ∫_{|σ| > ℓ} e^(-y cosh σ + νσ) dσ`. -/
theorem besselK_split {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) {y : ℝ} (hy : 0 < y) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    besselK ν y =
      (1 / 2 : ℂ) * (∫ σ in (-ℓ)..ℓ, Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ)) +
        (1 / 2 : ℂ) * ∫ σ in {σ : ℝ | ℓ < |σ|},
          Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ) := by
  unfold besselK
  rw [← mul_add]
  congr 1
  have hint := integrable_besselK_integrand hν hy
  have hc : (Icc (-ℓ) ℓ)ᶜ = {σ : ℝ | ℓ < |σ|} := by
    ext σ
    simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, ← abs_le, not_le]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc, ← hc,
    integral_add_compl measurableSet_Icc hint]

/-- **`Ψ_h` on the spectrum `𝒥₀`** (Lemma 11.1): for `|Im t| ≤ 1/2` and `ℓ ≥ 0`,
`Ψ_h(t) = ½ ∫_{1/2}^{1} ∫_{-ℓ}^{ℓ} w₁(s) a_h(s) e^(-2πhYs cosh σ) e^(itσ) dσ ds + r` with
`|r| ≤ (A/y₀) e^(-y₀ e^ℓ/2)`, where `|w₁ a_h| ≤ A` on `[1/2, 1]` and `y₀ ≤ πhY`. -/
theorem PsiH_J0 {ψ₁ ψ₂ : ℝ → ℂ} (hψ₁ : ContDiff ℝ ∞ ψ₁)
    (hs₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hψ₂ : Continuous ψ₂)
    (hs₂ : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {X K Y h : ℝ} (hY : 0 < Y) (hh : 0 < h) {t : ℂ}
    (ht : |t.im| ≤ 1 / 2) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hy₀h : y₀ ≤ Real.pi * h * Y) {A : ℝ}
    (hA : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ‖gMh ψ₁ ψ₂ X K h s‖ ≤ A) :
    ∃ r : ℂ, ‖r‖ ≤ A / y₀ * Real.exp (-(y₀ * Real.exp ℓ / 2)) ∧
      PsiH ψ₁ ψ₂ X K Y h t = (1 / 2 : ℂ) * (∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-ℓ)..ℓ,
        gMh ψ₁ ψ₂ X K h s * ((Real.exp (-(2 * Real.pi * h * Y * s * Real.cosh σ)) : ℂ) *
          Complex.exp (I * t * σ))) + r := by
  set ν := I * t with hνdef
  have hν : |ν.re| ≤ 1 / 2 := by
    simp only [hνdef, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, abs_neg]; exact ht
  set F : ℝ → ℝ → ℂ := fun s σ =>
    Complex.exp (-((2 * Real.pi * h * Y * s * Real.cosh σ : ℝ) : ℂ) + ν * σ) with hF
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF]; fun_prop
  set main : ℝ → ℂ := fun s => (1 / 2 : ℂ) * ∫ σ in (-ℓ)..ℓ, F s σ with hmain
  set tail : ℝ → ℂ := fun s => (1 / 2 : ℂ) * ∫ σ in {σ : ℝ | ℓ < |σ|}, F s σ with htail
  have hsplit : ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      besselK ν (2 * Real.pi * h * Y * s) = main s + tail s := by
    intro s hs
    have hs0 : 0 < s := by simp only [mem_Icc] at hs; linarith
    have := besselK_split hν (y := 2 * Real.pi * h * Y * s) (by positivity) hℓ
    rw [this]
  have hy₀s : ∀ s ∈ Icc (1 / 2 : ℝ) 1, y₀ ≤ 2 * Real.pi * h * Y * s := by
    intro s hs
    simp only [mem_Icc] at hs
    have : Real.pi * h * Y ≤ 2 * Real.pi * h * Y * s := by
      have h1 : 0 ≤ Real.pi * h * Y := by positivity
      nlinarith
    linarith
  have htail_le : ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      ‖tail s‖ ≤ 2 / y₀ * Real.exp (-(y₀ * Real.exp ℓ / 2)) := by
    intro s hs
    have := besselK_tail hν (V := Real.exp ℓ) (by simpa using Real.one_le_exp hℓ) hy₀
      (hy₀s s hs)
    rw [Real.log_exp] at this
    exact this
  -- interval integrability
  have hK_int : IntervalIntegrable (fun s => gMh ψ₁ ψ₂ X K h s *
      besselK ν (2 * Real.pi * h * Y * s)) volume (1 / 2) 1 :=
    (continuousOn_gMh_besselK hψ₁ hs₁ hψ₂ hs₂ hY hh hν).intervalIntegrable_of_Icc (by norm_num)
  have hmain_c : Continuous main := by
    simp only [hmain]
    exact continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hFc _ _)
  have hg_c : Continuous (gMh ψ₁ ψ₂ X K h) := (contDiff_gMh hψ₁ hs₁ hψ₂ hs₂ X K h).continuous
  have hmain_int : IntervalIntegrable (fun s => gMh ψ₁ ψ₂ X K h s * main s) volume (1 / 2) 1 :=
    (hg_c.mul hmain_c).intervalIntegrable _ _
  refine ⟨∫ s in (1 / 2 : ℝ)..1, gMh ψ₁ ψ₂ X K h s * tail s, ?_, ?_⟩
  · have hle : ∀ s ∈ Ι (1 / 2 : ℝ) 1, ‖gMh ψ₁ ψ₂ X K h s * tail s‖ ≤
        A * (2 / y₀ * Real.exp (-(y₀ * Real.exp ℓ / 2))) := by
      intro s hs
      rw [uIoc_of_le (by norm_num)] at hs
      have hs' : s ∈ Icc (1 / 2 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      rw [norm_mul]
      exact mul_le_mul (hA s hs') (htail_le s hs') (norm_nonneg _)
        ((norm_nonneg _).trans (hA s hs'))
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hle).trans (le_of_eq ?_)
    rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
    ring
  · unfold PsiH
    have hcongr : ∀ s ∈ uIcc (1 / 2 : ℝ) 1, gMh ψ₁ ψ₂ X K h s *
        besselK (I * t) (2 * Real.pi * h * Y * s) =
        gMh ψ₁ ψ₂ X K h s * main s + gMh ψ₁ ψ₂ X K h s * tail s := by
      intro s hs
      rw [uIcc_of_le (by norm_num)] at hs
      rw [← hνdef, hsplit s hs, mul_add]
    rw [intervalIntegral.integral_congr hcongr]
    have htail_int : IntervalIntegrable (fun s => gMh ψ₁ ψ₂ X K h s * tail s) volume (1 / 2) 1 := by
      have : IntervalIntegrable (fun s => gMh ψ₁ ψ₂ X K h s * besselK ν (2 * Real.pi * h * Y * s) -
          gMh ψ₁ ψ₂ X K h s * main s) volume (1 / 2) 1 := hK_int.sub hmain_int
      refine this.congr ?_
      intro s hs
      rw [uIoc_of_le (by norm_num)] at hs
      have hs' : s ∈ Icc (1 / 2 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      simp only
      rw [hsplit s hs']
      ring
    rw [intervalIntegral.integral_add hmain_int htail_int]
    congr 1
    simp only [hmain]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    rw [← mul_assoc, mul_comm (gMh ψ₁ ψ₂ X K h s), mul_assoc, ← intervalIntegral.integral_const_mul]
    congr 1
    congr 1
    ext σ
    simp only [hF]
    rw [Complex.exp_add, Complex.ofReal_exp]
    push_cast
    ring_nf

/-- `s ↦ s^z` is continuous on `(0, ∞)`. -/
theorem continuousOn_ofReal_cpow (z : ℂ) :
    ContinuousOn (fun s : ℝ => (s : ℂ) ^ z) (Ioi 0) := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.cpow (by fun_prop) continuousAt_const
  exact Complex.ofReal_mem_slitPlane.2 hs

/-- `(ab)^z = a^z b^z` for `a, b ≥ 0`. -/
theorem ofReal_mul_cpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) :
    ((a * b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ z := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg ha hb z

/-- **`Ψ_h` on `𝒥₁`** (Lemma 11.2 integrated against `w₁ a_h`): for real `τ ≠ 0`, with
`w = -3/2 + iξ`,
`Ψ_h(τ) = ½Γ(iτ)(πhY)^(-iτ) M_h(iτ) + ½Γ(-iτ)(πhY)^(iτ) M_h(-iτ)
  + (1/2π) ∫ G_τ(w) (2πhY)^(-w) M_h(w) dξ`. -/
theorem PsiH_J1 (hB : BesselAssumptions) {ψ₁ ψ₂ : ℝ → ℂ} (hψ₁ : ContDiff ℝ ∞ ψ₁)
    (hs₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hψ₂ : Continuous ψ₂)
    (hs₂ : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {X K Y h : ℝ} (hY : 0 < Y) (hh : 0 < h) {τ : ℝ}
    (hτ : τ ≠ 0) :
    PsiH ψ₁ ψ₂ X K Y h τ =
      (1 / 2 : ℂ) * Complex.Gamma (I * τ) * ((Real.pi * h * Y : ℝ) : ℂ) ^ (-(I * τ)) *
          Mh ψ₁ ψ₂ X K h (I * τ) +
        (1 / 2 : ℂ) * Complex.Gamma (-(I * τ)) * ((Real.pi * h * Y : ℝ) : ℂ) ^ (I * τ) *
          Mh ψ₁ ψ₂ X K h (-(I * τ)) +
        (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, Gt τ (-3 / 2 + I * ξ) *
          ((2 * Real.pi * h * Y : ℝ) : ℂ) ^ (-(-3 / 2 + I * ξ)) * Mh ψ₁ ψ₂ X K h (-3 / 2 + I * ξ) := by
  set g := gMh ψ₁ ψ₂ X K h with hgdef
  have hg_c : Continuous g := (contDiff_gMh hψ₁ hs₁ hψ₂ hs₂ X K h).continuous
  set P : ℝ := Real.pi * h * Y with hP
  set P₂ : ℝ := 2 * Real.pi * h * Y with hP₂
  have hP0 : 0 < P := by positivity
  have hP₂0 : 0 < P₂ := by positivity
  set w : ℝ → ℂ := fun ξ => -3 / 2 + I * ξ with hw
  set a : ℝ → ℂ := fun s => (1 / 2 : ℂ) * Complex.Gamma (I * τ) * (P : ℂ) ^ (-(I * τ)) *
    (s : ℂ) ^ (-(I * τ)) with ha
  set b : ℝ → ℂ := fun s => (1 / 2 : ℂ) * Complex.Gamma (-(I * τ)) * (P : ℂ) ^ (I * τ) *
    (s : ℂ) ^ (I * τ) with hb
  set c : ℝ → ℂ := fun s => (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, Gt τ (w ξ) * (P₂ : ℂ) ^ (-(w ξ)) *
    (s : ℂ) ^ (-(w ξ)) with hc
  have hsplit : ∀ s ∈ Icc (1 / 2 : ℝ) 1, besselK (I * τ) (2 * Real.pi * h * Y * s) =
      a s + b s + c s := by
    intro s hs
    have hs0 : 0 < s := by simp only [mem_Icc] at hs; linarith
    rw [(mellin_barnes hB hτ (y := 2 * Real.pi * h * Y * s) (by positivity)).2]
    have e1 : (2 * Real.pi * h * Y * s / 2 : ℝ) = P * s := by rw [hP]; ring
    have e2 : (2 * Real.pi * h * Y * s : ℝ) = P₂ * s := by rw [hP₂]
    simp only [ha, hb, hc]
    rw [e1, ofReal_mul_cpow hP0.le hs0.le, ofReal_mul_cpow hP0.le hs0.le]
    congr 1
    · ring
    · congr 1
      apply integral_congr_ae
      refine Eventually.of_forall fun ξ => ?_
      simp only
      rw [e2, ofReal_mul_cpow hP₂0.le hs0.le]
      ring
  -- continuity of the main terms
  have ha_c : ContinuousOn (fun s => g s * a s) (Icc (1 / 2 : ℝ) 1) := by
    apply hg_c.continuousOn.mul
    simp only [ha]
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_ofReal_cpow _).mono (fun s hs => by
      simp only [mem_Icc] at hs; simp only [mem_Ioi]; linarith)
  have hb_c : ContinuousOn (fun s => g s * b s) (Icc (1 / 2 : ℝ) 1) := by
    apply hg_c.continuousOn.mul
    simp only [hb]
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_ofReal_cpow _).mono (fun s hs => by
      simp only [mem_Icc] at hs; simp only [mem_Ioi]; linarith)
  have ha_int : IntervalIntegrable (fun s => g s * a s) volume (1 / 2) 1 :=
    ha_c.intervalIntegrable_of_Icc (by norm_num)
  have hb_int : IntervalIntegrable (fun s => g s * b s) volume (1 / 2) 1 :=
    hb_c.intervalIntegrable_of_Icc (by norm_num)
  have hν : |(I * (τ : ℂ)).re| ≤ 1 / 2 := by simp
  have hK_int : IntervalIntegrable (fun s => g s * besselK (I * τ) (2 * Real.pi * h * Y * s))
      volume (1 / 2) 1 :=
    (continuousOn_gMh_besselK hψ₁ hs₁ hψ₂ hs₂ hY hh hν).intervalIntegrable_of_Icc (by norm_num)
  have hc_int : IntervalIntegrable (fun s => g s * c s) volume (1 / 2) 1 := by
    refine ((hK_int.sub ha_int).sub hb_int).congr ?_
    intro s hs
    rw [uIoc_of_le (by norm_num)] at hs
    simp only
    rw [hsplit s ⟨hs.1.le, hs.2⟩]
    ring
  unfold PsiH
  have hcongr : ∀ s ∈ uIcc (1 / 2 : ℝ) 1, g s * besselK (I * τ) (2 * Real.pi * h * Y * s) =
      g s * a s + g s * b s + g s * c s := by
    intro s hs
    rw [uIcc_of_le (by norm_num)] at hs
    rw [hsplit s hs]; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add (ha_int.add hb_int)
    hc_int, intervalIntegral.integral_add ha_int hb_int]
  congr 1
  congr 1
  · -- the term with `Γ(iτ)`
    simp only [ha]
    unfold Mh
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext s
    simp only [hgdef, gMh]; ring
  · -- the term with `Γ(-iτ)`
    simp only [hb]
    unfold Mh
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext s
    simp only [hgdef, gMh, neg_neg]; ring
  · -- the remainder, by Fubini
    obtain ⟨Ag, hAg⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hg_c.continuousOn (s := Icc (1 / 2 : ℝ) 1))
    set f : ℝ → ℝ → ℂ := fun s ξ => g s * (Gt τ (w ξ) * (P₂ : ℂ) ^ (-(w ξ)) *
      (s : ℂ) ^ (-(w ξ))) with hf
    have hgsupp : ∀ s, g s ≠ 0 → s ∈ Icc (1 / 2 : ℝ) 1 := fun s hs =>
      gMh_support hs₁ X K h hs
    have hwre : ∀ ξ : ℝ, (-(w ξ)).re = 3 / 2 := by
      intro ξ; simp only [hw]; simp; norm_num
    have hbound : ∀ s ξ, ‖f s ξ‖ ≤ (Ag * P₂ ^ (3 / 2 : ℝ)) * ‖Gt τ (w ξ)‖ := by
      intro s ξ
      by_cases hgs : g s = 0
      · simp only [hf, hgs, zero_mul, norm_zero]
        have := (norm_nonneg _).trans (hAg (1 / 2) ⟨le_refl _, by norm_num⟩)
        positivity
      · have hs := hgsupp s hgs
        have hs0 : 0 < s := by simp only [mem_Icc] at hs; linarith
        simp only [hf]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hP₂0,
          Complex.norm_cpow_eq_rpow_re_of_pos hs0, hwre]
        have h1 : s ^ (3 / 2 : ℝ) ≤ 1 :=
          Real.rpow_le_one hs0.le hs.2 (by norm_num)
        have h2 := hAg s hs
        have h3 : 0 ≤ P₂ ^ (3 / 2 : ℝ) := by positivity
        calc ‖g s‖ * (‖Gt τ (w ξ)‖ * P₂ ^ (3 / 2 : ℝ) * s ^ (3 / 2 : ℝ))
            ≤ Ag * (‖Gt τ (w ξ)‖ * P₂ ^ (3 / 2 : ℝ) * 1) := by
              apply mul_le_mul h2 _ (by positivity) ((norm_nonneg _).trans h2)
              gcongr
          _ = Ag * P₂ ^ (3 / 2 : ℝ) * ‖Gt τ (w ξ)‖ := by ring
    have hGt_int : Integrable (fun ξ : ℝ => Gt τ (w ξ)) := integrable_Gt hB τ
    have hmeas : Measurable (Function.uncurry f) := by
      have h1 : Measurable (fun p : ℝ × ℝ => g p.1) := hg_c.measurable.comp measurable_fst
      have h2 : Measurable (fun p : ℝ × ℝ => Gt τ (w p.2)) :=
        ((continuous_Gt_line.comp (Continuous.prodMk continuous_const continuous_id)).measurable).comp
          measurable_snd
      have h3 : Measurable (fun p : ℝ × ℝ => (P₂ : ℂ) ^ (-(w p.2))) := by
        simp only [hw]; fun_prop
      have h4 : Measurable (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) ^ (-(w p.2))) := by
        simp only [hw]
        exact Measurable.pow (by fun_prop) (by fun_prop)
      exact h1.mul ((h2.mul h3).mul h4)
    have hfint : Integrable (Function.uncurry f) ((volume.restrict (Ioc (1 / 2 : ℝ) 1)).prod volume) := by
      have hdom : Integrable (fun p : ℝ × ℝ => (Ag * P₂ ^ (3 / 2 : ℝ)) * ‖Gt τ (w p.2)‖)
          ((volume.restrict (Ioc (1 / 2 : ℝ) 1)).prod volume) :=
        (integrable_const (μ := volume.restrict (Ioc (1 / 2 : ℝ) 1))
          (Ag * P₂ ^ (3 / 2 : ℝ))).mul_prod hGt_int.norm
      exact hdom.mono' hmeas.aestronglyMeasurable
        (Eventually.of_forall fun p => hbound p.1 p.2)
    have hswap := integral_integral_swap hfint
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hin : ∀ s, g s * c s = (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, f s ξ := by
      intro s
      simp only [hc, hf]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
      congr 1; ext ξ; ring
    simp only [hin]
    rw [integral_const_mul, hswap]
    congr 1
    congr 1; ext ξ
    simp only [hf]
    unfold Mh
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
    congr 1; ext s
    simp only [hgdef, gMh, hw]; ring

end Triples
