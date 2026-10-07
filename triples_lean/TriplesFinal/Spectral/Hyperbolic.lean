import TriplesFinal.Heegner.Pairs
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Hyperbolic integrals (for Lemma 10.7)

Integration on `ℍ` against point-pair invariants, with `dμ = dx dy / y²` (Mathlib's
`GL₂(ℝ)`-invariant measure `volume` on `ℍ`):

* integration in coordinates (`integral_eq_iterated`);
* the **radial formula** for the Selberg transform (`integral_radial_cosh`):
  `∫_ℍ φ(u(z, i)) y^s dμ(z) = ∫_ℝ 2 cosh(r(s - 1/2)) g_φ(r) dr`, where
  `g_φ(r) = Q_φ(sinh²(r/2))` and `Q_φ(a) = ∫ φ(w² + a) dw`; the substitution is
  `x = 2√y w`, `y = e^r`;
* the **area of a disc**: `∫_ℍ φ(u(z, i)) dμ(z) = 4 ∫ Q_φ(v²) dv` (`v = sinh(r/2)`), so
  `4πU ≤ ∫_ℍ φ(u(z, i)) dμ(z) ≤ 4πU'` when `1_{[0, U]} ≤ φ ≤ 1_{[0, U']}`
  (`le_integral_area`, `integral_area_le`);
* **invariance**: `∫_ℍ F(u(z, v)) dμ(v) = ∫_ℍ F(u(v, i)) dμ(v)` (`integral_pointPair_left`);
* **finiteness**: only finitely many `γ ∈ Γ₀(q)` have `u(z, γw) ≤ R` (`finite_pointPair_le`).

Paper: §10.5 (proof of Lemma 10.7).
-/

namespace Triples

open MeasureTheory UpperHalfPlane Complex
open scoped NNReal MatrixGroups

namespace Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integration on `ℍ`** as an integral over `{Im w > 0} ⊆ ℂ` with density `1/(Im w)²`. -/
theorem integral_eq_setIntegral_complex (F : ℍ → E) :
    ∫ z : ℍ, F z = ∫ w in {w : ℂ | 0 < w.im}, (1 / w.im ^ 2 : ℝ) • F (ofComplex w) := by
  rw [volume_def, integral_withDensity_eq_integral_smul]
  · have h := measurableEmbedding_coe.integral_map (μ := volume.comap UpperHalfPlane.coe)
      (fun w : ℂ => (1 / w.im ^ 2 : ℝ) • F (ofComplex w))
    rw [measurableEmbedding_coe.map_comap, range_coe] at h
    rw [h]
    congr 1
    ext z
    rw [ofComplex_apply]
    rw [NNReal.smul_def]
    congr 1
    simp [NNReal.coe_pow, coe_im]
  · fun_prop

/-- `∫_{Im w > 0} G = ∫_{ℝ × (0, ∞)} G(x + iy)`. -/
theorem setIntegral_upper_eq_prod (G : ℂ → E) :
    ∫ w in {w : ℂ | 0 < w.im}, G w =
      ∫ p in (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ), G ⟨p.1, p.2⟩ := by
  have h := (volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    measurableEquivRealProd.symm.measurableEmbedding G {w : ℂ | 0 < w.im}
  rw [← h]
  have hpre : measurableEquivRealProd.symm ⁻¹' {w : ℂ | 0 < w.im} =
      (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    ext p
    simp [measurableEquivRealProd_symm_apply]
  rw [hpre]
  rfl

/-- **Fubini** on `ℝ × (0, ∞)`, with the `y`-integral outside. -/
theorem setIntegral_prod_Ioi {H : ℝ × ℝ → E}
    (hH : IntegrableOn H ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))) :
    ∫ p in (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ), H p =
      ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, H (x, y) := by
  rw [Measure.volume_eq_prod] at hH ⊢
  rw [← setIntegral_prod_swap]
  have hH' : IntegrableOn (fun z : ℝ × ℝ => H z.swap) (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
      (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hH ⊢
    exact hH.swap
  rw [setIntegral_prod _ hH']
  simp

/-- **Integration on `ℍ`** in coordinates, for `F(x + iy)/y²` integrable on `ℝ × (0, ∞)`. -/
theorem integral_eq_iterated (F : ℍ → E)
    (hF : IntegrableOn (fun p : ℝ × ℝ => (1 / p.2 ^ 2 : ℝ) • F (ofComplex ⟨p.1, p.2⟩))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))) :
    ∫ z : ℍ, F z = ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, (1 / y ^ 2 : ℝ) • F (ofComplex ⟨x, y⟩) := by
  rw [integral_eq_setIntegral_complex, setIntegral_upper_eq_prod]
  exact setIntegral_prod_Ioi hF

/-- `u(x + iy, i) = (x² + (y - 1)²)/(4y)`. -/
theorem pointPair_ofComplex_I {x y : ℝ} (hy : 0 < y) :
    pointPair (ofComplex ⟨x, y⟩) I = (x ^ 2 + (y - 1) ^ 2) / (4 * y) := by
  have h : ((ofComplex ⟨x, y⟩ : ℍ) : ℂ) = ⟨x, y⟩ := by
    rw [ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
  unfold pointPair
  rw [h]
  have him : (ofComplex ⟨x, y⟩ : ℍ).im = y := by
    rw [UpperHalfPlane.im, h]
  rw [him, UpperHalfPlane.I_im]
  have : ‖(⟨x, y⟩ : ℂ) - (I : ℍ)‖ ^ 2 = x ^ 2 + (y - 1) ^ 2 := by
    rw [UpperHalfPlane.coe_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  rw [this, mul_one]

theorem im_ofComplex {x y : ℝ} (hy : 0 < y) : (ofComplex ⟨x, y⟩ : ℍ).im = y := by
  have h : ((ofComplex ⟨x, y⟩ : ℍ) : ℂ) = ⟨x, y⟩ := by
    rw [ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
  rw [UpperHalfPlane.im, h]

/-- `Q_φ(a) = ∫ φ(w² + a) dw`. -/
noncomputable def Qφ (φ : ℝ → ℝ) (a : ℝ) : ℝ := ∫ w : ℝ, φ (w ^ 2 + a)

/-- `∫ φ((x² + (y-1)²)/(4y)) dx = 2√y Q_φ((y-1)²/(4y))`. -/
theorem integral_x (φ : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ, φ ((x ^ 2 + (y - 1) ^ 2) / (4 * y)) = 2 * Real.sqrt y * Qφ φ ((y - 1) ^ 2 / (4 * y)) := by
  have hs : 0 < 2 * Real.sqrt y := by positivity
  have h := Measure.integral_comp_mul_left (fun x : ℝ => φ ((x ^ 2 + (y - 1) ^ 2) / (4 * y)))
    (2 * Real.sqrt y)
  have e : ∀ w : ℝ, ((2 * Real.sqrt y * w) ^ 2 + (y - 1) ^ 2) / (4 * y) =
      w ^ 2 + (y - 1) ^ 2 / (4 * y) := by
    intro w
    rw [mul_pow, mul_pow, Real.sq_sqrt hy.le]
    field_simp
    ring
  simp only [e] at h
  unfold Qφ
  rw [h, abs_of_pos (inv_pos.2 hs), smul_eq_mul]
  field_simp

/-- The integrand in coordinates: `(1/y²) φ((x² + (y-1)²)/(4y)) y^s`. -/
noncomputable def Gs (φ : ℝ → ℝ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 / p.2 ^ 2 : ℝ) • ((φ ((p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2)) : ℂ) * (p.2 : ℂ) ^ s)

/-- On the support of `φ(u(z, i))` (with `φ = 0` on `(A, ∞)`): `|x| ≤ 2 + 4A` and
`1/(2 + 4A) ≤ y ≤ 2 + 4A`. -/
theorem support_bounds {A x y : ℝ} (hA : 0 ≤ A) (hy : 0 < y)
    (h : (x ^ 2 + (y - 1) ^ 2) / (4 * y) ≤ A) :
    |x| ≤ 2 + 4 * A ∧ 1 / (2 + 4 * A) ≤ y ∧ y ≤ 2 + 4 * A := by
  rw [div_le_iff₀ (by positivity)] at h
  have hy2 : y ≤ 2 + 4 * A := by nlinarith [sq_nonneg x]
  refine ⟨?_, ?_, hy2⟩
  · have : x ^ 2 ≤ (2 + 4 * A) ^ 2 := by nlinarith [sq_nonneg (y - 1)]
    exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.2 h
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg x]

/-- `y^σ ≤ a^σ + b^σ` for `a ≤ y ≤ b`, `0 < a`. -/
theorem rpow_le_add_of_mem {a b y σ : ℝ} (ha : 0 < a) (hay : a ≤ y) (hyb : y ≤ b) :
    y ^ σ ≤ a ^ σ + b ^ σ := by
  have hy : 0 < y := lt_of_lt_of_le ha hay
  rcases le_or_gt 0 σ with h | h
  · have := Real.rpow_le_rpow hy.le hyb h
    have : 0 ≤ a ^ σ := Real.rpow_nonneg ha.le _
    linarith
  · have := Real.rpow_le_rpow_of_nonpos ha hay h.le
    have : 0 ≤ b ^ σ := Real.rpow_nonneg (le_trans ha.le (hay.trans hyb)) _
    linarith

theorem integrableOn_Gs {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (s : ℂ) :
    IntegrableOn (Gs φ s) ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
  set c : ℝ := 2 + 4 * A with hc
  have hc0 : 0 < c := by positivity
  set box := Set.Icc (-c) c ×ˢ Set.Icc (1 / c) c with hbox
  have hmeas : Measurable (Gs φ s) := by
    have h1 : Measurable (fun p : ℝ × ℝ => (1 / p.2 ^ 2 : ℝ)) := by fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ =>
        (φ ((p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2)) : ℂ) * (p.2 : ℂ) ^ s) := by
      apply Measurable.mul
      · exact Complex.measurable_ofReal.comp (hφm.comp (by fun_prop))
      · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const s
    exact h1.smul h2
  have hbox_int : IntegrableOn (Gs φ s) box := by
    apply Measure.integrableOn_of_bounded (M := B * ((1 / c) ^ (s.re - 2) + c ^ (s.re - 2)))
    · rw [hbox, Measure.volume_eq_prod, Measure.prod_prod]
      simp only [Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · exact hmeas.aestronglyMeasurable
    · rw [ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      obtain ⟨hy1, hy2⟩ := hp.2
      have hy : 0 < p.2 := lt_of_lt_of_le (by positivity) hy1
      unfold Gs
      rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hy, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / p.2 ^ 2)]
      have h1 : 1 / p.2 ^ 2 * p.2 ^ s.re = p.2 ^ (s.re - 2) := by
        rw [Real.rpow_sub hy, Real.rpow_two]; field_simp
      have h2 := rpow_le_add_of_mem (σ := s.re - 2) (by positivity) hy1 hy2
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
      calc 1 / p.2 ^ 2 * (|φ ((p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2))| * p.2 ^ s.re)
          = |φ ((p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2))| * (1 / p.2 ^ 2 * p.2 ^ s.re) := by ring
        _ ≤ B * ((1 / c) ^ (s.re - 2) + c ^ (s.re - 2)) := by
            rw [h1]
            exact mul_le_mul (hB _) h2 (Real.rpow_nonneg hy.le _) hB0
  apply hbox_int.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioi)
  intro p hp
  obtain ⟨⟨-, hy⟩, hpb⟩ := hp
  simp only [Set.mem_Ioi] at hy
  unfold Gs
  by_cases hφ : φ ((p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2)) = 0
  · simp [hφ]
  · exfalso
    apply hpb
    have hle : (p.1 ^ 2 + (p.2 - 1) ^ 2) / (4 * p.2) ≤ A := by
      by_contra h
      exact hφ (hA _ (not_le.1 h))
    obtain ⟨h1, h2, h3⟩ := support_bounds hA0 hy hle
    exact ⟨abs_le.1 h1, h2, h3⟩

theorem sinh_half_sq (r : ℝ) : Real.sinh (r / 2) ^ 2 = (Real.exp r - 1) ^ 2 / (4 * Real.exp r) := by
  have h : Real.exp r = Real.exp (r / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.sinh_eq, Real.exp_neg, h]
  have : 0 < Real.exp (r / 2) := Real.exp_pos _
  field_simp
  ring

theorem ofReal_exp_cpow (r : ℝ) (s : ℂ) : ((Real.exp r : ℝ) : ℂ) ^ s = Complex.exp (r * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos r).ne'), Complex.ofReal_exp,
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]

/-- **The radial formula** for the Selberg transform:
`∫_ℍ φ(u(z, i)) y^s dμ(z) = ∫_ℝ 2 e^{r(s - 1/2)} Q_φ(sinh²(r/2)) dr`. -/
theorem integral_radial {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (s : ℂ) :
    ∫ z : ℍ, (φ (pointPair z I) : ℂ) * (z.im : ℂ) ^ s =
      ∫ r : ℝ, 2 * Complex.exp (r * (s - 1 / 2)) * (Qφ φ (Real.sinh (r / 2) ^ 2) : ℂ) := by
  have hcongr : Set.EqOn (fun p : ℝ × ℝ => (1 / p.2 ^ 2 : ℝ) •
      ((φ (pointPair (ofComplex ⟨p.1, p.2⟩) I) : ℂ) * ((ofComplex ⟨p.1, p.2⟩ : ℍ).im : ℂ) ^ s))
      (Gs φ s) ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro p hp
    have hy : 0 < p.2 := hp.2
    simp only [Gs]
    rw [pointPair_ofComplex_I hy, im_ofComplex hy]
  rw [integral_eq_iterated _ ((integrableOn_Gs hφm hA0 hB hA s).congr_fun hcongr.symm
    (MeasurableSet.univ.prod measurableSet_Ioi))]
  have hinner : ∀ y ∈ Set.Ioi (0 : ℝ), ∫ x : ℝ, (1 / y ^ 2 : ℝ) •
      ((φ (pointPair (ofComplex ⟨x, y⟩) I) : ℂ) * ((ofComplex ⟨x, y⟩ : ℍ).im : ℂ) ^ s) =
      ((2 * Real.sqrt y * Qφ φ ((y - 1) ^ 2 / (4 * y)) / y ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ s := by
    intro y hy
    have hy' : 0 < y := hy
    have e : ∀ x : ℝ, (1 / y ^ 2 : ℝ) •
        ((φ (pointPair (ofComplex ⟨x, y⟩) I) : ℂ) * ((ofComplex ⟨x, y⟩ : ℍ).im : ℂ) ^ s) =
        (((1 / y ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ s) * (φ ((x ^ 2 + (y - 1) ^ 2) / (4 * y)) : ℂ) := by
      intro x
      rw [pointPair_ofComplex_I hy', im_ofComplex hy', Complex.real_smul]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_complex_ofReal, integral_x φ hy']
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have himg : Real.exp '' Set.univ = Set.Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun r _ => (Real.hasDerivAt_exp r).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  congr 1
  ext r
  rw [abs_of_pos (Real.exp_pos r), ← Real.exp_half, ← sinh_half_sq, ofReal_exp_cpow,
    Complex.real_smul]
  push_cast
  have hexp : Complex.exp r * (2 * Complex.exp (r / 2) * (Qφ φ (Real.sinh (r / 2) ^ 2) : ℂ) /
      Complex.exp r ^ 2 * Complex.exp (r * s)) =
      2 * (Complex.exp r * Complex.exp (r / 2) * Complex.exp (r * s) / Complex.exp r ^ 2) *
        (Qφ φ (Real.sinh (r / 2) ^ 2) : ℂ) := by ring
  rw [hexp]
  congr 2
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- `Q_φ` is measurable. -/
theorem measurable_Qφ {φ : ℝ → ℝ} (hφm : Measurable φ) : Measurable (Qφ φ) := by
  have h : StronglyMeasurable (Function.uncurry fun (a w : ℝ) => φ (w ^ 2 + a)) :=
    (hφm.comp (by fun_prop)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

/-- `Q_φ(a) = 0` for `a > A`, and `|Q_φ(a)| ≤ 2B√A` for `a ≥ 0`. -/
theorem Qφ_eq_zero {φ : ℝ → ℝ} {A : ℝ} (hA : ∀ a, A < a → φ a = 0) {a : ℝ} (ha : A < a) :
    Qφ φ a = 0 := by
  unfold Qφ
  have : ∀ w : ℝ, φ (w ^ 2 + a) = 0 := fun w => hA _ (by nlinarith [sq_nonneg w])
  simp [this]

theorem abs_Qφ_le {φ : ℝ → ℝ} {A B : ℝ} (hB : ∀ a, |φ a| ≤ B)
    (hA : ∀ a, A < a → φ a = 0) (a : ℝ) (ha : 0 ≤ a) : |Qφ φ a| ≤ B * (2 * (Real.sqrt A + 1)) := by
  unfold Qφ
  have hsupp : ∀ w : ℝ, w ∉ Set.Icc (-(Real.sqrt A + 1)) (Real.sqrt A + 1) → φ (w ^ 2 + a) = 0 := by
    intro w hw
    apply hA
    simp only [Set.mem_Icc, not_and_or, not_le] at hw
    have hsA : A < w ^ 2 := by
      have h1 : Real.sqrt A + 1 < |w| := by
        rcases hw with h | h
        · rw [abs_of_neg (by linarith [Real.sqrt_nonneg A])]; linarith
        · rw [abs_of_pos (by linarith [Real.sqrt_nonneg A])]; exact h
      have h2 : Real.sqrt A < |w| := by linarith
      have h3 := Real.lt_sq_of_sqrt_lt h2
      rwa [sq_abs] at h3
    linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-(Real.sqrt A + 1)) (Real.sqrt A + 1))
    (fun w hw => hsupp w hw)]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Set.Icc (-(Real.sqrt A + 1)) (Real.sqrt A + 1)) (f := fun w => φ (w ^ 2 + a)) (C := B)
    (by simp) (fun w _ => by rw [Real.norm_eq_abs]; exact hB _)
  rw [Real.volume_real_Icc_of_le (by linarith [Real.sqrt_nonneg A]), Real.norm_eq_abs] at h
  linarith

/-- A bounded measurable function vanishing outside `[-R, R]` times a continuous function is
integrable. -/
theorem integrable_cont_mul {g : ℝ → ℝ} (hg : Measurable g) {M R : ℝ} (hM : ∀ r, |g r| ≤ M)
    (hR : ∀ r, R < |r| → g r = 0) {h : ℝ → ℂ} (hh : Continuous h) :
    Integrable (fun r => h r * (g r : ℂ)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hh.continuousOn
  have hmeas : AEStronglyMeasurable (fun r => h r * (g r : ℂ)) volume :=
    (hh.aestronglyMeasurable).mul (Complex.measurable_ofReal.comp hg).aestronglyMeasurable
  have hon : IntegrableOn (fun r => h r * (g r : ℂ)) (Set.Icc (-R) R) := by
    apply Measure.integrableOn_of_bounded (M := C * M)
    · simp [Real.volume_Icc]
    · exact hmeas
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hC r hr
      have h2 := hM r
      have hC0 : 0 ≤ C := (norm_nonneg _).trans h1
      exact mul_le_mul h1 h2 (abs_nonneg _) hC0
  apply hon.integrable_of_forall_notMem_eq_zero
  intro r hr
  have hRr : R < |r| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hr
    rcases hr with h | h
    · linarith [neg_abs_le r]
    · linarith [le_abs_self r]
  rw [hR r hRr, Complex.ofReal_zero, mul_zero]

/-- `g_φ(r) = Q_φ(sinh²(r/2))`. -/
noncomputable def gφ (φ : ℝ → ℝ) (r : ℝ) : ℝ := Qφ φ (Real.sinh (r / 2) ^ 2)

theorem gφ_neg (φ : ℝ → ℝ) (r : ℝ) : gφ φ (-r) = gφ φ r := by
  simp [gφ, neg_div, Real.sinh_neg]

theorem measurable_gφ {φ : ℝ → ℝ} (hφm : Measurable φ) : Measurable (gφ φ) :=
  (measurable_Qφ hφm).comp (by fun_prop)

theorem abs_gφ_le {φ : ℝ → ℝ} {A B : ℝ} (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0)
    (r : ℝ) : |gφ φ r| ≤ B * (2 * (Real.sqrt A + 1)) :=
  abs_Qφ_le hB hA _ (sq_nonneg _)

theorem gφ_eq_zero {φ : ℝ → ℝ} {A : ℝ} (hA : ∀ a, A < a → φ a = 0) {r : ℝ}
    (hr : 2 * Real.sqrt A < |r|) : gφ φ r = 0 := by
  apply Qφ_eq_zero hA
  have h1 : |r| / 2 ≤ Real.sinh (|r| / 2) := Real.self_le_sinh_iff.2 (by positivity)
  have h2 : |Real.sinh (r / 2)| = Real.sinh (|r| / 2) := by
    rw [Real.abs_sinh, abs_div, abs_two]
  have h3 : Real.sqrt A < |Real.sinh (r / 2)| := by rw [h2]; linarith
  have h4 := Real.lt_sq_of_sqrt_lt h3
  rwa [sq_abs] at h4

theorem integrable_gφ_mul {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (_hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) {h : ℝ → ℂ} (hh : Continuous h) :
    Integrable (fun r => h r * (gφ φ r : ℂ)) :=
  integrable_cont_mul (measurable_gφ hφm) (abs_gφ_le hB hA) (fun _ hr => gφ_eq_zero hA hr) hh

/-- **The radial formula, symmetrised**: `∫_ℍ φ(u(z, i)) y^s dμ = ∫ 2 cosh(r(s - 1/2)) g_φ(r) dr`.
In particular the Selberg transform `h(t)` (`s = 1/2 + it`) is `∫ 2 cos(rt) g_φ(r) dr`. -/
theorem integral_radial_cosh {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (s : ℂ) :
    ∫ z : ℍ, (φ (pointPair z I) : ℂ) * (z.im : ℂ) ^ s =
      ∫ r : ℝ, 2 * Complex.cosh (r * (s - 1 / 2)) * (gφ φ r : ℂ) := by
  rw [integral_radial hφm hA0 hB hA s]
  set w := s - 1 / 2
  have hF : Integrable (fun r : ℝ => 2 * Complex.exp (r * w) * (gφ φ r : ℂ)) :=
    integrable_gφ_mul hφm hA0 hB hA (by fun_prop)
  have hFn : Integrable (fun r : ℝ => 2 * Complex.exp (-(r * w)) * (gφ φ r : ℂ)) :=
    integrable_gφ_mul hφm hA0 hB hA (by fun_prop)
  have hneg : ∫ r : ℝ, 2 * Complex.exp (r * w) * (gφ φ r : ℂ) =
      ∫ r : ℝ, 2 * Complex.exp (-(r * w)) * (gφ φ r : ℂ) := by
    rw [← integral_neg_eq_self (fun r : ℝ => 2 * Complex.exp (r * w) * (gφ φ r : ℂ))]
    congr 1
    ext r
    rw [gφ_neg]
    push_cast
    ring_nf
  have hsum : ∫ r : ℝ, 2 * Complex.cosh (r * w) * (gφ φ r : ℂ) =
      (1 / 2 : ℂ) * ((∫ r : ℝ, 2 * Complex.exp (r * w) * (gφ φ r : ℂ)) +
        ∫ r : ℝ, 2 * Complex.exp (-(r * w)) * (gφ φ r : ℂ)) := by
    rw [← integral_add hF hFn, ← integral_const_mul]
    congr 1
    ext r
    rw [Complex.cosh]
    ring
  simp only [Qφ] at hsum hneg ⊢
  change ∫ r : ℝ, 2 * Complex.exp (r * w) * (gφ φ r : ℂ) = _
  rw [hsum, ← hneg]
  ring

/-- `∫_ℍ φ(u(z, i)) dμ(z) = ∫ 2 cosh(r/2) g_φ(r) dr`. -/
theorem integral_radial_zero {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) :
    ∫ z : ℍ, φ (pointPair z I) = ∫ r : ℝ, 2 * Real.cosh (r / 2) * gφ φ r := by
  have h := integral_radial_cosh hφm hA0 hB hA 0
  simp only [Complex.cpow_zero, mul_one, zero_sub] at h
  rw [integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  rw [h, ← integral_complex_ofReal]
  congr 1
  ext r
  push_cast
  rw [show (r : ℂ) * -(1 / 2) = -((r : ℂ) / 2) by ring, Complex.cosh_neg]

/-- **Change of variables `v = sinh(r/2)`**: `∫ 2 cosh(r/2) g_φ(r) dr = 4 ∫ Q_φ(v²) dv`. -/
theorem integral_cosh_gφ (φ : ℝ → ℝ) :
    ∫ r : ℝ, 2 * Real.cosh (r / 2) * gφ φ r = 4 * ∫ v : ℝ, Qφ φ (v ^ 2) := by
  have hderiv : ∀ r ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun r : ℝ => Real.sinh (r / 2)) (Real.cosh (r / 2) / 2) Set.univ r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => r / 2) (1 / 2) r := by
      simpa using (hasDerivAt_id r).div_const 2
    have h2 : HasDerivAt (fun r : ℝ => Real.sinh (r / 2)) (Real.cosh (r / 2) * (1 / 2)) r :=
      h1.sinh
    have h3 : Real.cosh (r / 2) * (1 / 2) = Real.cosh (r / 2) / 2 := by ring
    rw [h3] at h2
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun r : ℝ => Real.sinh (r / 2)) Set.univ := by
    intro a _ b _ hab
    have := Real.sinh_injective hab
    linarith
  have himg : (fun r : ℝ => Real.sinh (r / 2)) '' Set.univ = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ]
    intro v
    obtain ⟨r, hr⟩ := Real.sinh_surjective v
    exact ⟨2 * r, by simp [hr]⟩
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun v => Qφ φ (v ^ 2))
  rw [himg, Measure.restrict_univ] at h
  rw [h, ← integral_const_mul]
  congr 1
  ext r
  rw [abs_of_pos (by positivity), smul_eq_mul, gφ]
  ring

/-- `∫ 2√(U - v²) dv = πU` (`√` of a negative number is `0`). -/
theorem integral_two_sqrt {U : ℝ} (hU : 0 < U) :
    ∫ v : ℝ, 2 * Real.sqrt (U - v ^ 2) = Real.pi * U := by
  have hsU := Real.sqrt_pos.2 hU
  have hzero : ∀ v ∉ Set.Ioc (-Real.sqrt U) (Real.sqrt U), 2 * Real.sqrt (U - v ^ 2) = 0 := by
    intro v hv
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    rw [Real.sqrt_eq_zero'.2, mul_zero]
    have : Real.sqrt U ≤ |v| := by
      rcases hv with h | h
      · linarith [neg_abs_le v]
      · linarith [le_abs_self v]
    have := pow_le_pow_left₀ hsU.le this 2
    rw [Real.sq_sqrt hU.le, sq_abs] at this
    linarith
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun v : ℝ => 2 * Real.sqrt (U - v ^ 2)) hsU.ne'
  have e : ∀ t : ℝ, 2 * Real.sqrt (U - (Real.sqrt U * t) ^ 2) =
      2 * Real.sqrt U * Real.sqrt (1 - t ^ 2) := by
    intro t
    rw [mul_pow, Real.sq_sqrt hU.le, show U - U * t ^ 2 = U * (1 - t ^ 2) by ring,
      Real.sqrt_mul hU.le]
    ring
  simp only [e] at h
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq] at h
  rw [show Real.sqrt U * -1 = -Real.sqrt U by ring, mul_one] at h
  rw [smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hsU.ne'] at h
  rw [← h]
  linear_combination Real.pi * Real.mul_self_sqrt hU.le


/-- A bounded measurable function vanishing outside `[-R, R]` is integrable. -/
theorem integrable_of_bdd_supp {g : ℝ → ℝ} (hg : Measurable g) {M R : ℝ} (hM : ∀ r, |g r| ≤ M)
    (hR : ∀ r, R < |r| → g r = 0) : Integrable g := by
  have hon : IntegrableOn g (Set.Icc (-R) R) := by
    apply Measure.integrableOn_of_bounded (M := M)
    · simp [Real.volume_Icc]
    · exact hg.aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun r _ => by rw [Real.norm_eq_abs]; exact hM r)
  apply hon.integrable_of_forall_notMem_eq_zero
  intro r hr
  apply hR
  simp only [Set.mem_Icc, not_and_or, not_le] at hr
  rcases hr with h | h
  · linarith [neg_abs_le r]
  · linarith [le_abs_self r]

/-- The real version of `integrable_gφ_mul`. -/
theorem integrable_gφ_mul_real {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun r => h r * gφ φ r) := by
  have := (integrable_gφ_mul hφm hA0 hB hA (h := fun r => (h r : ℂ))
    (Complex.continuous_ofReal.comp hh)).re
  simpa using this

/-- `w ↦ φ(w² + a)` is integrable for continuous `φ` vanishing on `(A, ∞)`. -/
theorem integrable_comp_sq_add {φ : ℝ → ℝ} (hφc : Continuous φ) {A : ℝ}
    (hA : ∀ a, A < a → φ a = 0) (a : ℝ) : Integrable (fun w : ℝ => φ (w ^ 2 + a)) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro (isCompact_Icc (a := -(|A| + |a| + 1)) (b := |A| + |a| + 1))
  intro w hw
  apply hA
  simp only [Set.mem_Icc, not_and_or, not_le] at hw
  have h1 : |A| + |a| + 1 < |w| := by
    rcases hw with h | h
    · linarith [neg_abs_le w]
    · linarith [le_abs_self w]
  have h2 : (|A| + |a| + 1) ^ 2 < w ^ 2 := by
    rw [← sq_abs w]; exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
  nlinarith [le_abs_self A, neg_abs_le a, abs_nonneg A, abs_nonneg a,
    mul_nonneg (add_nonneg (abs_nonneg A) (abs_nonneg a))
      (add_nonneg (add_nonneg (abs_nonneg A) (abs_nonneg a)) zero_le_one)]

theorem Qφ_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ a, 0 ≤ φ a) (a : ℝ) : 0 ≤ Qφ φ a :=
  integral_nonneg fun _ => hφ0 _

theorem gφ_nonneg {φ : ℝ → ℝ} (hφ0 : ∀ a, 0 ≤ φ a) (r : ℝ) : 0 ≤ gφ φ r :=
  Qφ_nonneg hφ0 _

/-- `Q_φ(v²) ≥ 2√(U - v²)` if `φ ≥ 0` and `φ = 1` on `[0, U]`. -/
theorem le_Qφ {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ a, 0 ≤ φ a) {A : ℝ}
    (hA : ∀ a, A < a → φ a = 0) {U : ℝ} (h1 : ∀ a, 0 ≤ a → a ≤ U → φ a = 1) (v : ℝ) :
    2 * Real.sqrt (U - v ^ 2) ≤ Qφ φ (v ^ 2) := by
  rcases lt_or_ge (U - v ^ 2) 0 with hneg | hpos
  · rw [Real.sqrt_eq_zero'.2 hneg.le, mul_zero]
    exact Qφ_nonneg hφ0 _
  · set c := Real.sqrt (U - v ^ 2) with hc
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hint := integrable_comp_sq_add hφc hA (v ^ 2)
    calc 2 * c = ∫ w in Set.Icc (-c) c, (1 : ℝ) := by
          rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
          ring
      _ ≤ ∫ w in Set.Icc (-c) c, φ (w ^ 2 + v ^ 2) := by
          apply setIntegral_mono_on continuous_const.integrableOn_Icc hint.integrableOn
            measurableSet_Icc
          intro w hw
          rw [h1 _ (by positivity)]
          have : w ^ 2 ≤ c ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 hw) 2
          rw [hc, Real.sq_sqrt hpos] at this
          linarith
      _ ≤ ∫ w, φ (w ^ 2 + v ^ 2) :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => hφ0 _)

/-- `Q_φ(v²) ≤ 2√(U - v²)` if `0 ≤ φ ≤ 1` and `φ = 0` on `(U, ∞)`. -/
theorem Qφ_le {φ : ℝ → ℝ} (hφ0 : ∀ a, 0 ≤ φ a) (hφ1 : ∀ a, φ a ≤ 1) {U : ℝ}
    (hU : ∀ a, U < a → φ a = 0) (v : ℝ) :
    Qφ φ (v ^ 2) ≤ 2 * Real.sqrt (U - v ^ 2) := by
  set c := Real.sqrt (U - v ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hzero : ∀ w ∉ Set.Icc (-c) c, φ (w ^ 2 + v ^ 2) = 0 := by
    intro w hw
    apply hU
    have h1 : c < |w| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hw
      rcases hw with h | h
      · linarith [neg_abs_le w]
      · linarith [le_abs_self w]
    rcases lt_or_ge (U - v ^ 2) 0 with hneg | hpos
    · nlinarith [sq_nonneg w]
    · have h2 : c ^ 2 < w ^ 2 := by
        rw [← sq_abs w]; exact pow_lt_pow_left₀ h1 hc0 two_ne_zero
      rw [hc, Real.sq_sqrt hpos] at h2
      linarith
  unfold Qφ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-c) c)
    (f := fun w => φ (w ^ 2 + v ^ 2)) (C := 1) (by simp) (fun w _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]; exact hφ1 _)
  rw [Real.volume_real_Icc_of_le (by linarith), Real.norm_eq_abs] at h
  linarith [le_abs_self (∫ w in Set.Icc (-c) c, φ (w ^ 2 + v ^ 2))]

/-- `v ↦ 2√(U - v²)` is integrable. -/
theorem integrable_two_sqrt (U : ℝ) : Integrable (fun v : ℝ => 2 * Real.sqrt (U - v ^ 2)) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro (isCompact_Icc (a := -(|U| + 1)) (b := |U| + 1))
  intro v hv
  simp only [Set.mem_Icc, not_and_or, not_le] at hv
  have h1 : |U| + 1 < |v| := by
    rcases hv with h | h
    · linarith [neg_abs_le v]
    · linarith [le_abs_self v]
  have h2 : (|U| + 1) ^ 2 < v ^ 2 := by
    rw [← sq_abs v]; exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
  have h3 : U < v ^ 2 := by nlinarith [le_abs_self U, abs_nonneg U]
  rw [Real.sqrt_eq_zero'.2 (by linarith), mul_zero]

/-- `v ↦ Q_φ(v²)` is integrable. -/
theorem integrable_Qφ_sq {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ}
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) :
    Integrable (fun v : ℝ => Qφ φ (v ^ 2)) := by
  apply integrable_of_bdd_supp ((measurable_Qφ hφm).comp (by fun_prop))
    (fun v => abs_Qφ_le hB hA _ (sq_nonneg v)) (R := Real.sqrt A)
  intro v hv
  apply Qφ_eq_zero hA
  have := Real.lt_sq_of_sqrt_lt hv
  rwa [sq_abs] at this

/-- `∫_ℍ φ(u(z, i)) dμ(z) = 4 ∫ Q_φ(v²) dv`. -/
theorem integral_area {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) :
    ∫ z : ℍ, φ (pointPair z I) = 4 * ∫ v : ℝ, Qφ φ (v ^ 2) := by
  rw [integral_radial_zero hφm hA0 hB hA, integral_cosh_gφ]

/-- **The area of a disc, from below**: if `0 ≤ φ` and `φ = 1` on `[0, U]`, then
`∫_ℍ φ(u(z, i)) dμ(z) ≥ 4πU`. -/
theorem le_integral_area {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ a, 0 ≤ φ a) {A B : ℝ}
    (hA0 : 0 ≤ A) (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) {U : ℝ} (hU : 0 < U)
    (h1 : ∀ a, 0 ≤ a → a ≤ U → φ a = 1) :
    4 * Real.pi * U ≤ ∫ z : ℍ, φ (pointPair z I) := by
  rw [integral_area hφc.measurable hA0 hB hA]
  have := integral_mono (integrable_two_sqrt U) (integrable_Qφ_sq hφc.measurable hB hA)
    (fun v => le_Qφ hφc hφ0 hA h1 v)
  rw [integral_two_sqrt hU] at this
  linarith

/-- **The area of a disc, from above**: if `0 ≤ φ ≤ 1` and `φ = 0` on `(U, ∞)`, then
`∫_ℍ φ(u(z, i)) dμ(z) ≤ 4πU`. -/
theorem integral_area_le {φ : ℝ → ℝ} (hφc : Continuous φ) (hφ0 : ∀ a, 0 ≤ φ a)
    (hφ1 : ∀ a, φ a ≤ 1) {U : ℝ} (hU : 0 < U) (hUz : ∀ a, U < a → φ a = 0) :
    ∫ z : ℍ, φ (pointPair z I) ≤ 4 * Real.pi * U := by
  have hB : ∀ a, |φ a| ≤ 1 := fun a => by rw [abs_of_nonneg (hφ0 a)]; exact hφ1 a
  rw [integral_area hφc.measurable hU.le hB hUz]
  have := integral_mono (integrable_Qφ_sq hφc.measurable hB hUz) (integrable_two_sqrt U)
    (fun v => Qφ_le hφ0 hφ1 hUz v)
  rw [integral_two_sqrt hU] at this
  linarith

/-! ### Invariance -/

/-- `u(g z, g w) = u(z, w)` for `g ∈ SL₂(ℝ)`. -/
theorem pointPair_smul_SL2R (g : SL(2, ℝ)) (z w : ℍ) : pointPair (g • z) (g • w) = pointPair z w := by
  rw [SymMat.pointPair_eq_cosh, SymMat.pointPair_eq_cosh, dist_smul]

/-- `∫_ℍ F(u(z, v)) dμ(v) = ∫_ℍ F(u(v, i)) dμ(v)`. -/
theorem integral_pointPair_left (F : ℝ → ℝ) (z : ℍ) :
    ∫ v : ℍ, F (pointPair z v) = ∫ v : ℍ, F (pointPair v I) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) UpperHalfPlane.I z
  have e : ∀ v : ℍ, pointPair z v = pointPair (g⁻¹ • v) I := by
    intro v
    rw [← hg, SymMat.pointPair_comm, ← pointPair_smul_SL2R g⁻¹, inv_smul_smul]
  simp_rw [e]
  exact integral_smul_eq_self (G := GL (Fin 2) ℝ) (μ := volume) (fun v => F (pointPair v I))
    (g := Matrix.SpecialLinearGroup.mapGL ℝ g⁻¹)

/-- `v ↦ u(z, v)` is continuous. -/
theorem continuous_pointPair_left (z : ℍ) : Continuous (fun v : ℍ => pointPair z v) := by
  simp_rw [SymMat.pointPair_eq_cosh]
  fun_prop

/-- `u(z, w) ≤ R` implies `d(z, w) ≤ 4R + 1`. -/
theorem dist_le_of_pointPair_le {z w : ℍ} {R : ℝ} (h : pointPair z w ≤ R) :
    dist z w ≤ 4 * R + 1 := by
  rw [SymMat.pointPair_eq_cosh] at h
  have h1 : Real.exp (dist z w) ≤ 2 * Real.cosh (dist z w) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-dist z w)]
  have h2 := Real.add_one_le_exp (dist z w)
  linarith

/-- `v ↦ F(u(z, v))` is integrable for continuous `F` vanishing on `(A, ∞)`. -/
theorem integrable_pointPair_left {F : ℝ → ℝ} (hF : Continuous F) {A : ℝ}
    (hA : ∀ a, A < a → F a = 0) (z : ℍ) : Integrable (fun v : ℍ => F (pointPair z v)) := by
  apply Continuous.integrable_of_hasCompactSupport (hF.comp (continuous_pointPair_left z))
  apply HasCompactSupport.intro (isCompact_closedBall z (4 * A + 1))
  intro v hv
  apply hA
  by_contra hle
  exact hv (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pointPair_le (not_lt.1 hle)))


/-! ### Finiteness -/

/-- Only finitely many `γ ∈ Γ₀(q)` satisfy `u(z, γ w) ≤ R`: the image of `SL₂(ℤ)` in `SL₂(ℝ)`
is discrete, so it acts properly discontinuously on `ℍ`. -/
theorem finite_pointPair_le (q : ℕ) (z w : ℍ) (R : ℝ) :
    {γ : CongruenceSubgroup.Gamma0 q | pointPair z ((γ : SL(2, ℤ)) • w) ≤ R}.Finite := by
  set 𝒢 : Subgroup SL(2, ℝ) := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).range
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := 𝒢) (T := ℍ)
    (isCompact_singleton (x := w)) (isCompact_closedBall z (4 * R + 1))
  set f : CongruenceSubgroup.Gamma0 q → 𝒢 := fun γ =>
    ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ : SL(2, ℤ)),
      MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun x : 𝒢 => ((x : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) hab
    simp only [hf] at h
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun h i) j
    simpa using this
  apply (hfin.preimage hinj.injOn).subset
  intro γ hγ
  rw [Set.mem_preimage]
  refine ⟨(f γ) • w, ⟨w, rfl, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  have : (f γ) • w = (γ : SL(2, ℤ)) • w := by
    rw [SymMat.smul_eq_map]; rfl
  rw [this]
  exact dist_le_of_pointPair_le hγ

end Hyperbolic

end Triples
