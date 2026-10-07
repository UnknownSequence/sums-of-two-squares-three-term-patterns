import TriplesFinal.Spectral.Expansion
import TriplesFinal.Spectral.Hyperbolic

/-!
# Lemma 10.7: the Heegner side

For `T ≥ 1` and points `z_1, …, z_I ∈ ℍ`, with `U_j = ∑_i u_j(z_i)`,
`U_𝔰(r) = ∑_i E_𝔰(z_i, 1/2 + ir)` and `𝒫 = ∑_{i,i'} #{γ ∈ Γ₀(q) : u(z_i, γ z_{i'}) ≤ 1}`:
`∑_{t_j ∈ [0, T]} |U_j|² + ∑_{exc} |U_j|² + (1/4π) ∑_𝔰 ∫_{-T}^{T} |U_𝔰(r)|² dr ≤ (256/π) T² 𝒫`.

The proof applies the pre-trace formula to `k = k₀ * k₀`, where `k₀(z, w) = φ₁(u(z, w))`,
`φ₁ = 1` on `[0, β₀/2]`, `φ₁ = 0` on `[β₀, ∞)`, `0 ≤ φ₁ ≤ 1` (`bump`), `β₀ = 1/(64T²)`, using the
convolution property of Selberg transforms, `h_k = h_{k₀}²`:

* by the radial formula, `h_{k₀}(t) = ∫ 2 cos(rt) g(r) dr` with `g ≥ 0`, so `h_{k₀}` is real on
  `ℝ ∪ iℝ` (`selbergTransform_im_eq_zero`); since `g(r) = 0` unless `sinh²(r/2) ≤ β₀`, and
  `∫_ℍ k₀(z, i) dμ(z) ≥ 2πβ₀` (the area of the disc `u ≤ β₀/2`), `h_{k₀}(t) ≥ πβ₀` for
  `t ∈ [-T, T]` (`lower_real`) and for `t = iθ` (`lower_imag`);
* `0 ≤ k ≤ 4πβ₀` (`pairConv_le`: the disc `u ≤ β₀` has area `4πβ₀`), and `k(z, w) = 0` unless
  `u(z, w) ≤ 4β₀(1 + β₀) ≤ 1` (`pointPair_le_of_pairConv_ne_zero`, by the triangle inequality
  for the hyperbolic distance);
* the sums over `γ` are finite (`Hyperbolic.finite_pointPair_le`).

The pre-trace formula (`SpectralData.PreTrace`) is stated with half the sum over the matrices
`γ ∈ Γ₀(q)`, which gives the constant `128/π`; the paper's `256/π` is what is stated.

Paper: §10.5, Lemma 10.7.
-/

namespace Triples

open scoped MatrixGroups ContDiff
open CongruenceSubgroup UpperHalfPlane MeasureTheory Hyperbolic

namespace HeegnerSide

/-! ### The profile `φ₁` -/

/-- The profile `φ_β(a) = s((4/3)(1 - (a/β)²))` (`s` the smooth transition): smooth, with values
in `[0, 1]`, `= 1` for `|a| ≤ β/2` and `= 0` for `|a| ≥ β`. -/
noncomputable def bump (β : ℝ) (a : ℝ) : ℝ := Real.smoothTransition (4 / 3 * (1 - (a / β) ^ 2))

variable {β : ℝ}

theorem bump_nonneg (a : ℝ) : 0 ≤ bump β a := Real.smoothTransition.nonneg _

theorem bump_le_one (a : ℝ) : bump β a ≤ 1 := Real.smoothTransition.le_one _

theorem abs_bump_le (a : ℝ) : |bump β a| ≤ 1 := by
  rw [abs_of_nonneg (bump_nonneg a)]; exact bump_le_one a

theorem contDiff_bump : ContDiff ℝ ∞ (bump β) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub ((contDiff_id.div_const _).pow 2)))

theorem continuous_bump : Continuous (bump β) := contDiff_bump.continuous

theorem bump_eq_one (hβ : 0 < β) {a : ℝ} (ha : |a| ≤ β / 2) : bump β a = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h1 : a ^ 2 ≤ (β / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have h2 : (a / β) ^ 2 ≤ 1 / 4 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem bump_eq_zero (hβ : 0 < β) {a : ℝ} (ha : β ≤ |a|) : bump β a = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : β ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ hβ.le ha 2
  have h2 : 1 ≤ (a / β) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity), one_mul]
    exact h1
  linarith

theorem bump_eq_zero' (hβ : 0 < β) {a : ℝ} (ha : β < a) : bump β a = 0 :=
  bump_eq_zero hβ (by rw [abs_of_pos (by linarith)]; exact ha.le)

theorem hasCompactSupport_bump (hβ : 0 < β) : HasCompactSupport (bump β) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -β) (b := β))
  intro a ha
  apply bump_eq_zero hβ
  simp only [Set.mem_Icc, not_and_or, not_le] at ha
  rcases ha with h | h
  · linarith [neg_abs_le a]
  · linarith [le_abs_self a]

theorem lt_of_bump_ne_zero (hβ : 0 < β) {a : ℝ} (ha : 0 ≤ a) (h : bump β a ≠ 0) : a < β := by
  by_contra hle
  exact h (bump_eq_zero hβ (by rw [abs_of_nonneg ha]; exact not_lt.1 hle))

/-! ### The Selberg transform of `φ₁` -/

/-- The Selberg transform in radial form: `h(t) = ∫ 2 cosh(irt) g_φ(r) dr`. -/
theorem selbergTransform_eq {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (t : ℂ) :
    selbergTransform φ t = ∫ r : ℝ, 2 * Complex.cosh (r * (Complex.I * t)) * (gφ φ r : ℂ) := by
  unfold selbergTransform
  rw [integral_radial_cosh hφm hA0 hB hA]
  congr 1
  ext r
  congr 3
  ring

/-- For real `τ`: `h(τ) = ∫ 2 cos(rτ) g_φ(r) dr`. -/
theorem selbergTransform_real {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (τ : ℝ) :
    selbergTransform φ τ = ((∫ r : ℝ, 2 * Real.cos (r * τ) * gφ φ r : ℝ) : ℂ) := by
  rw [selbergTransform_eq hφm hA0 hB hA, ← integral_complex_ofReal]
  congr 1
  ext r
  push_cast
  rw [show (r : ℂ) * (Complex.I * τ) = ((r : ℂ) * τ) * Complex.I by ring, Complex.cosh_mul_I]

/-- For `t = iθ`: `h(iθ) = ∫ 2 cosh(rθ) g_φ(r) dr`. -/
theorem selbergTransform_imag {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) (θ : ℝ) :
    selbergTransform φ (Complex.I * θ) =
      ((∫ r : ℝ, 2 * Real.cosh (r * θ) * gφ φ r : ℝ) : ℂ) := by
  rw [selbergTransform_eq hφm hA0 hB hA, ← integral_complex_ofReal]
  congr 1
  ext r
  push_cast
  rw [show (r : ℂ) * (Complex.I * (Complex.I * θ)) = -((r : ℂ) * θ) by
    rw [← mul_assoc Complex.I, Complex.I_mul_I]; ring, Complex.cosh_neg]

/-- `h(t)` is real for `t ∈ ℝ ∪ iℝ`. -/
theorem selbergTransform_im_eq_zero {φ : ℝ → ℝ} (hφm : Measurable φ) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB : ∀ a, |φ a| ≤ B) (hA : ∀ a, A < a → φ a = 0) {t : ℂ} (ht : t.im = 0 ∨ t.re = 0) :
    selbergTransform φ t = ((selbergTransform φ t).re : ℂ) := by
  apply Complex.ext (by simp)
  simp only [Complex.ofReal_im]
  rcases ht with ht | ht
  · have e : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [ht])
    rw [e, selbergTransform_real hφm hA0 hB hA]
    simp
  · have e : t = Complex.I * (t.im : ℂ) := Complex.ext (by simp [ht]) (by simp)
    rw [e, selbergTransform_imag hφm hA0 hB hA]
    simp

/-- `x² ≤ sinh² x`. -/
theorem sq_le_sinh_sq (x : ℝ) : x ^ 2 ≤ Real.sinh x ^ 2 := by
  have h : |x| ≤ |Real.sinh x| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.2 (abs_nonneg x)
  rw [← sq_abs x, ← sq_abs (Real.sinh x)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The bound `(1 + β) ∫ 2 g_{φ₁} ≥ ∫_ℍ φ₁(u(z, i)) dμ(z) ≥ 2πβ`. -/
theorem area_bound (hβ : 0 < β) :
    2 * Real.pi * β ≤ (1 + β) * ∫ r : ℝ, 2 * gφ (bump β) r := by
  have harea := le_integral_area (φ := bump β) continuous_bump bump_nonneg hβ.le abs_bump_le
    (fun a ha => bump_eq_zero' hβ ha) (U := β / 2) (by positivity)
    (fun a ha0 haU => bump_eq_one hβ (by rw [abs_of_nonneg ha0]; exact haU))
  rw [integral_radial_zero continuous_bump.measurable hβ.le abs_bump_le
    (fun a ha => bump_eq_zero' hβ ha)] at harea
  have hle : ∫ r : ℝ, 2 * Real.cosh (r / 2) * gφ (bump β) r ≤
      ∫ r : ℝ, (1 + β) * (2 * gφ (bump β) r) := by
    apply integral_mono
      (integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun r => 2 * Real.cosh (r / 2)) (by fun_prop))
      ((integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun _ => 2) continuous_const).const_mul (1 + β))
    intro r
    have hg := gφ_nonneg (bump_nonneg (β := β)) r
    by_cases hs : Real.sinh (r / 2) ^ 2 ≤ β
    · have hc1 := Real.one_le_cosh (r / 2)
      have hc2 : Real.cosh (r / 2) ^ 2 = Real.sinh (r / 2) ^ 2 + 1 := Real.cosh_sq _
      have hc : Real.cosh (r / 2) ≤ 1 + β := by nlinarith
      simp only
      nlinarith
    · have h0 : gφ (bump β) r = 0 := Qφ_eq_zero (fun a ha => bump_eq_zero' hβ ha) (not_le.1 hs)
      simp [h0]
  rw [integral_const_mul] at hle
  linarith

theorem integral_two_gφ_nonneg : 0 ≤ ∫ r : ℝ, 2 * gφ (bump β) r :=
  integral_nonneg fun r => mul_nonneg zero_le_two (gφ_nonneg bump_nonneg r)

/-- **Lower bound for real `τ`**: `h_{φ₁}(τ) ≥ πβ` if `β ≤ 1/64` and `4βτ² ≤ 1/16`. -/
theorem lower_real (hβ : 0 < β) (hβ1 : β ≤ 1 / 64) {τ : ℝ} (hτ : 4 * β * τ ^ 2 ≤ 1 / 16) :
    Real.pi * β ≤ (selbergTransform (bump β) τ).re := by
  rw [selbergTransform_real continuous_bump.measurable hβ.le abs_bump_le
    (fun a ha => bump_eq_zero' hβ ha), Complex.ofReal_re]
  have hle : ∫ r : ℝ, 31 / 32 * (2 * gφ (bump β) r) ≤
      ∫ r : ℝ, 2 * Real.cos (r * τ) * gφ (bump β) r := by
    apply integral_mono
      ((integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun _ => 2) continuous_const).const_mul _)
      (integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun r => 2 * Real.cos (r * τ)) (by fun_prop))
    intro r
    have hg := gφ_nonneg (bump_nonneg (β := β)) r
    by_cases hs : Real.sinh (r / 2) ^ 2 ≤ β
    · have h1 := sq_le_sinh_sq (r / 2)
      have h2 : (r * τ) ^ 2 ≤ 1 / 16 := by
        have : r ^ 2 ≤ 4 * β := by nlinarith
        calc (r * τ) ^ 2 = r ^ 2 * τ ^ 2 := by ring
          _ ≤ 4 * β * τ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg τ)
          _ ≤ 1 / 16 := hτ
      have h3 := Real.one_sub_sq_div_two_le_cos (x := r * τ)
      have h4 : 31 / 32 ≤ Real.cos (r * τ) := by linarith
      simp only
      nlinarith
    · have h0 : gφ (bump β) r = 0 := Qφ_eq_zero (fun a ha => bump_eq_zero' hβ ha) (not_le.1 hs)
      simp [h0]
  rw [integral_const_mul] at hle
  have ha := area_bound hβ
  have hG := integral_two_gφ_nonneg (β := β)
  have hpi := Real.pi_pos
  nlinarith

/-- **Lower bound for `t = iθ`**: `h_{φ₁}(iθ) ≥ πβ` if `β ≤ 1/64`. -/
theorem lower_imag (hβ : 0 < β) (hβ1 : β ≤ 1 / 64) (θ : ℝ) :
    Real.pi * β ≤ (selbergTransform (bump β) (Complex.I * θ)).re := by
  rw [selbergTransform_imag continuous_bump.measurable hβ.le abs_bump_le
    (fun a ha => bump_eq_zero' hβ ha), Complex.ofReal_re]
  have hle : ∫ r : ℝ, 2 * gφ (bump β) r ≤ ∫ r : ℝ, 2 * Real.cosh (r * θ) * gφ (bump β) r := by
    apply integral_mono
      (integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun _ => 2) continuous_const)
      (integrable_gφ_mul_real continuous_bump.measurable hβ.le abs_bump_le
        (fun a ha => bump_eq_zero' hβ ha) (h := fun r => 2 * Real.cosh (r * θ)) (by fun_prop))
    intro r
    have hg := gφ_nonneg (bump_nonneg (β := β)) r
    have hc := Real.one_le_cosh (r * θ)
    simp only
    nlinarith
  have ha := area_bound hβ
  have hG := integral_two_gφ_nonneg (β := β)
  have hpi := Real.pi_pos
  nlinarith

/-! ### The kernel `k = k₀ * k₀` -/

/-- If `u(z, v) ≤ β` and `u(v, w) ≤ β` then `u(z, w) ≤ 4β(1 + β)`: with `d = d(z, w)`,
`cosh d ≤ cosh(d₁ + d₂) ≤ c² + (c² - 1)` where `c = 1 + 2β ≥ cosh dᵢ`. -/
theorem pointPair_triangle {z v w : ℍ} {β : ℝ} (h1 : pointPair z v ≤ β)
    (h2 : pointPair v w ≤ β) : pointPair z w ≤ 4 * β * (1 + β) := by
  rw [SymMat.pointPair_eq_cosh] at h1 h2 ⊢
  have hd : dist z w ≤ dist z v + dist v w := dist_triangle z v w
  have hd1 : 0 ≤ dist z v := dist_nonneg
  have hd2 : 0 ≤ dist v w := dist_nonneg
  have hc : Real.cosh (dist z w) ≤ Real.cosh (dist z v + dist v w) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith)]
    exact hd
  rw [Real.cosh_add] at hc
  have e1 := Real.cosh_sq (dist z v)
  have e2 := Real.cosh_sq (dist v w)
  have s1 : 0 ≤ Real.sinh (dist z v) := Real.sinh_nonneg_iff.2 hd1
  have s2 : 0 ≤ Real.sinh (dist v w) := Real.sinh_nonneg_iff.2 hd2
  have c1 : 1 ≤ Real.cosh (dist z v) := Real.one_le_cosh _
  have c2 : 1 ≤ Real.cosh (dist v w) := Real.one_le_cosh _
  have b1 : Real.cosh (dist z v) ≤ 1 + 2 * β := by linarith
  have b2 : Real.cosh (dist v w) ≤ 1 + 2 * β := by linarith
  have p1 : Real.cosh (dist z v) * Real.cosh (dist v w) ≤ (1 + 2 * β) ^ 2 := by
    rw [sq]; exact mul_le_mul b1 b2 (by linarith) (by linarith)
  have q1 : Real.sinh (dist z v) ^ 2 ≤ (1 + 2 * β) ^ 2 - 1 := by nlinarith
  have q2 : Real.sinh (dist v w) ^ 2 ≤ (1 + 2 * β) ^ 2 - 1 := by nlinarith
  have p2 : Real.sinh (dist z v) * Real.sinh (dist v w) ≤ (1 + 2 * β) ^ 2 - 1 := by
    nlinarith [sq_nonneg (Real.sinh (dist z v) - Real.sinh (dist v w))]
  nlinarith

theorem pointPair_nonneg (z w : ℍ) : 0 ≤ pointPair z w := by
  rw [SymMat.pointPair_eq_cosh]
  linarith [Real.one_le_cosh (dist z w)]

theorem pairConv_nonneg (z w : ℍ) : 0 ≤ pairConv (bump β) (bump β) z w :=
  integral_nonneg fun _ => mul_nonneg (bump_nonneg _) (bump_nonneg _)

/-- `k(z, w) ≤ 4πβ`: `k(z, w) ≤ ∫ k₀(z, v) dμ(v)`, the area of a disc of radius `u = β`. -/
theorem pairConv_le (hβ : 0 < β) (z w : ℍ) :
    pairConv (bump β) (bump β) z w ≤ 4 * Real.pi * β := by
  unfold pairConv
  calc ∫ v : ℍ, bump β (pointPair z v) * bump β (pointPair v w)
      ≤ ∫ v : ℍ, bump β (pointPair z v) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun v => mul_nonneg (bump_nonneg _) (bump_nonneg _))
          (integrable_pointPair_left continuous_bump (fun a ha => bump_eq_zero' hβ ha) z)
        exact Filter.Eventually.of_forall fun v =>
          mul_le_of_le_one_right (bump_nonneg _) (bump_le_one _)
    _ = ∫ v : ℍ, bump β (pointPair v UpperHalfPlane.I) := integral_pointPair_left _ z
    _ ≤ 4 * Real.pi * β :=
        integral_area_le continuous_bump bump_nonneg bump_le_one hβ
          (fun a ha => bump_eq_zero' hβ ha)

/-- `k(z, w) ≠ 0` implies `u(z, w) ≤ 4β(1 + β)`. -/
theorem pointPair_le_of_pairConv_ne_zero (hβ : 0 < β) {z w : ℍ}
    (h : pairConv (bump β) (bump β) z w ≠ 0) : pointPair z w ≤ 4 * β * (1 + β) := by
  obtain ⟨v, hv⟩ : ∃ v, bump β (pointPair z v) * bump β (pointPair v w) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h
    unfold pairConv
    simp [hcon]
  have h1 := lt_of_bump_ne_zero hβ (pointPair_nonneg z v) (left_ne_zero_of_mul hv)
  have h2 := lt_of_bump_ne_zero hβ (pointPair_nonneg v w) (right_ne_zero_of_mul hv)
  exact pointPair_triangle h1.le h2.le


end HeegnerSide

/-- The pair count `∑_{i,i'} #{γ ∈ Γ₀(q) : u(z_i, γ z_{i'}) ≤ 1}` for points `z : Fin n → ℍ`. -/
noncomputable def pairCountPts (q : ℕ) {n : ℕ} (z : Fin n → ℍ) : ℕ :=
  ∑ i, ∑ i', {γ : Gamma0 q | pointPair (z i) ((γ : SL(2, ℤ)) • z i') ≤ 1}.ncard

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

open HeegnerSide in
/-- **Lemma 10.7.** -/
theorem heegner_side (hPT : D.PreTrace) (hSC : SelbergConvolution) {T : ℝ} (hT : 1 ≤ T)
    {n : ℕ} (z : Fin n → ℍ) :
    (∑ᶠ j ∈ {j | (D.t j).im = 0 ∧ (D.t j).re ≤ T}, ‖∑ i, D.u j (z i)‖ ^ 2) +
        (∑ᶠ j ∈ {j | D.IsExceptional j}, ‖∑ i, D.u j (z i)‖ ^ 2) +
        1 / (4 * Real.pi) * ∑ 𝔰, ∫ r in Set.Icc (-T) T, ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 ≤
      256 / Real.pi * T ^ 2 * pairCountPts q z := by
  classical
  -- parameters
  set β : ℝ := 1 / (64 * T ^ 2) with hβdef
  have hT0 : 0 < T := by linarith
  have hβ : 0 < β := by positivity
  have hβ1 : β ≤ 1 / 64 := by
    rw [hβdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hβT : 4 * β * T ^ 2 = 1 / 16 := by
    rw [hβdef]; field_simp; ring
  have hpi := Real.pi_pos
  -- the kernel `k = k₀ * k₀` with profile `φ`, and the pre-trace formula for it
  obtain ⟨φ, hφs, hφc, hφk, hφh⟩ := hSC (bump β) (bump β) contDiff_bump
    (hasCompactSupport_bump hβ) contDiff_bump (hasCompactSupport_bump hβ)
  obtain ⟨hsum, hint, heq⟩ := hPT φ hφs hφc n z
  -- `h_φ = h_{φ₁}²` is real and nonnegative on `ℝ ∪ iℝ`
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℝ, ∀ t, H t = (selbergTransform (bump β) t).re := ⟨_, fun _ => rfl⟩
  have hreal : ∀ t : ℂ, t.im = 0 ∨ t.re = 0 → selbergTransform φ t = ((H t ^ 2 : ℝ) : ℂ) := by
    intro t ht
    rw [hφh, selbergTransform_im_eq_zero continuous_bump.measurable hβ.le abs_bump_le
      (fun a ha => bump_eq_zero' hβ ha) ht, ← hH]
    push_cast
    ring
  have hspec : ∀ j, (D.t j).im = 0 ∨ (D.t j).re = 0 := by
    intro j
    rcases D.t_mem j with ⟨h, _⟩ | ⟨h, _, _⟩
    · exact Or.inl h
    · exact Or.inr h
  -- the terms of the pre-trace formula, as real numbers
  set a : D.ι → ℝ := fun j => H (D.t j) ^ 2 * ‖∑ i, D.u j (z i)‖ ^ 2 with ha
  set b : D.κ → ℝ → ℝ := fun 𝔰 r => H r ^ 2 * ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 with hb
  have hterm_j : ∀ j, selbergTransform φ (D.t j) * ((‖∑ i, D.u j (z i)‖ ^ 2 : ℝ) : ℂ) =
      ((a j : ℝ) : ℂ) := by
    intro j
    rw [hreal _ (hspec j)]
    simp only [ha]
    push_cast
    ring
  have hterm_r : ∀ 𝔰 (r : ℝ), selbergTransform φ (r : ℂ) *
      ((‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 : ℝ) : ℂ) = ((b 𝔰 r : ℝ) : ℂ) := by
    intro 𝔰 r
    rw [hreal _ (Or.inl (Complex.ofReal_im r))]
    simp only [hb]
    push_cast
    ring
  have hterm_c : selbergTransform φ (Complex.I / 2) * ((n : ℂ) ^ 2 / (D.vol : ℂ)) =
      ((H (Complex.I / 2) ^ 2 * (n ^ 2 / D.vol) : ℝ) : ℂ) := by
    rw [hreal _ (Or.inr (by simp))]
    push_cast
    ring
  simp only [hterm_j, hterm_r] at hsum hint heq
  rw [hterm_c] at heq
  have hsumR : Summable a := Complex.summable_ofReal.1 hsum
  have hintR : ∀ 𝔰, Integrable (b 𝔰) := fun 𝔰 => by
    have := (hint 𝔰).re
    simpa using this
  set RHS : ℝ := (1 / 2 : ℝ) * ∑ i, ∑ i', ∑' γ : Gamma0 q,
    φ (pointPair (z i) ((γ : SL(2, ℤ)) • z i')) with hRHS
  have heqR : (∑' j, a j) + H (Complex.I / 2) ^ 2 * (n ^ 2 / D.vol) +
      1 / (4 * Real.pi) * ∑ 𝔰, ∫ r : ℝ, b 𝔰 r = RHS := by
    rw [← Complex.ofReal_tsum] at heq
    simp only [integral_complex_ofReal] at heq
    exact_mod_cast heq
  -- the geometric side: `0 ≤ k ≤ 4πβ`, and `k(z, w) = 0` unless `u(z, w) ≤ 1`
  have hRHS_le : RHS ≤ 2 * Real.pi * β * pairCountPts q z := by
    have hkey : ∀ i i', ∑' γ : Gamma0 q, φ (pointPair (z i) ((γ : SL(2, ℤ)) • z i')) ≤
        4 * Real.pi * β *
          ({γ : Gamma0 q | pointPair (z i) ((γ : SL(2, ℤ)) • z i') ≤ 1}.ncard : ℝ) := by
      intro i i'
      have hfin := Hyperbolic.finite_pointPair_le q (z i) (z i') 1
      rw [tsum_eq_sum (s := hfin.toFinset)]
      · rw [Set.ncard_eq_toFinset_card _ hfin]
        calc ∑ γ ∈ hfin.toFinset, φ (pointPair (z i) ((γ : SL(2, ℤ)) • z i'))
            ≤ ∑ γ ∈ hfin.toFinset, 4 * Real.pi * β := by
              apply Finset.sum_le_sum
              intro γ _
              rw [hφk]
              exact pairConv_le hβ _ _
          _ = 4 * Real.pi * β * hfin.toFinset.card := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
      · intro γ hγ
        rw [hφk]
        by_contra hne
        apply hγ
        rw [Set.Finite.mem_toFinset]
        have := pointPair_le_of_pairConv_ne_zero hβ hne
        show pointPair (z i) ((γ : SL(2, ℤ)) • z i') ≤ 1
        nlinarith
    rw [hRHS, pairCountPts]
    push_cast
    calc (1 / 2 : ℝ) * ∑ i, ∑ i', ∑' γ : Gamma0 q, φ (pointPair (z i) ((γ : SL(2, ℤ)) • z i'))
        ≤ (1 / 2 : ℝ) * ∑ i, ∑ i', 4 * Real.pi * β *
          ({γ : Gamma0 q | pointPair (z i) ((γ : SL(2, ℤ)) • z i') ≤ 1}.ncard : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => hkey i i'
      _ = 2 * Real.pi * β * ∑ i, ∑ i',
          ({γ : Gamma0 q | pointPair (z i) ((γ : SL(2, ℤ)) • z i') ≤ 1}.ncard : ℝ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i' _
          ring
  -- the spectral side: `h_{φ₁}(t) ≥ πβ` for `t ∈ [-T, T]` and for `t = iθ`
  set S₁ := {j | (D.t j).im = 0 ∧ (D.t j).re ≤ T} with hS₁
  set S₂ := {j | D.IsExceptional j} with hS₂
  have hH1 : ∀ j ∈ S₁, Real.pi * β ≤ H (D.t j) := by
    intro j hj
    obtain ⟨him, hre⟩ := hj
    have hre0 : 0 ≤ (D.t j).re := by
      rcases D.t_mem j with ⟨_, h⟩ | ⟨_, h, _⟩
      · exact h
      · linarith
    have e : D.t j = ((D.t j).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hH, e]
    apply lower_real hβ hβ1
    have : (D.t j).re ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hre0 hre 2
    nlinarith
  have hH2 : ∀ j ∈ S₂, Real.pi * β ≤ H (D.t j) := by
    intro j hj
    have hj' : 0 < (D.t j).im := hj
    have hre : (D.t j).re = 0 := by
      rcases D.t_mem j with ⟨h, _⟩ | ⟨h, _, _⟩
      · exact absurd h hj'.ne'
      · exact h
    have e : D.t j = Complex.I * ((D.t j).im : ℂ) := Complex.ext (by simp [hre]) (by simp)
    rw [hH, e]
    exact lower_imag hβ hβ1 _
  have hS₁fin : S₁.Finite := (D.finite_le T).subset fun j hj => by
    obtain ⟨him, hre⟩ := hj
    have hre0 : 0 ≤ (D.t j).re := by
      rcases D.t_mem j with ⟨_, h⟩ | ⟨_, h, _⟩
      · exact h
      · linarith
    have e : D.t j = ((D.t j).re : ℂ) := Complex.ext (by simp) (by simp [him])
    show ‖D.t j‖ ≤ T
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0]
    exact hre
  have hS₂fin : S₂.Finite := (D.finite_le T).subset fun j hj => by
    have hj' : 0 < (D.t j).im := hj
    obtain ⟨hre, hlt⟩ : (D.t j).re = 0 ∧ (D.t j).im < 1 / 2 := by
      rcases D.t_mem j with ⟨h, _⟩ | ⟨h, _, h'⟩
      · exact absurd h hj'.ne'
      · exact ⟨h, h'⟩
    have e : D.t j = Complex.I * ((D.t j).im : ℂ) := Complex.ext (by simp [hre]) (by simp)
    show ‖D.t j‖ ≤ T
    rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hj']
    linarith
  have hdisc : (Real.pi * β) ^ 2 * ((∑ᶠ j ∈ S₁, ‖∑ i, D.u j (z i)‖ ^ 2) +
      ∑ᶠ j ∈ S₂, ‖∑ i, D.u j (z i)‖ ^ 2) ≤ ∑' j, a j := by
    have hdisj : Disjoint S₁ S₂ := Set.disjoint_left.2 fun j h1 h2 => by
      have e1 : (D.t j).im = 0 := h1.1
      have e2 : 0 < (D.t j).im := h2
      linarith
    rw [← finsum_mem_union hdisj hS₁fin hS₂fin]
    have hU := hS₁fin.union hS₂fin
    rw [finsum_mem_eq_finite_toFinset_sum _ hU, Finset.mul_sum]
    calc ∑ j ∈ hU.toFinset, (Real.pi * β) ^ 2 * ‖∑ i, D.u j (z i)‖ ^ 2
        ≤ ∑ j ∈ hU.toFinset, a j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Set.Finite.mem_toFinset] at hj
          have hHj : Real.pi * β ≤ H (D.t j) := by
            rcases hj with h | h
            · exact hH1 j h
            · exact hH2 j h
          simp only [ha]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_pow_left₀ (by positivity) hHj 2
      _ ≤ ∑' j, a j := Summable.sum_le_tsum _ (fun j _ => by simp only [ha]; positivity) hsumR
  have hcont : ∀ 𝔰, (Real.pi * β) ^ 2 * ∫ r in Set.Icc (-T) T, ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 ≤
      ∫ r : ℝ, b 𝔰 r := by
    intro 𝔰
    rw [← integral_const_mul]
    calc ∫ r in Set.Icc (-T) T, (Real.pi * β) ^ 2 * ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2
        ≤ ∫ r in Set.Icc (-T) T, b 𝔰 r := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => by positivity)
            (hintR 𝔰).integrableOn
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          refine Filter.Eventually.of_forall fun r hr => ?_
          have hr' : |r| ≤ T := abs_le.2 hr
          have hHr : Real.pi * β ≤ H r := by
            rw [hH]
            apply lower_real hβ hβ1
            have : r ^ 2 ≤ T ^ 2 := by
              rw [← sq_abs r]; exact pow_le_pow_left₀ (abs_nonneg r) hr' 2
            nlinarith
          simp only [hb]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_pow_left₀ (by positivity) hHr 2
      _ ≤ ∫ r : ℝ, b 𝔰 r := setIntegral_le_integral (hintR 𝔰)
          (Filter.Eventually.of_forall fun r => by simp only [hb]; positivity)
  have hc0 : 0 ≤ H (Complex.I / 2) ^ 2 * (n ^ 2 / D.vol) := by
    have := D.vol_pos
    positivity
  -- conclusion
  set L := (∑ᶠ j ∈ S₁, ‖∑ i, D.u j (z i)‖ ^ 2) + (∑ᶠ j ∈ S₂, ‖∑ i, D.u j (z i)‖ ^ 2) +
    1 / (4 * Real.pi) * ∑ 𝔰, ∫ r in Set.Icc (-T) T, ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 with hL
  have hsc : (Real.pi * β) ^ 2 * (1 / (4 * Real.pi) *
      ∑ 𝔰, ∫ r in Set.Icc (-T) T, ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2) ≤
      1 / (4 * Real.pi) * ∑ 𝔰, ∫ r : ℝ, b 𝔰 r := by
    rw [← mul_assoc, mul_comm ((Real.pi * β) ^ 2), mul_assoc, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun 𝔰 _ => hcont 𝔰
  have hmain : (Real.pi * β) ^ 2 * L ≤ 2 * Real.pi * β * pairCountPts q z := by
    calc (Real.pi * β) ^ 2 * L = (Real.pi * β) ^ 2 * ((∑ᶠ j ∈ S₁, ‖∑ i, D.u j (z i)‖ ^ 2) +
          ∑ᶠ j ∈ S₂, ‖∑ i, D.u j (z i)‖ ^ 2) + (Real.pi * β) ^ 2 * (1 / (4 * Real.pi) *
          ∑ 𝔰, ∫ r in Set.Icc (-T) T, ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2) := by
          rw [hL]; ring
      _ ≤ (∑' j, a j) + H (Complex.I / 2) ^ 2 * (n ^ 2 / D.vol) +
          1 / (4 * Real.pi) * ∑ 𝔰, ∫ r : ℝ, b 𝔰 r := by linarith
      _ = RHS := heqR
      _ ≤ 2 * Real.pi * β * pairCountPts q z := hRHS_le
  have hP : (0 : ℝ) ≤ pairCountPts q z := Nat.cast_nonneg _
  have hLb : Real.pi * β * L ≤ 2 * pairCountPts q z := by
    have h' : (Real.pi * β) * (Real.pi * β * L) ≤ (Real.pi * β) * (2 * pairCountPts q z) := by
      calc (Real.pi * β) * (Real.pi * β * L) = (Real.pi * β) ^ 2 * L := by ring
        _ ≤ 2 * Real.pi * β * pairCountPts q z := hmain
        _ = (Real.pi * β) * (2 * pairCountPts q z) := by ring
    exact le_of_mul_le_mul_left h' (by positivity)
  calc L = (Real.pi * β * L) * (64 * T ^ 2 / Real.pi) := by
        rw [hβdef]; field_simp
    _ ≤ (2 * pairCountPts q z) * (64 * T ^ 2 / Real.pi) :=
        mul_le_mul_of_nonneg_right hLb (by positivity)
    _ ≤ 256 / Real.pi * T ^ 2 * pairCountPts q z := by
        have h0 : 0 ≤ T ^ 2 * pairCountPts q z / Real.pi := by positivity
        have e1 : (2 * (pairCountPts q z : ℝ)) * (64 * T ^ 2 / Real.pi) =
            128 * (T ^ 2 * pairCountPts q z / Real.pi) := by ring
        have e2 : 256 / Real.pi * T ^ 2 * (pairCountPts q z : ℝ) =
            256 * (T ^ 2 * pairCountPts q z / Real.pi) := by ring
        rw [e1, e2]
        linarith

end SpectralData

end Triples
