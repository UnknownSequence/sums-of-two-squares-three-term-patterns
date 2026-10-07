import TriplesFinal.Poisson.Defs
import TriplesFinal.Heegner.Pairs

/-!
# Lemma 9.2: the Heegner–Poincaré identity

Let `g : (0, ∞) → ℂ` be smooth with compact support and `h ∈ ℤ`, and let
`P_{g,h}(z) = ∑_{γ ∈ Γ_∞ \ Γ} g(Im γz) e(h Re γz)` with `Γ = Γ₀(q)`, `q = 4Ed`. Then `P_{g,h}`
is `Γ`-invariant, and
`∑_{μ ≡ κd (4d)} g(√N/(Eμ)) S(h; μ) = ∑_{i=1}^{I} P_{g,h}(z_i)` (equation (9.2)),
where `z_1, …, z_I` are the Heegner points of the representatives of the `Γ`-orbits on `Q^κ`.
In particular `W_h = ∑_i P_h(z_i)` with `P_h = P_{g_h,h}` and
`g_h(y) = ψ₁(√N/(EKy)) (EXy/√N) ψ̂₂(EhXy/√N)` (equation (9.3)), supported in `[Y/2, Y]`.

This file contains the definitions, the `Γ₀(q)`-invariance of `P_{g,h}` (`poincare_invariant`)
and the weight `g_h`. The identities (9.2) and (9.3) are proved in
`Poisson/HeegnerPoincareIdentity.lean`, using the unfolding identity of `Poisson/Unfolding.lean`.

Paper: §9.2, Lemma 9.2.
-/

namespace Triples

open scoped MatrixGroups

open CongruenceSubgroup UpperHalfPlane SymMat
open scoped ContDiff

/-- `F_{c,d}(w) = (B w - A)/(c w + d)` with `cA + dB = 1` the Bézout coefficients: the Möbius
transformation of a matrix of `SL(2, ℤ)` with bottom row `(c, d)`. -/
noncomputable def mobBR (c d : ℤ) (w : ℂ) : ℂ :=
  ((Int.gcdB c d : ℂ) * w - Int.gcdA c d) / ((c : ℂ) * w + d)

/-- `c z + d ≠ 0` for `z ∈ ℍ` and `(c, d) ≠ (0, 0)`. -/
theorem linear_ne_zero' {c d : ℤ} (h : Int.gcd c d = 1) (z : ℍ) : (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  rcases him with hc | hz
  · subst hc
    simp at hre
    subst hre
    simp at h
  · exact (ne_of_gt z.im_pos) hz

theorem bezout_one {c d : ℤ} (h : Int.gcd c d = 1) : c * Int.gcdA c d + d * Int.gcdB c d = 1 := by
  have := Int.gcd_eq_gcd_ab c d
  rw [h] at this
  exact_mod_cast this.symm

/-- `Im F_{c,d}(z) = Im z / |cz + d|²`. -/
theorem imAct_eq {c d : ℤ} (h : Int.gcd c d = 1) (z : ℍ) :
    imAct c d z = (mobBR c d z).im := by
  have hD := linear_ne_zero' h z
  have hb := bezout_one h
  have hbC : (c : ℝ) * Int.gcdA c d + d * Int.gcdB c d = 1 := by exact_mod_cast hb
  unfold imAct mobBR
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
  have hn : Complex.normSq ((c : ℂ) * z + d) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  field_simp
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re]
  linear_combination (-(z.im : ℝ)) * hbC

/-- The bottom row of `δ γ`, for `δ` with bottom row `(c, d)`. -/
def brMul (γ : SL(2, ℤ)) (cd : ℤ × ℤ) : ℤ × ℤ :=
  (cd.1 * γ 0 0 + cd.2 * γ 1 0, cd.1 * γ 0 1 + cd.2 * γ 1 1)

theorem det_SL (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2
  rw [Matrix.det_fin_two] at this
  exact this

theorem brMul_gcd (γ : SL(2, ℤ)) {c d : ℤ} (h : Int.gcd c d = 1) :
    Int.gcd (brMul γ (c, d)).1 (brMul γ (c, d)).2 = 1 := by
  have hb := bezout_one h
  have hdet := det_SL γ
  rw [← Int.isCoprime_iff_gcd_eq_one]
  refine ⟨Int.gcdA c d * γ 1 1 - Int.gcdB c d * γ 0 1,
    -(Int.gcdA c d * γ 1 0) + Int.gcdB c d * γ 0 0, ?_⟩
  simp only [brMul]
  linear_combination (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) * hb + hdet

/-- **Translation property.** `F_{c,d}(γ z) = F_{(c,d)γ}(z) + k` for an integer `k`. -/
theorem mobBR_smul (γ : SL(2, ℤ)) {c d : ℤ} (h : Int.gcd c d = 1) (z : ℍ) :
    ∃ k : ℤ, mobBR c d ((γ • z : ℍ) : ℂ) =
      mobBR (brMul γ (c, d)).1 (brMul γ (c, d)).2 z + k := by
  have hz := UpperHalfPlane.coe_specialLinearGroup_apply γ z
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at hz
  have hDγ : ((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
    simpa [UpperHalfPlane.denom] using this
  have hD : (c : ℂ) * ((γ • z : ℍ) : ℂ) + d ≠ 0 := linear_ne_zero' h (γ • z)
  have h₂ : Int.gcd (brMul γ (c, d)).1 (brMul γ (c, d)).2 = 1 := brMul_gcd γ h
  have hD₂ := linear_ne_zero' h₂ z
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := det_SL γ
  set a := γ 0 0
  set b := γ 0 1
  set c' := γ 1 0
  set d' := γ 1 1
  set c₂ := (brMul γ (c, d)).1 with hc₂
  set d₂ := (brMul γ (c, d)).2 with hd₂
  have hc₂' : c₂ = c * a + d * c' := rfl
  have hd₂' : d₂ = c * b + d * d' := rfl
  set A := Int.gcdA c d
  set B := Int.gcdB c d
  set A₂ := Int.gcdA c₂ d₂
  set B₂ := Int.gcdB c₂ d₂
  have hb1 : c * A + d * B = 1 := bezout_one h
  have hb2 : c₂ * A₂ + d₂ * B₂ = 1 := bezout_one h₂
  set u := B * a - A * c' - B₂ with hu
  set v := B * b - A * d' + A₂ with hv
  have huv : u * d₂ = v * c₂ := by
    rw [hc₂', hd₂'] at hb2 ⊢
    linear_combination (B * d + A * c) * hdet + hb1 - hb2
  set k := u * A₂ + v * B₂ with hk
  refine ⟨k, ?_⟩
  have hk1 : k * c₂ = u := by rw [hk]; linear_combination u * hb2 - B₂ * huv
  have hk2 : k * d₂ = v := by rw [hk]; linear_combination v * hb2 + A₂ * huv
  have hk1C : (k : ℂ) * c₂ = (B : ℂ) * a - A * c' - B₂ := by
    have : k * c₂ = B * a - A * c' - B₂ := hk1
    exact_mod_cast this
  have hk2C : (k : ℂ) * d₂ = (B : ℂ) * b - A * d' + A₂ := by
    have : k * d₂ = B * b - A * d' + A₂ := hk2
    exact_mod_cast this
  have hc₂C : (c₂ : ℂ) = c * a + d * c' := by rw [hc₂']; push_cast; ring
  have hd₂C : (d₂ : ℂ) = c * b + d * d' := by rw [hd₂']; push_cast; ring
  have hDγ' : (z : ℂ) * c' + d' ≠ 0 := by rwa [mul_comm]
  unfold mobBR
  rw [hz]
  have hden : (c : ℂ) * ((a * z + b) / (c' * z + d')) + d = (c₂ * z + d₂) / (c' * z + d') := by
    rw [hc₂C, hd₂C]; field_simp; ring
  have hnum : (B : ℂ) * ((a * z + b) / (c' * z + d')) - A =
      ((B * a - A * c') * z + (B * b - A * d')) / (c' * z + d') := by
    field_simp; ring
  rw [hden, hnum, div_div_div_cancel_right₀ hDγ, div_add' _ _ _ hD₂]
  congr 1
  linear_combination (-(z : ℂ)) * hk1C - hk2C

theorem brMul_mul (γ₁ γ₂ : SL(2, ℤ)) (cd : ℤ × ℤ) :
    brMul (γ₁ * γ₂) cd = brMul γ₂ (brMul γ₁ cd) := by
  obtain ⟨c, d⟩ := cd
  simp only [brMul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem brMul_one (cd : ℤ × ℤ) : brMul 1 cd = cd := by
  obtain ⟨c, d⟩ := cd
  simp [brMul]

theorem brMul_mem {q : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 q) {cd : ℤ × ℤ}
    (h : cd ∈ bottomRows q) : brMul γ cd ∈ bottomRows q := by
  obtain ⟨c, d⟩ := cd
  refine ⟨brMul_gcd γ h.1, ?_⟩
  have hq : (q : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 (Gamma0_mem.1 hγ)
  exact dvd_add (dvd_mul_of_dvd_left h.2 _) (dvd_mul_of_dvd_right hq _)

/-- Right multiplication by `γ ∈ Γ₀(q)` permutes the bottom rows. -/
def brEquiv (q : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 q) : bottomRows q ≃ bottomRows q where
  toFun cd := ⟨brMul γ cd.1, brMul_mem hγ cd.2⟩
  invFun cd := ⟨brMul γ⁻¹ cd.1, brMul_mem (inv_mem hγ) cd.2⟩
  left_inv cd := Subtype.ext (by simp only; rw [← brMul_mul, mul_inv_cancel, brMul_one])
  right_inv cd := Subtype.ext (by simp only; rw [← brMul_mul, inv_mul_cancel, brMul_one])

/-- `P_{g,h}` is invariant under `Γ₀(q)`. -/
theorem poincare_invariant (q : ℕ) (g : ℝ → ℂ) (h : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 q)
    (z : ℍ) : poincare q g h (γ • z) = poincare q g h z := by
  unfold poincare
  congr 1
  refine Eq.trans ?_ ((brEquiv q γ hγ).tsum_eq (fun cd : bottomRows q =>
    g (imAct cd.1.1 cd.1.2 z) * Complex.exp (2 * Real.pi * Complex.I * h * reAct cd.1.1 cd.1.2 z)))
  apply tsum_congr
  rintro ⟨⟨c, d⟩, hcd⟩
  have hgcd : Int.gcd c d = 1 := hcd.1
  obtain ⟨k, hk⟩ := mobBR_smul γ hgcd z
  show g (imAct c d (γ • z)) * Complex.exp (2 * Real.pi * Complex.I * h * reAct c d (γ • z)) =
    g (imAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z) *
      Complex.exp (2 * Real.pi * Complex.I * h * reAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z)
  have him : imAct c d (γ • z) = imAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z := by
    rw [imAct_eq hgcd, imAct_eq (brMul_gcd γ hgcd), hk]
    simp
  have hre : reAct c d (γ • z) = reAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z + k := by
    have e1 : reAct c d (γ • z) = (mobBR c d ((γ • z : ℍ) : ℂ)).re := rfl
    have e2 : reAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z =
        (mobBR (brMul γ (c, d)).1 (brMul γ (c, d)).2 z).re := rfl
    rw [e1, e2, hk]
    simp
  rw [him, hre]
  congr 1
  have e : 2 * Real.pi * Complex.I * h *
      ((reAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z + k : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * h * (reAct (brMul γ (c, d)).1 (brMul γ (c, d)).2 z : ℝ) +
        ((h * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The weight `g_h(y) = ψ₁(√N/(EKy)) (EXy/√N) ψ̂₂(EhXy/√N)` of equation (9.3). -/
noncomputable def gh (E H : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) (h : ℤ) (y : ℝ) : ℂ :=
  ψ₁ (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y)) *
    ((E * X * y / Real.sqrt ((E * H : ℕ) : ℝ) : ℝ) : ℂ) *
    fourier ψ₂ (E * h * X * y / Real.sqrt ((E * H : ℕ) : ℝ))

end Triples
