import TriplesFinal.Poisson.HeegnerPoincare

/-!
# Lemma 9.2: unfolding the Poincaré series at the Heegner points

Let `𝒬 ⊆ Q_N` be `Γ = Γ₀(q)`-invariant (`N > 0` neither a square nor three times a square), and let
`𝔤_1, …, 𝔤_I` be the representatives `τ ⋄ ζ` of the `Γ`-orbits on `𝒬` (Lemma 8.1(b)), with
Heegner points `z_i = z(𝔤_i)`. For `G(z) = g(Im z) e(h Re z)` with `g` vanishing near `0`,
`∑_i P_{g,h}(z_i) = ∑_{𝔤 ∈ Γ_∞ \ 𝒬} G(z(𝔤))` (`sum_poincare_eq`).

The proof follows the paper: the map `(Γ_∞ γ, i) ↦ Γ_∞ ⋄ (γ ⋄ 𝔤_i)` is a bijection from
`(Γ_∞ \ Γ) × {1, …, I}` onto `Γ_∞ \ 𝒬` (by Lemma 8.1(a),(b)), and `G(γ z_i) = G(z(γ ⋄ 𝔤_i))`
by (8.1). In the formalization a coset `Γ_∞ γ` is a coprime bottom row `±(c, d)` with `q ∣ c`
(the Poincaré series is half the sum over all bottom rows), realised by the matrix
`(B, -A; c, d)` with `cA + dB = 1` (`mBR`), and the class `Γ_∞ ⋄ 𝔥` is represented by its
translate with `0 ≤ 𝔟 < 𝔠` (`red`). The map `Ψ(γ, 𝔤_i) = red(γ ⋄ 𝔤_i)` is two-to-one onto the
reduced elements of `𝒬`, with fibres `{(±γ, 𝔤_i)}` (`Ψ_fiber_eq`).

Paper: §9.2, Lemma 9.2 (first part of the proof).
-/

namespace Triples

open scoped MatrixGroups
open CongruenceSubgroup UpperHalfPlane SymMat

namespace SymMat

/-- The translation `T^t = (1 t; 0 1)`. -/
def mT (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, t; 0, 1]

theorem det_mT (t : ℤ) : (mT t).det = 1 := by
  simp [mT, Matrix.det_fin_two_of]

/-- `T^t` as an element of `SL₂(ℤ)`. -/
def sT (t : ℤ) : SL(2, ℤ) := ⟨mT t, det_mT t⟩

theorem sT_mem_Gamma0 (q : ℕ) (t : ℤ) : sT t ∈ Gamma0 q := by
  rw [Gamma0_mem]
  simp [sT, mT]

@[simp] theorem act_mT_a (t : ℤ) (g : SymMat) : (act (mT t) g).a = g.a + 2 * t * g.b + t ^ 2 * g.c := by
  simp [act, mT]

@[simp] theorem act_mT_b (t : ℤ) (g : SymMat) : (act (mT t) g).b = g.b + t * g.c := by
  simp [act, mT]

@[simp] theorem act_mT_c (t : ℤ) (g : SymMat) : (act (mT t) g).c = g.c := by
  simp [act, mT]

/-- The `Γ_∞`-reduction of `𝔤`: the translate `T^t ⋄ 𝔤` with `0 ≤ 𝔟 < 𝔠`. -/
def red (g : SymMat) : SymMat := act (mT (-(g.b / g.c))) g

theorem red_b (g : SymMat) : (red g).b = g.b % g.c := by
  rw [red, act_mT_b, Int.emod_def]; ring

theorem red_c (g : SymMat) : (red g).c = g.c := by
  rw [red, act_mT_c]

/-- Elements of `Q_N` with the same `𝔟` and `𝔠` coincide. -/
theorem eq_of_b_c {N : ℤ} {g g' : SymMat} (hg : g ∈ QN N) (hg' : g' ∈ QN N) (hb : g.b = g'.b)
    (hc : g.c = g'.c) : g = g' := by
  obtain ⟨-, hc0, hdet⟩ := hg
  obtain ⟨-, -, hdet'⟩ := hg'
  simp only [det] at hdet hdet'
  rw [hb, hc] at hdet
  have : (g.a - g'.a) * g'.c = 0 := by linear_combination hdet - hdet'
  rcases mul_eq_zero.1 this with h | h
  · exact SymMat.ext (by linarith) hb hc
  · rw [hc] at hc0; exact absurd h hc0.ne'

theorem act_mT_mem_QN {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) (t : ℤ) :
    act (mT t) g ∈ QN N :=
  act_mem_QN hN (det_mT t) hg

theorem red_mem_QN {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) : red g ∈ QN N :=
  act_mT_mem_QN hN hg _

theorem red_act_mT {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) (t : ℤ) :
    red (act (mT t) g) = red g := by
  apply eq_of_b_c (red_mem_QN hN (act_mT_mem_QN hN hg t)) (red_mem_QN hN hg)
  · rw [red_b, red_b, act_mT_b, act_mT_c, Int.add_mul_emod_self_right]
  · rw [red_c, red_c, act_mT_c]

theorem red_of_le {g : SymMat} (h0 : 0 ≤ g.b) (h1 : g.b < g.c) : red g = g := by
  have : g.b / g.c = 0 := Int.ediv_eq_zero_of_lt h0 h1
  rw [red, this, neg_zero]
  ext <;> simp

theorem red_b_nonneg {g : SymMat} (hc : 0 < g.c) : 0 ≤ (red g).b := by
  rw [red_b]; exact Int.emod_nonneg _ hc.ne'

theorem red_b_lt {g : SymMat} (hc : 0 < g.c) : (red g).b < (red g).c := by
  rw [red_b, red_c]; exact Int.emod_lt_of_pos _ hc

/-- Two matrices of determinant `1` with the same bottom row differ by a translation. -/
theorem mT_mul_of_bottom {γ γ' : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1) (hγ' : γ'.det = 1)
    (h10 : γ 1 0 = γ' 1 0) (h11 : γ 1 1 = γ' 1 1) :
    mT (γ' 0 1 * γ 0 0 - γ' 0 0 * γ 0 1) * γ = γ' := by
  rw [Matrix.det_fin_two] at hγ hγ'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mT, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [h10, h11] at hγ
    linear_combination γ' 0 0 * hγ - γ 0 0 * hγ' + (γ 0 0 * γ' 0 1 - γ' 0 0 * γ 0 1) * h10
  · rw [h10, h11] at hγ
    linear_combination γ' 0 1 * hγ - γ 0 1 * hγ' + (γ' 0 1 * γ 0 0 - γ 0 1 * γ' 0 0) * h11
  · exact h10
  · exact h11

theorem red_act_of_bottom {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N)
    {γ γ' : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1) (hγ' : γ'.det = 1)
    (h10 : γ 1 0 = γ' 1 0) (h11 : γ 1 1 = γ' 1 1) :
    red (act γ' g) = red (act γ g) := by
  rw [← mT_mul_of_bottom hγ hγ' h10 h11, act_mul, red_act_mT hN (act_mem_QN hN hγ hg)]

/-- The matrix `(B, -A; c, d)` with `cA + dB = 1` (Bézout coefficients). -/
def mBR (c d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![Int.gcdB c d, -Int.gcdA c d; c, d]

theorem det_mBR {c d : ℤ} (h : Int.gcd c d = 1) : (mBR c d).det = 1 := by
  rw [mBR, Matrix.det_fin_two_of]; linear_combination bezout_one h

/-- `(B, -A; c, d)` as an element of `SL₂(ℤ)`. -/
def sBR (c d : ℤ) (h : Int.gcd c d = 1) : SL(2, ℤ) := ⟨mBR c d, det_mBR h⟩

theorem sBR_mem_Gamma0 {q : ℕ} {c d : ℤ} (h : Int.gcd c d = 1) (hq : (q : ℤ) ∣ c) :
    sBR c d h ∈ Gamma0 q := by
  rw [Gamma0_mem]
  simpa [sBR, mBR] using (ZMod.intCast_zmod_eq_zero_iff_dvd c q).2 hq

theorem coe_sBR_smul {c d : ℤ} (h : Int.gcd c d = 1) (z : ℍ) :
    ((sBR c d h • z : ℍ) : ℂ) = mobBR c d z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [sBR, mBR, mobBR, sub_eq_add_neg]

/-- `G(z) = g(Im z) e(h Re z)`. -/
noncomputable def Gfun (g : ℝ → ℂ) (h : ℤ) (z : ℍ) : ℂ :=
  g z.im * Complex.exp (2 * Real.pi * Complex.I * h * z.re)

/-- The summand of the Poincaré series at the bottom row `(c, d)` is `G((B, -A; c, d) z)`. -/
theorem poincare_summand {c d : ℤ} (hcd : Int.gcd c d = 1) (g : ℝ → ℂ) (h : ℤ) (z : ℍ) :
    g (imAct c d z) * Complex.exp (2 * Real.pi * Complex.I * h * reAct c d z) =
      Gfun g h (sBR c d hcd • z) := by
  have e1 : (sBR c d hcd • z).im = imAct c d z := by
    rw [imAct_eq hcd, ← UpperHalfPlane.coe_im, coe_sBR_smul]
  have e2 : (sBR c d hcd • z).re = reAct c d z := by
    rw [← UpperHalfPlane.coe_re, coe_sBR_smul]; rfl
  rw [Gfun, e1, e2]

theorem zpt_im_re {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) :
    (zpt g).im = Real.sqrt N / g.c ∧ (zpt g).re = g.b / g.c := by
  have hz := coe_zpt_of_mem hN hg
  have hc : (g.c : ℂ) = ((g.c : ℝ) : ℂ) := by push_cast; rfl
  rw [hc] at hz
  constructor
  · rw [← UpperHalfPlane.coe_im, hz, Complex.div_ofReal_im]; simp
  · rw [← UpperHalfPlane.coe_re, hz, Complex.div_ofReal_re]; simp

theorem Gfun_zpt {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) (G : ℝ → ℂ) (h : ℤ) :
    Gfun G h (zpt g) = G (Real.sqrt N / g.c) *
      Complex.exp (2 * Real.pi * Complex.I * h * ((g.b : ℝ) / g.c : ℝ)) := by
  obtain ⟨h1, h2⟩ := zpt_im_re hN hg
  rw [Gfun, h1, h2]

theorem Gfun_zpt_red {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) (G : ℝ → ℂ) (h : ℤ) :
    Gfun G h (zpt (red g)) = Gfun G h (zpt g) := by
  rw [Gfun_zpt hN (red_mem_QN hN hg), Gfun_zpt hN hg, red_c, red_b]
  congr 1
  have hc : (g.c : ℝ) ≠ 0 := by have := hg.2.1; positivity
  have e : ((g.b % g.c : ℤ) : ℝ) / g.c = (g.b : ℝ) / g.c - ((g.b / g.c : ℤ) : ℝ) := by
    rw [Int.emod_def]; push_cast; field_simp
  rw [e]
  have e2 : 2 * (Real.pi : ℂ) * Complex.I * h * (((g.b : ℝ) / g.c - ((g.b / g.c : ℤ) : ℝ) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * h * (((g.b : ℝ) / g.c : ℝ) : ℂ) -
        ((h * (g.b / g.c) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e2, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The summand of the Poincaré series at a Heegner point. -/
theorem poincare_summand_zpt {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) {c d : ℤ}
    (hcd : Int.gcd c d = 1) (G : ℝ → ℂ) (h : ℤ) :
    G (imAct c d (zpt g)) * Complex.exp (2 * Real.pi * Complex.I * h * reAct c d (zpt g)) =
      Gfun G h (zpt (red (act (mBR c d) g))) := by
  rw [poincare_summand hcd, ← zpt_act hN hg, Gfun_zpt_red hN (act_mem_QN hN (det_mBR hcd) hg)]
  rfl

/-- The map `(γ, 𝔤) ↦ Γ_∞ ⋄ (γ ⋄ 𝔤)`, with the coset `Γ_∞ γ` given by the bottom row of `γ`
and `Γ_∞ ⋄ 𝔥` by its reduced representative. -/
def Ψ (x : (ℤ × ℤ) × SymMat) : SymMat := red (act (mBR x.1.1 x.1.2) x.2)

/-- The `Γ_∞`-reduced elements of `𝒬`: `0 ≤ 𝔟 < 𝔠`. -/
def fund (Q : Set SymMat) : Set SymMat := {s | s ∈ Q ∧ 0 ≤ s.b ∧ s.b < s.c}

theorem isCoprime_bottom (γ : SL(2, ℤ)) : Int.gcd (γ 1 0) (γ 1 1) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact ⟨-γ 0 1, γ 0 0, by linear_combination det_SL γ⟩

theorem bottomRows_neg {q : ℕ} {cd : ℤ × ℤ} (h : cd ∈ bottomRows q) : -cd ∈ bottomRows q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_neg, Prod.snd_neg, Int.gcd_neg, Int.neg_gcd]; exact h1
  · simp only [Prod.fst_neg, dvd_neg]; exact h2

section Counting

variable {N : ℤ} {q : ℕ} {Q : Set SymMat}

theorem Ψ_mem_fund (hQ : Q ⊆ QN N)
    (hQinv : ∀ γ ∈ Gamma0 q, ∀ g ∈ Q, act γ g ∈ Q) {x : (ℤ × ℤ) × SymMat}
    (h1 : x.1 ∈ bottomRows q) (h2 : x.2 ∈ Q) : Ψ x ∈ fund Q := by
  have hg : act (mBR x.1.1 x.1.2) x.2 ∈ Q :=
    hQinv (sBR x.1.1 x.1.2 h1.1) (sBR_mem_Gamma0 h1.1 h1.2) _ h2
  have hc : 0 < (act (mBR x.1.1 x.1.2) x.2).c := (hQ hg).2.1
  refine ⟨hQinv (sT _) (sT_mem_Gamma0 q _) _ hg, red_b_nonneg hc, red_b_lt hc⟩

theorem Ψ_neg (hN : 0 < N) (hQ : Q ⊆ QN N) {x : (ℤ × ℤ) × SymMat}
    (h1 : x.1 ∈ bottomRows q) (h2 : x.2 ∈ Q) : Ψ (-x.1, x.2) = Ψ x := by
  obtain ⟨⟨c, d⟩, g⟩ := x
  simp only [Ψ, Prod.fst_neg, Prod.snd_neg]
  have hcd : Int.gcd c d = 1 := h1.1
  have hcd' : Int.gcd (-c) (-d) = 1 := by rw [Int.gcd_neg, Int.neg_gcd]; exact hcd
  have hdet : (-(mBR c d)).det = 1 := by
    rw [Matrix.det_neg]; simp [det_mBR hcd]
  rw [red_act_of_bottom hN (hQ h2) hdet (det_mBR hcd') (by simp [mBR]) (by simp [mBR]), act_neg]

theorem bottom_sT_mul_sBR (t c d : ℤ) (h : Int.gcd c d = 1) :
    ((sT t * sBR c d h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c ∧
    ((sT t * sBR c d h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have e1 : ((sT t : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = mT t := rfl
  have e2 : ((sBR c d h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = mBR c d := rfl
  rw [e1, e2]
  simp [mT, mBR, Matrix.mul_apply, Fin.sum_univ_two]

theorem red_eq_act (g : SymMat) : ∃ t, red g = act (mT t) g := ⟨_, rfl⟩

/-- **Surjectivity.** Every `Γ_∞`-reduced element of `𝒬` is `Ψ(γ, 𝔤_i)` for a bottom row `γ` and
a Heegner representative `𝔤_i`. -/
theorem Ψ_surj (hN : 0 < N) (hQ : Q ⊆ QN N) (hQinv : ∀ γ ∈ Gamma0 q, ∀ g ∈ Q, act γ g ∈ Q)
    {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ) {T : Set SL(2, ℤ)} (hT : IsCosetReps q T)
    {s : SymMat} (hs : s ∈ fund Q) :
    ∃ x : (ℤ × ℤ) × SymMat, x.1 ∈ bottomRows q ∧ x.2 ∈ heegnerReps Λ T Q ∧ Ψ x = s := by
  obtain ⟨ζ, hζ, τ, hτ, hτζ, γ, hγ, hs'⟩ := orbit_reps_exists hΛ hT hQ hQinv hs.1
  refine ⟨((γ 1 0, γ 1 1), act τ ζ), ⟨isCoprime_bottom γ, ?_⟩, ⟨hτζ, ζ, hζ, τ, hτ, rfl⟩, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 (Gamma0_mem.1 hγ)
  · simp only [Ψ]
    rw [red_act_of_bottom hN (hQ hτζ) γ.det_coe (det_mBR (isCoprime_bottom γ)) (by simp [mBR])
      (by simp [mBR]), ← hs', red_of_le hs.2.1 hs.2.2]

/-- **The fibres.** `Ψ(γ', 𝔤_{i'}) = Ψ(γ, 𝔤_i)` only if `i' = i` and `γ' = ±γ`. -/
theorem Ψ_fiber (hN : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2) (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2)
    (hQ : Q ⊆ QN N) {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {x x' : (ℤ × ℤ) × SymMat}
    (h1 : x.1 ∈ bottomRows q) (h2 : x.2 ∈ heegnerReps Λ T Q)
    (h1' : x'.1 ∈ bottomRows q) (h2' : x'.2 ∈ heegnerReps Λ T Q) (h : Ψ x' = Ψ x) :
    x'.2 = x.2 ∧ (x'.1 = x.1 ∨ x'.1 = -x.1) := by
  obtain ⟨⟨c, d⟩, g⟩ := x
  obtain ⟨⟨c', d'⟩, g'⟩ := x'
  obtain ⟨hgQ, ζ, hζ, τ, hτ, rfl⟩ := h2
  obtain ⟨hgQ', ζ', hζ', τ', hτ', rfl⟩ := h2'
  have hcd : Int.gcd c d = 1 := h1.1
  have hcd' : Int.gcd c' d' = 1 := h1'.1
  simp only [Ψ] at h
  obtain ⟨t, ht⟩ := red_eq_act (act (mBR c d) (act τ ζ))
  obtain ⟨t', ht'⟩ := red_eq_act (act (mBR c' d') (act τ' ζ'))
  rw [ht, ht'] at h
  set A : SL(2, ℤ) := sT t' * sBR c' d' hcd' with hA
  set B : SL(2, ℤ) := sT t * sBR c d hcd with hB
  have hAB : act A (act τ' ζ') = act B (act τ ζ) := by
    rw [hA, hB, act_coe_mul, act_coe_mul]; exact h
  have hA0 : A ∈ Gamma0 q := mul_mem (sT_mem_Gamma0 q t') (sBR_mem_Gamma0 hcd' h1'.2)
  have hB0 : B ∈ Gamma0 q := mul_mem (sT_mem_Gamma0 q t) (sBR_mem_Gamma0 hcd h1.2)
  have hγ : A⁻¹ * B ∈ Gamma0 q := mul_mem (inv_mem hA0) hB0
  have hg' : act τ' ζ' = act ((A⁻¹ * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (act τ ζ) := by
    rw [act_coe_mul, ← hAB, act_coe_inv_act]
  obtain ⟨hζζ, hττ⟩ := orbit_reps_unique hN hsq h3 hΛ hT hζ hζ' hτ hτ' hγ hg'
  subst hζζ hττ
  refine ⟨rfl, ?_⟩
  have hfix : act ((A⁻¹ * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (act τ' ζ') = act τ' ζ' :=
    hg'.symm
  obtain ⟨hBc, hBd⟩ := bottom_sT_mul_sBR t c d hcd
  obtain ⟨hAc, hAd⟩ := bottom_sT_mul_sBR t' c' d' hcd'
  rw [← hA] at hAc hAd
  rw [← hB] at hBc hBd
  rcases stabiliser_SL hN hsq h3 (hQ hgQ) hfix with h1 | h1
  · left
    have : B = A := by
      have := congrArg (A * ·) h1
      simpa [← mul_assoc] using this
    rw [this] at hBc hBd
    rw [Prod.mk.injEq]
    exact ⟨hAc.symm.trans hBc, hAd.symm.trans hBd⟩
  · right
    have : B = -A := by
      have := congrArg (A * ·) h1
      simpa [← mul_assoc] using this
    rw [this, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hBc hBd
    rw [Prod.neg_mk, Prod.mk.injEq]
    exact ⟨by rw [← hAc, ← hBc, neg_neg], by rw [← hAd, ← hBd, neg_neg]⟩

/-- The reduced elements of `𝒬` at which `G` does not vanish form a finite set. -/
theorem fund_support_finite (hQ : Q ⊆ QN N) {G : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hG : ∀ y, G y ≠ 0 → a ≤ y) :
    {s | s ∈ fund Q ∧ G (Real.sqrt N / s.c) ≠ 0}.Finite := by
  set C : ℤ := ⌈Real.sqrt N / a⌉
  apply (((Set.finite_Icc (0 : ℤ) C).prod (Set.finite_Icc (0 : ℤ) C)).image
    (fun p : ℤ × ℤ => (⟨(N + p.1 ^ 2) / p.2, p.1, p.2⟩ : SymMat))).subset
  rintro s ⟨⟨hsQ, hb0, hbc⟩, hG0⟩
  have hsN := hQ hsQ
  have hc0 : 0 < s.c := hsN.2.1
  have hle : a ≤ Real.sqrt N / s.c := hG _ hG0
  have hcC : s.c ≤ C := by
    have hc' : (0 : ℝ) < s.c := by exact_mod_cast hc0
    have : (s.c : ℝ) ≤ Real.sqrt N / a := by
      rw [le_div_iff₀ ha]; rw [le_div_iff₀ hc'] at hle; linarith
    exact_mod_cast this.trans (Int.le_ceil _)
  refine ⟨(s.b, s.c), ⟨⟨hb0, by omega⟩, ⟨hc0.le, hcC⟩⟩, ?_⟩
  have hdet := hsN.2.2
  simp only [det] at hdet
  ext
  · show (N + s.b ^ 2) / s.c = s.a
    rw [← hdet, show s.a * s.c - s.b ^ 2 + s.b ^ 2 = s.a * s.c by ring]
    exact Int.mul_ediv_cancel s.a hc0.ne'
  · rfl
  · rfl

theorem ne_neg_of_mem_bottomRows {cd : ℤ × ℤ} (h : cd ∈ bottomRows q) : cd ≠ -cd := by
  intro e
  have h1 : cd.1 = 0 := by have := congrArg Prod.fst e; simp at this; omega
  have h2 : cd.2 = 0 := by have := congrArg Prod.snd e; simp at this; omega
  have := h.1
  rw [h1, h2] at this
  simp at this

/-- Each fibre of `Ψ` over a reduced element of `𝒬` has exactly the two elements `(±γ, 𝔤_i)`. -/
theorem Ψ_fiber_eq (hN : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2) (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2)
    (hQ : Q ⊆ QN N) (hQinv : ∀ γ ∈ Gamma0 q, ∀ g ∈ Q, act γ g ∈ Q)
    {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ) {T : Set SL(2, ℤ)} (hT : IsCosetReps q T)
    {s : SymMat} (hs : s ∈ fund Q) :
    ∃ x₀ : (ℤ × ℤ) × SymMat, x₀ ≠ (-x₀.1, x₀.2) ∧
      {x | x.1 ∈ bottomRows q ∧ x.2 ∈ heegnerReps Λ T Q ∧ Ψ x = s} = {x₀, (-x₀.1, x₀.2)} := by
  obtain ⟨x₀, h1, h2, h3'⟩ := Ψ_surj hN hQ hQinv hΛ hT hs
  refine ⟨x₀, fun e => ne_neg_of_mem_bottomRows h1 (congrArg Prod.fst e), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx1, hx2, hx3⟩
    obtain ⟨e2, e1 | e1⟩ := Ψ_fiber hN hsq h3 hQ hΛ hT h1 h2 hx1 hx2 (hx3.trans h3'.symm)
    · left; exact Prod.ext e1 e2
    · right; exact Prod.ext e1 e2
  · rintro (rfl | rfl)
    · exact ⟨h1, h2, h3'⟩
    · exact ⟨bottomRows_neg h1, h2, (Ψ_neg hN hQ h1 h2.1).trans h3'⟩

/-- **The unfolding identity.** `∑_i P_{G,h}(z_i) = ∑_{𝔤 ∈ Γ_∞ \ 𝒬} G(z(𝔤))`. -/
theorem sum_poincare_eq (hN : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2)
    (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2) (hQ : Q ⊆ QN N)
    (hQinv : ∀ γ ∈ Gamma0 q, ∀ g ∈ Q, act γ g ∈ Q)
    {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ) {T : Set SL(2, ℤ)} (hT : IsCosetReps q T)
    {G : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hG : ∀ y, G y ≠ 0 → a ≤ y) (h : ℤ) :
    ∑ᶠ g' ∈ heegnerReps Λ T Q, poincare q G h (zpt g') =
      ∑ᶠ s ∈ fund Q, Gfun G h (zpt s) := by
  classical
  set S := {s | s ∈ fund Q ∧ G (Real.sqrt N / s.c) ≠ 0} with hSdef
  have hSfin : S.Finite := fund_support_finite hQ ha hG
  set X := {x : (ℤ × ℤ) × SymMat | x.1 ∈ bottomRows q ∧ x.2 ∈ heegnerReps Λ T Q ∧ Ψ x ∈ S}
    with hXdef
  have hXfin : X.Finite := by
    apply (hSfin.biUnion (t := fun s =>
      {x : (ℤ × ℤ) × SymMat | x.1 ∈ bottomRows q ∧ x.2 ∈ heegnerReps Λ T Q ∧ Ψ x = s})
      ?_).subset
    · rintro x ⟨hx1, hx2, hx3⟩
      exact Set.mem_biUnion hx3 ⟨hx1, hx2, rfl⟩
    · intro s hs
      obtain ⟨x₀, -, he⟩ := Ψ_fiber_eq hN hsq h3 hQ hQinv hΛ hT hs.1
      rw [he]
      exact (Set.finite_singleton _).insert _
  set Φ : (ℤ × ℤ) × SymMat → ℂ := fun x => Gfun G h (zpt (Ψ x)) with hΦ
  -- `Gfun` vanishes on the reduced elements outside `S`
  have hGfun : ∀ s ∈ fund Q, Gfun G h (zpt s) ≠ 0 → s ∈ S := by
    intro s hs hne
    refine ⟨hs, fun h0 => hne ?_⟩
    rw [Gfun_zpt hN (hQ hs.1), h0, zero_mul]
  -- Step 1: `∑_{x ∈ X} Φ(x) = 2 ∑_{s ∈ S} G(z(s))`
  have step1 : ∑ x ∈ hXfin.toFinset, Φ x = ∑ s ∈ hSfin.toFinset, 2 * Gfun G h (zpt s) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Ψ) (t := hSfin.toFinset)]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [Set.Finite.mem_toFinset] at hs
      obtain ⟨x₀, hne, he⟩ := Ψ_fiber_eq hN hsq h3 hQ hQinv hΛ hT hs.1
      have hfib : hXfin.toFinset.filter (fun x => Ψ x = s) = {x₀, (-x₀.1, x₀.2)} := by
        ext x
        have hmem := Set.ext_iff.1 he x
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
          Finset.mem_singleton, hXdef, Set.mem_ofPred_eq]
        rw [← hmem]
        constructor
        · rintro ⟨⟨hx1, hx2, -⟩, hx3⟩; exact ⟨hx1, hx2, hx3⟩
        · rintro ⟨hx1, hx2, hx3⟩; exact ⟨⟨hx1, hx2, hx3 ▸ hs⟩, hx3⟩
      have hx₀ : x₀ ∈ ({x₀, (-x₀.1, x₀.2)} : Set _) := Set.mem_insert _ _
      have hx₀' : (-x₀.1, x₀.2) ∈ ({x₀, (-x₀.1, x₀.2)} : Set _) :=
        Set.mem_insert_of_mem _ rfl
      rw [← he] at hx₀ hx₀'
      rw [hfib, Finset.sum_pair hne]
      simp only [hΦ, hx₀.2.2, hx₀'.2.2]
      ring
    · intro x hx
      rw [Set.Finite.mem_toFinset] at hx ⊢
      exact hx.2.2
  -- Step 2: the Poincaré series at `z(𝔤_i)` is the sum of `Φ` over the fibre of `i`
  have step2 : ∀ g' ∈ heegnerReps Λ T Q, poincare q G h (zpt g') =
      (1 / 2 : ℂ) * ∑ x ∈ hXfin.toFinset.filter (fun x => x.2 = g'), Φ x := by
    intro g' hg'
    have hg'N : g' ∈ QN N := hQ hg'.1
    unfold poincare
    congr 1
    rw [tsum_subtype (bottomRows q) (fun p : ℤ × ℤ =>
      G (imAct p.1 p.2 (zpt g')) * Complex.exp (2 * Real.pi * Complex.I * h * reAct p.1 p.2 (zpt g')))]
    rw [tsum_eq_sum (s := (hXfin.toFinset.filter (fun x => x.2 = g')).image Prod.fst)]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hx
        obtain ⟨⟨hx1, -, -⟩, hx2⟩ := hx
        rw [Set.indicator_of_mem hx1, poincare_summand_zpt hN hg'N hx1.1, hΦ]
        simp only [Ψ, ← hx2]
      · intro x hx y hy hxy
        simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx hy
        exact Prod.ext hxy (hx.2.trans hy.2.symm)
    · intro p hp
      by_cases hpB : p ∈ bottomRows q
      · rw [Set.indicator_of_mem hpB, poincare_summand_zpt hN hg'N hpB.1]
        by_contra hne
        apply hp
        rw [Finset.mem_image]
        refine ⟨(p, g'), ?_, rfl⟩
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨hpB, hg', hGfun _ (Ψ_mem_fund hQ hQinv (x := (p, g')) hpB hg'.1) hne⟩, rfl⟩
      · exact Set.indicator_of_notMem hpB _
  -- Step 3: assemble
  rw [finsum_mem_congr rfl step2]
  rw [finsum_mem_eq_sum_of_subset _ (t := hXfin.toFinset.image Prod.snd)]
  · rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (g := Prod.snd)
      (fun x hx => Finset.mem_image_of_mem _ hx), step1]
    rw [finsum_mem_eq_sum_of_subset _ (t := hSfin.toFinset)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    · intro s ⟨hs, hne⟩
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact hGfun s hs hne
    · intro s hs
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
      exact hs.1
  · intro g' ⟨hg', hne⟩
    rw [Finset.mem_coe, Finset.mem_image]
    by_contra hno
    apply hne
    dsimp only
    rw [Finset.sum_eq_zero, mul_zero]
    intro x hx
    rw [Finset.mem_filter] at hx
    exact absurd ⟨x, hx.1, hx.2⟩ hno
  · intro g' hg'
    rw [Finset.mem_coe, Finset.mem_image] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    rw [Set.Finite.mem_toFinset] at hx
    exact hx.2.1

end Counting

end SymMat

end Triples
