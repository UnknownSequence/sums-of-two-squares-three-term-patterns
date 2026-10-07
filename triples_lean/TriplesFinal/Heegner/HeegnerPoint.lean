import TriplesFinal.Heegner.Qkappa
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Heegner points `z(𝔤)` and equation (8.1)

To `𝔤 ∈ Q_N` we attach `z(𝔤) = (𝔟 + i√N)/𝔠 ∈ ℍ`. Equation (8.1): `z(γ ⋄ 𝔤) = γ · z(𝔤)` for
`γ ∈ SL₂(ℤ)`. For the matrix attached to `(μ, ℓ)` in Lemma 8.2(a),
`z(𝔤) = ℓ/μ + i√N/(Eμ)`.

Paper: §8.1, equation (8.1), and Lemma 8.2(a).
-/

namespace Triples

open scoped MatrixGroups

namespace SymMat

open UpperHalfPlane Complex

/-- The complex number `(𝔟 + i√(det 𝔤))/𝔠`. -/
noncomputable def zC (g : SymMat) : ℂ :=
  ((g.b : ℂ) + Complex.I * (Real.sqrt g.det : ℂ)) / (g.c : ℂ)

theorem zC_im (g : SymMat) : (zC g).im = Real.sqrt g.det / g.c := by
  simp [zC, Complex.div_im, Complex.normSq_intCast]
  rcases eq_or_ne (g.c : ℝ) 0 with h | h
  · simp [h]
  · field_simp

theorem zC_im_pos {g : SymMat} (hdet : 0 < g.det) (hc : 0 < g.c) : 0 < (zC g).im := by
  rw [zC_im]
  have : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have : (0 : ℝ) < g.c := by exact_mod_cast hc
  positivity

/-- The Heegner point `z(𝔤) = (𝔟 + i√N)/𝔠 ∈ ℍ` (and `i` for degenerate `𝔤`). -/
noncomputable def zpt (g : SymMat) : ℍ :=
  if h : 0 < g.det ∧ 0 < g.c then ⟨zC g, zC_im_pos h.1 h.2⟩ else UpperHalfPlane.I

theorem coe_zpt {g : SymMat} (hdet : 0 < g.det) (hc : 0 < g.c) : (zpt g : ℂ) = zC g := by
  simp [zpt, hdet, hc]

theorem coe_zpt_of_mem {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) :
    (zpt g : ℂ) = ((g.b : ℂ) + Complex.I * (Real.sqrt N : ℂ)) / (g.c : ℂ) := by
  obtain ⟨-, hc, hdet⟩ := hg
  rw [coe_zpt (hdet ▸ hN) hc, zC, hdet]

/-- `z(𝔤)` determines `𝔤` (for `𝔤 ∈ Q_N`). -/
theorem zpt_injOn {N : ℤ} (hN : 0 < N) : Set.InjOn zpt (QN N) := by
  intro g hg g' hg' h
  have h' := congrArg (fun z : ℍ => (z : ℂ)) h
  simp only [coe_zpt_of_mem hN hg, coe_zpt_of_mem hN hg'] at h'
  obtain ⟨ha, hc, hdet⟩ := hg
  obtain ⟨ha', hc', hdet'⟩ := hg'
  have hσ : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hc0 : (g.c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc0' : (g'.c : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [div_eq_div_iff hc0 hc0'] at h'
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp at hre him
  -- `𝔠' = 𝔠` (imaginary parts) and `𝔟 𝔠' = 𝔟' 𝔠` (real parts)
  have hc_eq : g.c = g'.c := by
    rcases him with h | h
    · exact_mod_cast h.symm
    · exact absurd h hσ.ne'
  have hcc : (g.c : ℝ) = g'.c := by exact_mod_cast hc_eq
  have hb_eq : g.b = g'.b := by
    have h1 : (g.b : ℝ) * g'.c = g'.b * g.c := by linarith
    rw [← hcc] at h1
    have : (g.b : ℝ) = g'.b := mul_right_cancel₀ (by exact_mod_cast hc.ne') h1
    exact_mod_cast this
  have ha_eq : g.a = g'.a := by
    simp only [det] at hdet hdet'
    rw [hc_eq, hb_eq] at hdet
    have : (g.a - g'.a) * g'.c = 0 := by linear_combination hdet - hdet'
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hc'.ne'
  exact SymMat.ext ha_eq hb_eq hc_eq

/-- **Equation (8.1):** `z(γ ⋄ 𝔤) = γ · z(𝔤)` for `γ ∈ SL₂(ℤ)` and `𝔤 ∈ Q_N`. -/
theorem zpt_act {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) (γ : SL(2, ℤ)) :
    zpt (act γ g) = γ • zpt g := by
  have hg' := act_mem_QN hN γ.det_coe hg
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_zpt_of_mem hN hg', coe_zpt_of_mem hN hg]
  obtain ⟨ha, hc, hdet⟩ := hg
  obtain ⟨-, hc', -⟩ := hg'
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  have hdetγ := γ.det_coe
  rw [Matrix.det_fin_two] at hdetγ
  set σ : ℂ := (Real.sqrt N : ℂ) with hσdef
  have hσ : σ ^ 2 = (g.a : ℂ) * g.c - (g.b : ℂ) ^ 2 := by
    rw [hσdef, ← Complex.ofReal_pow, Real.sq_sqrt (by exact_mod_cast hN.le)]
    simp only [det] at hdet
    rw [← hdet]; push_cast; ring
  have hD : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetγ
  have hc0 : (g.c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc0' : ((act γ g).c : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  set z : ℂ := ((g.b : ℂ) + Complex.I * σ) / (g.c : ℂ) with hzdef
  have hz : z * g.c = g.b + Complex.I * σ := by rw [hzdef]; field_simp
  -- the denominator `γ₃ z + γ₄` does not vanish
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    intro h0
    have hzim : 0 < z.im := by
      have := zC_im_pos (g := g) (hdet ▸ hN) hc
      simpa [zC, hzdef, hσdef, hdet] using this
    have him := congrArg Complex.im h0
    simp at him
    rcases him with h | h
    · have hr : γ 1 0 = 0 := by exact_mod_cast h
      have hs : γ 1 1 = 0 := by
        have hre := congrArg Complex.re h0
        simpa [hr] using hre
      rw [hr, hs] at hdetγ
      simp at hdetγ
    · exact absurd h hzim.ne'
  rw [div_eq_div_iff hc0' hden]
  apply mul_right_cancel₀ hc0
  simp only [act]
  push_cast
  linear_combination
    (((γ 0 0 * γ 1 0 * g.a + (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) * g.b + γ 0 1 * γ 1 1 * g.c : ℂ) +
        Complex.I * σ) * γ 1 0 -
      γ 0 0 * (γ 1 0 ^ 2 * g.a + 2 * γ 1 0 * γ 1 1 * g.b + γ 1 1 ^ 2 * g.c : ℂ)) * hz +
    ((γ 1 0 : ℂ) * σ ^ 2) * Complex.I_sq -
    (γ 1 0 : ℂ) * hσ +
    ((γ 1 0 : ℂ) * (g.a * g.c - g.b ^ 2) - Complex.I * σ * (γ 1 0 * g.b + γ 1 1 * g.c)) * hD

/-- **Lemma 8.2(a)**, the Heegner point of the matrix attached to `(μ, ℓ)`:
`z(𝔤) = ℓ/μ + i√N/(Eμ)`. -/
theorem zpt_ofPair {E H d κ : ℤ} (hE : 0 < E) (hH : 0 < H) {p : ℤ × ℤ}
    (hp : p ∈ pairSet E H d κ) :
    (zpt (ofPair E H p) : ℂ) =
      (p.2 : ℂ) / p.1 + Complex.I * (Real.sqrt (E * H) : ℂ) / (E * p.1) := by
  have hmem := (ofPair_bijOn (d := d) (κ := κ) hE hH).mapsTo hp
  rw [coe_zpt_of_mem (by positivity) hmem.1]
  obtain ⟨hμ, -, -⟩ := hp
  have hμ0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (show p.1 ≠ 0 by omega)
  have hE0 : (E : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
  simp only [ofPair]
  push_cast
  field_simp

end SymMat

end Triples
