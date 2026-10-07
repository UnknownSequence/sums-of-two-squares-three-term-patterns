import TriplesFinal.TypeIProof.XiMBound
import TriplesFinal.TypeIProof.Mopt
import TriplesFinal.Poisson.PoissonDyadic

/-!
# Auxiliary facts for the completion of the proof of Theorem 6.1

* (H) is preserved by `ψ₂ ↦ ψ₂(-·)` (`HypH.reflect`);
* the frequencies of `𝓜` satisfy `1/2 ≤ M ≤ 2h₀` (`mem_dyadicSet_bounds`);
* `(X/K) Y^(-1/2) = E^(1/2) N^(-1/4) X K^(-1/2)` (`Setup.Bk_eq`);
* enumerating the Heegner representatives turns the pair count into `pairCountPts`.

Paper: §12.6.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups
open SymMat

/-- (H) holds for `ψ₂(-·)` when it holds for `ψ₂`. -/
theorem HypH.reflect {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (h : HypH Cν E H d κ Δ X K ψ₁ ψ₂) : HypH Cν E H d κ Δ X K ψ₁ (reflect ψ₂) where
  hE := h.hE
  hH := h.hH
  hHodd := h.hHodd
  hd := h.hd
  hd3 := h.hd3
  hdH := h.hdH
  hNsq := h.hNsq
  hN3 := h.hN3
  hκ := h.hκ
  hΔ := h.hΔ
  hX := h.hX
  hK1 := h.hK1
  hKq := h.hKq
  smooth₁ := h.smooth₁
  smooth₂ := h.smooth₂.comp contDiff_neg
  supp₁ := h.supp₁
  supp₂ := fun t ht => by
    have := h.supp₂ (-t) ht
    constructor <;> linarith [this.1, this.2]
  deriv₁ := h.deriv₁
  deriv₂ := fun ν t => by
    have e : Triples.reflect ψ₂ = fun x => ψ₂ (-x) := rfl
    rw [e, iteratedDeriv_comp_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact h.deriv₂ ν (-t)

/-- The frequencies of `𝓜` lie in `[1/2, 2h₀]`. -/
theorem mem_dyadicSet_bounds {h0 M : ℝ} (hM : M ∈ dyadicSet h0) : 1 / 2 ≤ M ∧ M ≤ 2 * h0 := by
  unfold dyadicSet at hM
  rw [Finset.mem_filter, Finset.mem_image] at hM
  obtain ⟨⟨i, _, rfl⟩, hle⟩ := hM
  refine ⟨?_, hle⟩
  have hi : (-(1 : ℝ)) ≤ ((((i : ℤ) - 2 : ℤ) : ℝ)) / 2 := by
    push_cast
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  calc (1 / 2 : ℝ) = 2 ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hi

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν)

theorem N_pos : 0 < S.N := by linarith [S.N_ge]

/-- `(X/K) Y^(-1/2) = E^(1/2) N^(-1/4) X K^(-1/2)`. -/
theorem Bk_eq : S.Bk = Real.sqrt S.E * S.N ^ (-(1 / 4 : ℝ)) * (S.X * S.K ^ (-(1 / 2 : ℝ))) := by
  have hN := S.N_pos
  have hE : (0 : ℝ) < S.E := by have := S.E_ge; linarith
  have hK := S.K_pos
  have hX := S.X_pos
  have h1 : 0 ≤ S.Bk := S.Bk_pos.le
  have h2 : 0 ≤ Real.sqrt S.E * S.N ^ (-(1 / 4 : ℝ)) * (S.X * S.K ^ (-(1 / 2 : ℝ))) := by
    positivity
  apply (sq_eq_sq₀ h1 h2).1
  unfold Bk
  rw [S.Y_eq]
  have hsN : 0 < Real.sqrt S.N := Real.sqrt_pos.2 hN
  have hY0 : 0 ≤ Real.sqrt S.N / (S.E * S.K) := by positivity
  have eY : ((Real.sqrt S.N / (S.E * S.K)) ^ (-(1 / 2 : ℝ))) ^ 2 =
      S.E * S.K / Real.sqrt S.N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]
    norm_num
    rw [Real.rpow_neg_one, inv_div]
  have eN : (S.N ^ (-(1 / 4 : ℝ))) ^ 2 = (Real.sqrt S.N)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hN.le]
    norm_num
  have eK : (S.K ^ (-(1 / 2 : ℝ))) ^ 2 = S.K⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    norm_num
    rw [Real.rpow_neg_one]
  have eE : (Real.sqrt S.E) ^ 2 = S.E := Real.sq_sqrt hE.le
  rw [mul_pow, eY, mul_pow, mul_pow, mul_pow, eN, eK, eE]
  field_simp

end Setup

/-- The pair count of a finite set of representatives, through an enumeration. -/
theorem pairCount_eq_pairCountPts {q : ℕ} {R : Set SymMat} (hR : R.Finite) :
    pairCount q R = pairCountPts q (fun i : Fin hR.toFinset.card =>
      zpt (hR.toFinset.equivFin.symm i : SymMat)) := by
  unfold pairCount pairCountPts
  rw [finsum_mem_eq_sum_enum hR]
  apply Finset.sum_congr rfl
  intro i _
  rw [finsum_mem_eq_sum_enum hR]

end Triples
