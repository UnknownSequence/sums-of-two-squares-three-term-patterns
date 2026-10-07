import TriplesFinal.Prelim.AfBound
import TriplesFinal.Prelim.Abel

/-!
# Lemma 5.3(c): convergence and size of the singular series

The series `𝔏_d = ∑_{k ≥ 1} χ(k) f(k)/k` converges (`Ld_tendsto`) and `|𝔏_d| ≪_ε d^(1+ε)`
(`Ld_bound`). Both follow from Lemma 5.3(b) by the Abelian theorem of `Prelim/Abel.lean`:
`𝔏_d = ∑_k A_f(k) (1/k - 1/(k+1))` (`IsGood.Ld_eq_and_tendsto`).

The product formula is in `Prelim/LdProduct.lean`, and part (d) in `Prelim/LdLower.lean`.

Paper: §5.3, Lemma 5.3(c).
-/

namespace Triples

open ZMod Filter Topology

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

section Convergence

variable {P}

/-- `g(k) = χ(k) f(k)` as a real sequence. -/
noncomputable def gR (P : PatternData a b) (d : ℕ) (k : ℕ) : ℝ := (P.gAF d k : ℝ)

theorem gR_zero (d : ℕ) : P.gR d 0 = 0 := by simp [gR]

theorem IsGood.gR_eq {d : ℕ} (hd : P.IsGood d) (k : ℕ) :
    P.gR d k = (χ₄ (k : ZMod 4) : ℝ) * P.fd d k := by
  rw [gR, P.gAF_apply, Int.cast_mul, hd.fAF_eq, chiAF_apply]

/-- The partial sums of `g` are the `A_f(N)`. -/
theorem IsGood.psum_gR {d : ℕ} (hd : P.IsGood d) (N : ℕ) : psum (P.gR d) N = P.Af d N := by
  rw [psum, Af, Nat.floor_natCast]
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 N) (s₂ := Finset.range (N + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    exact hd.gR_eq k
  · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
  · intro k hk1 hk
    rw [Finset.mem_range] at hk1
    simp only [Finset.mem_Icc, not_and, not_le] at hk
    have : k = 0 := by
      by_contra h0
      have := hk (by omega)
      omega
    subst this
    exact gR_zero d

theorem IsGood.LdPartial_eq {d : ℕ} (hd : P.IsGood d) (N : ℕ) :
    P.LdPartial d N = ∑ k ∈ Finset.range N, P.gR d k / k := by
  rw [LdPartial]
  apply Finset.sum_congr rfl
  intro k _
  rw [hd.gR_eq]

variable (P) in
/-- `|A_f(N)| ≤ C d^(1+ε) N^(1/2+ε)` (Lemma 5.3(b)) in the form used by the Abelian theorem. -/
theorem abs_psum_gR_le (hPV : PolyaVinogradov) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, P.IsGood d → ∀ N : ℕ, 1 ≤ N →
      |psum (P.gR d) N| ≤ (C * (d : ℝ) ^ (1 + ε)) * (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC⟩ := P.Af_bound hPV hε
  refine ⟨|C|, abs_nonneg _, fun d hd N hN => ?_⟩
  rw [hd.psum_gR]
  have h := hC d hd N (by exact_mod_cast hN)
  have h0 : 0 ≤ (N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε) := by positivity
  calc |P.Af d N| ≤ C * (N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε) := h
    _ = C * ((N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε)) := by ring
    _ ≤ |C| * ((N : ℝ) ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε)) := by gcongr; exact le_abs_self C
    _ = |C| * (d : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 / 2 + ε) := by ring

/-- `𝔏_d = ∑_k A_f(k) (1/k - 1/(k+1))`, and the partial sums converge to it. -/
theorem IsGood.Ld_eq_and_tendsto (hPV : PolyaVinogradov) {d : ℕ} (hd : P.IsGood d) :
    P.Ld d = ∑' k, abelTerm (P.gR d) 1 k ∧
      Tendsto (P.LdPartial d) atTop (𝓝 (P.Ld d)) := by
  obtain ⟨C, -, hC⟩ := P.abs_psum_gR_le hPV (ε := 1 / 4) (by norm_num)
  have hθ : (1 / 2 + 1 / 4 : ℝ) < 1 := by norm_num
  have h := tendsto_sum_div (gR_zero d) hθ (hC d hd)
  have h' : Tendsto (P.LdPartial d) atTop (𝓝 (∑' k, abelTerm (P.gR d) 1 k)) :=
    h.congr (fun N => (hd.LdPartial_eq N).symm)
  have hL : P.Ld d = ∑' k, abelTerm (P.gR d) 1 k := h'.limUnder_eq
  exact ⟨hL, hL ▸ h'⟩

variable (P) in
/-- **Lemma 5.3(c)**, convergence: the series `𝔏_d` converges. -/
theorem Ld_tendsto (hPV : PolyaVinogradov) {d : ℕ} (hd : P.IsGood d) :
    Tendsto (P.LdPartial d) atTop (𝓝 (P.Ld d)) :=
  (hd.Ld_eq_and_tendsto hPV).2

variable (P) in
/-- **Lemma 5.3(c)**, size: `|𝔏_d| ≪_ε d^(1+ε)`. -/
theorem Ld_bound (hPV : PolyaVinogradov) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ d : ℕ, P.IsGood d → |P.Ld d| ≤ C * (d : ℝ) ^ (1 + ε) := by
  set ε₀ := min ε (1 / 4) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀le : ε₀ ≤ ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := P.abs_psum_gR_le hPV hε₀pos
  have hθ : 1 / 2 + ε₀ < 1 := by have := min_le_right ε (1 / 4); linarith
  set Z := ∑' k : ℕ, (k : ℝ) ^ ((1 / 2 + ε₀) - 2) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  refine ⟨2 * C * Z, fun d hd => ?_⟩
  rw [(hd.Ld_eq_and_tendsto hPV).1]
  have h := abs_tsum_abelTerm_le (gR_zero d) hθ (hC d hd)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  have hdpow : (d : ℝ) ^ (1 + ε₀) ≤ (d : ℝ) ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  calc |∑' k, abelTerm (P.gR d) 1 k| ≤ 2 * (C * (d : ℝ) ^ (1 + ε₀)) * Z := h
    _ ≤ 2 * (C * (d : ℝ) ^ (1 + ε)) * Z := by gcongr
    _ = 2 * C * Z * (d : ℝ) ^ (1 + ε) := by ring


end Convergence

end PatternData

end Triples
