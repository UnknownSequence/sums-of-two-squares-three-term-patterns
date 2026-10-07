import TriplesFinal.Poisson.HeegnerPoincareIdentity
import TriplesFinal.Heegner.Reduction
import TriplesFinal.Poisson.FourierBump
import TriplesFinal.Assumptions.Assumptions

/-!
# Lemma 10.1: the spectral expansion of `Ξ_M`

For `M ∈ 𝓜`, with `U_j = ∑_i u_j(z_i)`, `U_𝔰(r) = ∑_i E_𝔰(z_i, 1/2 + ir)`,
`B_j = ∑_{h ≥ 1} ψ₀(h/M) conj(ρ_j(h)) ǧ_h(t_j)` and
`B_𝔰(r) = ∑_{h ≥ 1} ψ₀(h/M) conj(ρ_𝔰(h, r)) ǧ_h(r)`:
`Ξ_M(ψ₂) = ∑_j B_j U_j + (1/4π) ∑_𝔰 ∫ B_𝔰(r) U_𝔰(r) dr`, with absolute convergence.

By Lemma 9.2, `Ξ_M(ψ₂) = ∑_h ψ₀(h/M) ∑_i P_h(z_i)`. The weight `g_h` is smooth (`contDiff_gh`;
`y ↦ ψ₁(c/y)` vanishes near `0`, and `ψ̂₂` is smooth) and supported in `[Y/2, Y]`, so
`PoincareExpansion` applies to each `P_h`. The Heegner representatives are finite in number
(`heegnerReps_finite`, by reduction theory), so the finite sums over `h` and `i` can be exchanged
with the spectral sum and integral.

Paper: §10.2, Lemma 10.1.
-/

namespace Triples

open scoped MatrixGroups ContDiff
open CongruenceSubgroup UpperHalfPlane SymMat MeasureTheory

/-- `y ↦ ψ(c/y)` is smooth if `ψ` is smooth and supported in `[1, 2]`: it vanishes near `0`. -/
theorem contDiff_comp_div {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ t, ψ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (fun y => ψ (c / y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hev : (fun y => ψ (c / y)) =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds (show -(c / 2) < (0 : ℝ) by linarith)
        (show (0 : ℝ) < c / 2 by linarith)] with y hy
      by_contra hne
      obtain ⟨h1, h2⟩ := hs _ hne
      rcases lt_trichotomy y 0 with hneg | hzero | hpos
      · have : c / y < 0 := div_neg_of_pos_of_neg hc hneg
        linarith
      · rw [hzero, div_zero] at h1; linarith
      · have : 2 < c / y := by rw [lt_div_iff₀ hpos]; linarith [hy.2]
        linarith
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hψ.contDiffAt.comp y (contDiffAt_const.div contDiffAt_id hy)

/-- A smooth function supported in `[-1, 1]` has a smooth Fourier transform. -/
theorem contDiff_fourier_of_supp {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) : ContDiff ℝ ∞ (fourier ψ) := by
  rw [fourier_eq_fourierIntegral]
  have hcs : HasCompactSupport ψ := HasCompactSupport.intro isCompact_Icc fun x hx => by
    by_contra hne; exact hx (hs x hne)
  exact Real.contDiff_fourier fun n _ =>
    ((continuous_norm.pow n).mul hψ.continuous.norm).integrable_of_hasCompactSupport
      hcs.norm.mul_left

variable {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}

/-- `g_h` is smooth. -/
theorem contDiff_gh (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) (h : ℤ) :
    ContDiff ℝ ∞ (gh E H X K ψ₁ ψ₂ h) := by
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hH0 : 0 < H := hH.hH
  have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hs : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => ψ₁ (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y))) := by
    have := contDiff_comp_div hH.smooth₁ hH.supp₁
      (c := Real.sqrt ((E * H : ℕ) : ℝ) / (E * K)) (by positivity)
    convert this using 2 with y
    rw [div_div]
  have h2 : ContDiff ℝ ∞ (fun y : ℝ => ((E * X * y / Real.sqrt ((E * H : ℕ) : ℝ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const _)
  have h3 : ContDiff ℝ ∞ (fun y : ℝ => fourier ψ₂ (E * h * X * y / Real.sqrt ((E * H : ℕ) : ℝ))) :=
    (contDiff_fourier_of_supp hH.smooth₂ hH.supp₂).comp ((contDiff_const.mul contDiff_id).div_const _)
  exact (h1.mul h2).mul h3

/-- `g_h` is supported in `[√N/(2EK), √N/(EK)]`. -/
theorem gh_support (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) (h : ℤ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ y, gh E H X K ψ₁ ψ₂ h y ≠ 0 → a ≤ y ∧ y ≤ b := by
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hH0 : 0 < H := hH.hH
  have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hs : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.sqrt ((E * H : ℕ) : ℝ) / (2 * E * K), Real.sqrt ((E * H : ℕ) : ℝ) / (E * K),
    by positivity, fun y hy => ?_⟩
  have h1 : ψ₁ (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y)) ≠ 0 := by
    intro h0; apply hy; unfold gh; rw [h0, zero_mul, zero_mul]
  obtain ⟨hlo, hhi⟩ := hH.supp₁ _ h1
  have hy0 : 0 < y := by
    by_contra hy0
    push Not at hy0
    have : Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hs.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy0)
    linarith
  constructor
  · rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hhi
    linarith
  · rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hlo
    linarith

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

/-- `U_j = ∑_i u_j(z_i)` over a finite set `R` of representatives. -/
noncomputable def Uj (R : Set SymMat) (j : D.ι) : ℂ := ∑ᶠ g ∈ R, D.u j (zpt g)

/-- `U_𝔰(r) = ∑_i E_𝔰(z_i, 1/2 + ir)`. -/
noncomputable def Us (R : Set SymMat) (𝔰 : D.κ) (r : ℝ) : ℂ := ∑ᶠ g ∈ R, D.Eis 𝔰 r (zpt g)

/-- `B_j = ∑_{h ≥ 1} ψ₀(h/M) conj(ρ_j(h)) ǧ_h(t_j)`. -/
noncomputable def Bj (ψ₀ : DyadicPartition) (E H : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) (M : ℝ)
    (j : D.ι) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊2 * M⌋₊, (ψ₀.ψ₀ (h / M) : ℂ) * (starRingEnd ℂ) (D.ρ j h) *
    besselTransform (gh E H X K ψ₁ ψ₂ h) h (D.t j)

/-- `B_𝔰(r) = ∑_{h ≥ 1} ψ₀(h/M) conj(ρ_𝔰(h, r)) ǧ_h(r)`. -/
noncomputable def Bs (ψ₀ : DyadicPartition) (E H : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) (M : ℝ)
    (𝔰 : D.κ) (r : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊2 * M⌋₊, (ψ₀.ψ₀ (h / M) : ℂ) * (starRingEnd ℂ) (D.ρEis 𝔰 r h) *
    besselTransform (gh E H X K ψ₁ ψ₂ h) h r

/-- **Lemma 10.1.** -/
theorem expansion (hPE : D.PoincareExpansion) (ψ₀ : DyadicPartition) {Cν : ℕ → ℝ}
    {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ} (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂)
    (hq : q = 4 * E * d) {Λ : Set SymMat} (hΛ : IsOrbitReps ((E : ℤ) * H) Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {M : ℝ} (_hM : 1 / 2 ≤ M) :
    let R := heegnerReps Λ T (Qkappa E H d κ)
    Summable (fun j => ‖D.Bj ψ₀ E H X K ψ₁ ψ₂ M j * D.Uj R j‖) ∧
      XiM ψ₀ E H d κ X K ψ₁ ψ₂ M =
        (∑' j, D.Bj ψ₀ E H X K ψ₁ ψ₂ M j * D.Uj R j) +
          (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, D.Bs ψ₀ E H X K ψ₁ ψ₂ M 𝔰 r * D.Us R 𝔰 r := by
  intro R
  classical
  subst hq
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hd2 : (d : ℤ) ≠ 2 := by have := hH.hd3; omega
  have hRfin : R.Finite := heegnerReps_finite (E := (E : ℤ)) (H := H) (d := d) (κ := κ)
    (by rcases hH.hE with h | h <;> rw [h] <;> norm_num) (by exact_mod_cast hH.hH)
    (Nat.prime_iff_prime_int.mp hH.hd) (by exact_mod_cast hH.hd.pos) hd2
    (by exact_mod_cast hH.hdH) (by push_cast; ring) hΛ hT
  set Rf := hRfin.toFinset with hRf
  set Hs := Finset.Icc 1 ⌊2 * M⌋₊ with hHs
  -- the coefficients of the expansion of `P_h`
  set c : ℕ → D.ι → ℂ := fun h j =>
    (starRingEnd ℂ) (D.ρ j h) * besselTransform (gh E H X K ψ₁ ψ₂ h) h (D.t j) with hc
  set cs : ℕ → D.κ → ℝ → ℂ := fun h 𝔰 r =>
    (starRingEnd ℂ) (D.ρEis 𝔰 r h) * besselTransform (gh E H X K ψ₁ ψ₂ h) h r with hcs
  have hPEh : ∀ h ∈ Hs, ∀ z : ℍ, Summable (fun j => ‖c h j * D.u j z‖) ∧
      (∀ 𝔰, Integrable (fun r : ℝ => cs h 𝔰 r * D.Eis 𝔰 r z)) ∧
      poincare (4 * E * d) (gh E H X K ψ₁ ψ₂ h) h z =
        (∑' j, c h j * D.u j z) +
          (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, cs h 𝔰 r * D.Eis 𝔰 r z := by
    intro h hh z
    have hh1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
    exact hPE (gh E H X K ψ₁ ψ₂ h) (contDiff_gh hH h) (gh_support hH h) h
      (by exact_mod_cast (show h ≠ 0 by omega)) z
  -- `Ξ_M` as a finite double sum
  have hXi : XiM ψ₀ E H d κ X K ψ₁ ψ₂ M = ∑ h ∈ Hs, ∑ g ∈ Rf,
      (ψ₀.ψ₀ (h / M) : ℂ) * poincare (4 * E * d) (gh E H X K ψ₁ ψ₂ h) h (zpt g) := by
    unfold XiM
    apply Finset.sum_congr rfl
    intro h hh
    have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast (Finset.mem_Icc.1 hh).1
    rw [Wh_eq_sum_poincare hH hΛ hT hh1, finsum_mem_eq_finite_toFinset_sum _ hRfin,
      Finset.mul_sum]
  -- `B_j U_j` and `B_𝔰(r) U_𝔰(r)` as finite double sums
  have hBU : ∀ j, D.Bj ψ₀ E H X K ψ₁ ψ₂ M j * D.Uj R j =
      ∑ h ∈ Hs, ∑ g ∈ Rf, (ψ₀.ψ₀ (h / M) : ℂ) * (c h j * D.u j (zpt g)) := by
    intro j
    unfold Bj Uj
    rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro g _
    simp only [hc]; ring
  have hBUs : ∀ 𝔰 r, D.Bs ψ₀ E H X K ψ₁ ψ₂ M 𝔰 r * D.Us R 𝔰 r =
      ∑ h ∈ Hs, ∑ g ∈ Rf, (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g)) := by
    intro 𝔰 r
    unfold Bs Us
    rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro g _
    simp only [hcs]; ring
  have hsum : ∀ h ∈ Hs, ∀ g ∈ Rf, Summable (fun j => (ψ₀.ψ₀ (h / M) : ℂ) *
      (c h j * D.u j (zpt g))) := fun h hh g _ =>
    (Summable.of_norm (hPEh h hh (zpt g)).1).mul_left _
  have hint : ∀ 𝔰, ∀ h ∈ Hs, ∀ g ∈ Rf, Integrable (fun r : ℝ => (ψ₀.ψ₀ (h / M) : ℂ) *
      (cs h 𝔰 r * D.Eis 𝔰 r (zpt g))) := fun 𝔰 h hh g _ =>
    ((hPEh h hh (zpt g)).2.1 𝔰).const_mul _
  refine ⟨?_, ?_⟩
  · -- summability
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (summable_sum fun h hh => summable_sum fun g hg => (hsum h hh g hg).norm)
    rw [hBU]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => norm_sum_le _ _)
  · rw [hXi]
    have hsplit : ∀ h ∈ Hs, ∀ g ∈ Rf, (ψ₀.ψ₀ (h / M) : ℂ) *
        poincare (4 * E * d) (gh E H X K ψ₁ ψ₂ h) h (zpt g) =
        (∑' j, (ψ₀.ψ₀ (h / M) : ℂ) * (c h j * D.u j (zpt g))) +
          (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ,
            (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g)) := by
      intro h hh g _
      rw [(hPEh h hh (zpt g)).2.2, mul_add, tsum_mul_left]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro 𝔰 _
      rw [integral_const_mul]; ring
    rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun g hg => hsplit h hh g hg]
    simp only [Finset.sum_add_distrib]
    congr 1
    · -- the discrete spectrum
      simp_rw [hBU]
      rw [Summable.tsum_finsetSum fun h hh => summable_sum fun g hg => hsum h hh g hg]
      apply Finset.sum_congr rfl; intro h hh
      rw [Summable.tsum_finsetSum fun g hg => hsum h hh g hg]
    · -- the continuous spectrum
      have key : ∑ 𝔰, ∫ r : ℝ, D.Bs ψ₀ E H X K ψ₁ ψ₂ M 𝔰 r * D.Us R 𝔰 r =
          ∑ h ∈ Hs, ∑ g ∈ Rf, ∑ 𝔰, ∫ r : ℝ,
            (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g)) := by
        simp_rw [hBUs]
        calc ∑ 𝔰, ∫ r : ℝ, ∑ h ∈ Hs, ∑ g ∈ Rf,
              (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g))
            = ∑ 𝔰, ∑ h ∈ Hs, ∑ g ∈ Rf, ∫ r : ℝ,
              (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g)) := by
              apply Finset.sum_congr rfl; intro 𝔰 _
              rw [integral_finsetSum _ fun h hh => integrable_finsetSum _ fun g hg =>
                hint 𝔰 h hh g hg]
              apply Finset.sum_congr rfl; intro h hh
              rw [integral_finsetSum _ fun g hg => hint 𝔰 h hh g hg]
          _ = ∑ h ∈ Hs, ∑ g ∈ Rf, ∑ 𝔰, ∫ r : ℝ,
              (ψ₀.ψ₀ (h / M) : ℂ) * (cs h 𝔰 r * D.Eis 𝔰 r (zpt g)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro h _
              rw [Finset.sum_comm]
      rw [key, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro h _
      rw [Finset.mul_sum]

end SpectralData

end Triples
