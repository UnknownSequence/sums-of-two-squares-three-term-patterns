import TriplesFinal.TypeIProof.Measurability
import TriplesFinal.Spectral.Smooth
import TriplesFinal.Spectral.HeegnerSide

/-!
# The discrete spectrum as a spectral family

The Maass cusp forms of `SpectralData`, with the counting measure, form a spectral family
(`SpectralData.discFam`), with Heegner sums `U_j = ∑_i u_j(z_i)`. Its hypotheses follow from the
assumptions: the large sieve inequality from Lemma 10.2 (`discFam_LS`), the Heegner side from
Lemma 10.7 (`discFam_HS`), the exceptional large sieve from Lemma 10.3 (`discFam_ExcB`) and from
Lemma 10.5 (`discFam_ExcA`).

Paper: §12 (the sums over `j`).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane

section CountMeasure

variable {ι : Type*} [MeasurableSpace ι] [DiscreteMeasurableSpace ι]

theorem integrableOn_count_of_finite {s : Set ι} (hs : s.Finite) (f : ι → ℝ) :
    IntegrableOn f s Measure.count := by
  refine IntegrableOn.of_bound (Measure.count_apply_lt_top.2 hs)
    Measurable.of_discrete.aestronglyMeasurable (∑ y ∈ hs.toFinset, ‖f y‖) ?_
  refine (ae_restrict_iff' hs.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
  exact Finset.single_le_sum (f := fun y => ‖f y‖) (fun y _ => norm_nonneg _)
    (hs.mem_toFinset.2 hx)

/-- On a finite set, the integral for the counting measure is the finite sum. -/
theorem setIntegral_count_eq_finsum {s : Set ι} (hs : s.Finite) (f : ι → ℝ) :
    ∫ x in s, f x ∂Measure.count = ∑ᶠ x ∈ s, f x := by
  have hi : IntegrableOn f (hs.toFinset : Set ι) Measure.count := by
    rw [hs.coe_toFinset]; exact integrableOn_count_of_finite hs f
  have h := setIntegral_finset (μ := Measure.count) hs.toFinset hi
  rw [hs.coe_toFinset] at h
  rw [h, finsum_mem_eq_finite_toFinset_sum f hs]
  apply Finset.sum_congr rfl
  intro x _
  rw [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]

end CountMeasure

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

theorem im_eq_zero_of_not_exceptional {j : D.ι} (hj : ¬ D.IsExceptional j) : (D.t j).im = 0 := by
  rcases D.t_mem j with h | h
  · exact h.1
  · exact absurd h.2.1 hj

theorem one_le_cosh_re {j : D.ι} (h : (D.t j).im = 0) :
    1 ≤ (Complex.cosh (Real.pi * D.t j)).re := by
  have ht : D.t j = ((D.t j).re : ℂ) := by apply Complex.ext <;> simp [h]
  rw [ht, ← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_re]
  exact Real.one_le_cosh _

/-- `cosh(π t_j) ≥ c > 0` uniformly in `j` (there are finitely many exceptional `j`). -/
theorem exists_cosh_lb : ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ (Complex.cosh (Real.pi * D.t j)).re := by
  set f : D.ι → ℝ := fun j => (Complex.cosh (Real.pi * D.t j)).re with hf
  by_cases hne : {j | D.IsExceptional j}.Nonempty
  · obtain ⟨j₀, _, hmin⟩ := Set.exists_min_image _ f D.finite_exceptional hne
    refine ⟨min 1 (f j₀), lt_min one_pos (D.cosh_re_pos j₀), fun j => ?_⟩
    by_cases hj : D.IsExceptional j
    · exact (min_le_right _ _).trans (hmin j hj)
    · exact (min_le_left _ _).trans (D.one_le_cosh_re (D.im_eq_zero_of_not_exceptional hj))
  · refine ⟨1, one_pos, fun j => ?_⟩
    have hj : ¬ D.IsExceptional j := fun h => hne ⟨j, h⟩
    exact D.one_le_cosh_re (D.im_eq_zero_of_not_exceptional hj)

/-- **The discrete spectrum** as a spectral family (counting measure), with the Heegner sums
`U_j = ∑_i u_j(z_i)`. -/
noncomputable def discFam {n : ℕ} (z : Fin n → ℍ) : SpecFam :=
  letI : MeasurableSpace D.ι := ⊤
  { Ω := D.ι
    ν := Measure.count
    t := D.t
    ρ := fun j m => D.ρ j m
    U := fun j => ∑ i, D.u j (z i)
    meas_t := Measurable.of_discrete
    meas_ρ := fun _ => Measurable.of_discrete
    meas_U := Measurable.of_discrete
    t_mem := fun j => by
      rcases D.t_mem j with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    finite_ball := fun T => (Measure.count_apply_lt_top.2 (D.finite_le T)).ne
    intρ := fun _ T => integrableOn_count_of_finite (D.finite_le T) _
    intU := fun T => integrableOn_count_of_finite (D.finite_le T) _
    ch_lb := D.exists_cosh_lb }

variable {n : ℕ} (z : Fin n → ℍ)

theorem discFam_exc : (D.discFam z).exc = {j | D.IsExceptional j} := rfl

/-- **Lemma 10.2 for the discrete family.** -/
theorem discFam_LS {C : ℝ → ℝ} (hLS : D.LargeSieveDI2 C) : (D.discFam z).LS q C := by
  let _ : MeasurableSpace D.ι := ⊤
  intro η hη T hT M hM a ha
  have h := hLS η hη T hT M hM a ha
  have hcont : 0 ≤ ∑ 𝔰, ∫ r in Set.Icc (-T) T,
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρEis 𝔰 r m‖ ^ 2 / Real.cosh (Real.pi * r) :=
    Finset.sum_nonneg fun 𝔰 _ =>
      integral_nonneg fun r => div_nonneg (sq_nonneg _) (Real.cosh_pos _).le
  show ∫ x in {x | ‖D.t x‖ ≤ T}, ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρ x m‖ ^ 2 /
      (Complex.cosh (Real.pi * D.t x)).re ∂Measure.count ≤ _
  rw [setIntegral_count_eq_finsum (D.finite_le T)]
  linarith

/-- **Lemma 10.7 for the discrete family.** -/
theorem discFam_HS (hPT : D.PreTrace) (hSC : SelbergConvolution) :
    (D.discFam z).HS (pairCountPts q z) := by
  let _ : MeasurableSpace D.ι := ⊤
  intro T hT
  have h := D.heegner_side hPT hSC hT z
  have hcont : 0 ≤ 1 / (4 * Real.pi) * ∑ 𝔰, ∫ r in Set.Icc (-T) T,
      ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun 𝔰 _ =>
      integral_nonneg fun r => sq_nonneg _)
  show ∫ x in {x | ‖D.t x‖ ≤ T}, ‖∑ i, D.u x (z i)‖ ^ 2 ∂Measure.count ≤ _
  rw [setIntegral_count_eq_finsum (D.finite_le T)]
  set A := {j | (D.t j).im = 0 ∧ (D.t j).re ≤ T} with hA
  set B := {j | D.IsExceptional j} with hB
  have hball : {x | ‖D.t x‖ ≤ T} = A ∪ B := by
    ext j
    simp only [hA, hB, mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hj
      by_cases he : D.IsExceptional j
      · exact Or.inr he
      · left
        have him := D.im_eq_zero_of_not_exceptional he
        refine ⟨him, ?_⟩
        have : ‖D.t j‖ = |(D.t j).re| := by
          rw [show D.t j = ((D.t j).re : ℂ) by apply Complex.ext <;> simp [him],
            Complex.norm_real, Real.norm_eq_abs]
          simp
        linarith [le_abs_self (D.t j).re]
    · rintro (⟨him, hre⟩ | he)
      · have hre0 : 0 ≤ (D.t j).re := by
          rcases D.t_mem j with h' | h'
          · exact h'.2
          · rw [h'.1]
        have : ‖D.t j‖ = (D.t j).re := by
          rw [show D.t j = ((D.t j).re : ℂ) by apply Complex.ext <;> simp [him],
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0]
          simp
        linarith
      · exact (D.norm_t_le_one he).trans hT
  have hAf : A.Finite := (D.finite_le T).subset (by rw [hball]; exact subset_union_left)
  have hBf : B.Finite := D.finite_exceptional
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro j hjA hjB
    have : 0 < (D.t j).im := hjB
    rw [hjA.1] at this
    exact lt_irrefl _ this
  rw [hball, finsum_mem_union hdisj hAf hBf]
  linarith

/-- **Lemma 10.3 for the discrete family.** -/
theorem discFam_ExcB {C : ℝ → ℝ} (hDI5 : D.LargeSieveDI5 C) {η : ℝ} (hη : 0 < η) :
    (D.discFam z).ExcB q η (C η) := by
  let _ : MeasurableSpace D.ι := ⊤
  intro M hM Y hY1 hY2 a ha
  have h := hDI5 η hη M hM Y hY1 hY2 a ha
  show ∫ x in {j | D.IsExceptional j}, Y ^ (2 * (D.t x).im) *
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, a m * D.ρ x m‖ ^ 2 ∂Measure.count ≤ _
  rw [setIntegral_count_eq_finsum D.finite_exceptional]
  exact h

/-- **Lemma 10.5 for the discrete family.** -/
theorem discFam_ExcA {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (C : ℝ → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ C' : ℝ, ∀ (q : ℕ) (D : SpectralData q), 0 < q → D.LargeSieveDI2 C →
      D.LargeSievePascadi C → D.ExceptionalBound θ →
      ∀ {n : ℕ} (z : Fin n → ℍ), (D.discFam z).ExcA q θ η C' := by
  obtain ⟨C', hC'⟩ := smooth_weights hθ0 hθ C hη
  refine ⟨C', fun q D hq hDI2 hPas hEB n z => ?_⟩
  let _ : MeasurableSpace D.ι := ⊤
  intro M Y LG CG hM hY hL hCG G hG hs hd
  have h := hC' q D hq hDI2 hPas hEB M Y LG CG hM hY hL hCG G hG hs hd
  show ∫ x in {j | D.IsExceptional j}, Y ^ (2 * (D.t x).im) *
      ‖∑ m ∈ Finset.Icc 1 ⌊2 * M⌋₊, G (m / M) * D.ρ x m‖ ^ 2 ∂Measure.count ≤ _
  rw [setIntegral_count_eq_finsum D.finite_exceptional]
  exact h

theorem discFam_ExcBound {θ : ℝ} (hEB : D.ExceptionalBound θ) :
    (D.discFam z).ExcBound θ :=
  fun j hj => hEB j hj

end SpectralData

end Triples
