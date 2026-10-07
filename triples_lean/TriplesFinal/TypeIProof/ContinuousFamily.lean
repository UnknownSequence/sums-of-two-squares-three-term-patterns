import TriplesFinal.TypeIProof.DiscreteSide

/-!
# The continuous spectrum as a spectral family

The Eisenstein series of `SpectralData`, indexed by `(𝔰, r) ∈ κ × ℝ` with the measure
`(1/4π) ∑_𝔰 dr`, form a spectral family (`SpectralData.contFam`), with Heegner sums
`U_𝔰(r) = ∑_i E_𝔰(z_i, 1/2 + ir)`. Its hypotheses follow from Lemma 10.2 (`contFam_LS`) and
Lemma 10.7 (`contFam_HS`); there are no exceptional points. This uses the continuity of the
Eisenstein data (`SpectralData.EisensteinContinuous`).

Paper: §12.5.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane

section CountProd

variable {κ : Type} [Fintype κ] [MeasurableSpace κ] [DiscreteMeasurableSpace κ]

/-- `∫_{κ × S} f d(count ⊗ dr) = ∑_𝔰 ∫_S f(𝔰, r) dr`. -/
theorem integral_count_prod_restrict {f : κ × ℝ → ℝ} {S : Set ℝ}
    (hf : IntegrableOn f (univ ×ˢ S) (Measure.count.prod volume)) :
    ∫ p in univ ×ˢ S, f p ∂(Measure.count.prod volume) = ∑ 𝔰, ∫ r in S, f (𝔰, r) := by
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  rw [← Measure.prod_restrict, Measure.restrict_univ, integral_prod _ hf, integral_count]

/-- `∫_{κ × ℝ} f d(count ⊗ dr) = ∑_𝔰 ∫ f(𝔰, r) dr`. -/
theorem integral_count_prod {f : κ × ℝ → ℝ} (hf : Integrable f (Measure.count.prod volume)) :
    ∫ p, f p ∂(Measure.count.prod volume) = ∑ 𝔰, ∫ r, f (𝔰, r) := by
  rw [integral_prod _ hf, integral_count]

theorem measure_prod_Icc_lt_top (T : ℝ) :
    (Measure.count.prod volume) (univ ×ˢ Icc (-T) T : Set (κ × ℝ)) < ⊤ := by
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 Set.finite_univ) measure_Icc_lt_top

/-- A function continuous in `r` for each `𝔰` is integrable on `κ × [-T, T]`. -/
theorem integrableOn_prod_Icc {g : κ → ℝ → ℝ} (hg : ∀ 𝔰, Continuous (g 𝔰)) (T : ℝ)
    (c : ENNReal) (hc : c ≠ ⊤) :
    IntegrableOn (fun p : κ × ℝ => g p.1 p.2) (univ ×ˢ Icc (-T) T)
      (c • Measure.count.prod volume) := by
  choose B hB using fun 𝔰 => (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (hg 𝔰).continuousOn
  have hm : Measurable fun p : κ × ℝ => g p.1 p.2 :=
    measurable_from_prod_countable_right fun 𝔰 => (hg 𝔰).measurable
  refine IntegrableOn.of_bound ?_ hm.aestronglyMeasurable (∑ 𝔰, |B 𝔰|) ?_
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) (measure_prod_Icc_lt_top T)
  · refine (ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)).2
      (Eventually.of_forall fun p hp => ?_)
    exact (hB p.1 p.2 hp.2).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun 𝔰 => |B 𝔰|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ p.1)))

end CountProd

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

theorem norm_ofReal_le_iff {T r : ℝ} : ‖((r : ℝ) : ℂ)‖ ≤ T ↔ r ∈ Icc (-T) T := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le, mem_Icc]

theorem ball_eq_prod (T : ℝ) :
    {p : D.κ × ℝ | ‖((p.2 : ℝ) : ℂ)‖ ≤ T} = univ ×ˢ Icc (-T) T := by
  ext p
  simp only [Set.mem_ofPred_eq, mem_prod, mem_univ, true_and]
  exact norm_ofReal_le_iff

/-- **The continuous spectrum** as a spectral family: `(𝔰, r) ∈ κ × ℝ`, with the measure
`(1/4π) ∑_𝔰 dr`, `t = r`, `ρ = ρ_𝔰(·, r)` and the Heegner sums `U_𝔰(r) = ∑_i E_𝔰(z_i, 1/2 + ir)`. -/
noncomputable def contFam (hEC : D.EisensteinContinuous) {n : ℕ} (z : Fin n → ℍ) : SpecFam :=
  letI : MeasurableSpace D.κ := ⊤
  { Ω := D.κ × ℝ
    ν := ENNReal.ofReal (1 / (4 * Real.pi)) • (Measure.count.prod volume)
    t := fun p => (p.2 : ℂ)
    ρ := fun p m => D.ρEis p.1 p.2 m
    U := fun p => ∑ i, D.Eis p.1 p.2 (z i)
    meas_t := Complex.measurable_ofReal.comp measurable_snd
    meas_ρ := fun m => measurable_from_prod_countable_right fun 𝔰 => (hEC.1 𝔰 m).measurable
    meas_U := measurable_from_prod_countable_right fun 𝔰 =>
      (continuous_finsetSum _ fun i _ => hEC.2 𝔰 (z i)).measurable
    t_mem := fun p => Or.inl (Complex.ofReal_im _)
    finite_ball := fun T => by
      rw [D.ball_eq_prod T, Measure.smul_apply, smul_eq_mul]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_prod_Icc_lt_top T)).ne
    intρ := fun m T => by
      rw [D.ball_eq_prod T]
      exact integrableOn_prod_Icc (g := fun 𝔰 r => ‖D.ρEis 𝔰 r m‖ ^ 2)
        (fun 𝔰 => ((hEC.1 𝔰 m).norm.pow 2)) T _ ENNReal.ofReal_ne_top
    intU := fun T => by
      rw [D.ball_eq_prod T]
      exact integrableOn_prod_Icc (g := fun 𝔰 r => ‖∑ i, D.Eis 𝔰 r (z i)‖ ^ 2)
        (fun 𝔰 => ((continuous_finsetSum _ fun i _ => hEC.2 𝔰 (z i)).norm.pow 2)) T _
        ENNReal.ofReal_ne_top
    ch_lb := ⟨1, one_pos, fun p => by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_re]
      exact Real.one_le_cosh _⟩ }

end SpectralData

end Triples
