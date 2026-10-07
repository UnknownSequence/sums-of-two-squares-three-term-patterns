import TriplesFinal.TypeIProof.BlockJ0

/-!
# The spectrum `𝒥₀`: the bound for `∫_{‖t‖ ≤ 1} m₀`

Integrating the large sieve bound of `J0_inner` over the box `(s, σ) ∈ (1/2, 1] × (-ℓ, ℓ]`
(Fubini), and bounding the error terms by the large sieve inequality with a single coefficient:
`∫_{‖t‖ ≤ 1} m₀ ≤ 2((X/K)Y^(-1/2))² ((ℓ/4)(2C₀)² ℓ (cosh π · C(η)(1 + M^(1+η)/q) 2M (2C₀)² + E)
  + 2Mε₀² ∑_h cosh π · C(η)(1 + (h/2)^(1+η)/q))`.
The exceptional sums `E` are bounded by Lemma 10.5 (`J0_exc`).

Paper: §12.2.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

namespace SpecFam

variable (F : SpecFam)

/-- On `‖t‖ ≤ T`: `∫ f ≤ cosh(πT) ∫ f / cosh(πt)`. -/
theorem setIntegral_le_cosh_mul {T : ℝ} {f : F.Ω → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f (F.ball T) F.ν) :
    ∫ x in F.ball T, f x ∂F.ν ≤
      Real.cosh (Real.pi * T) * ∫ x in F.ball T, f x / F.ch x ∂F.ν := by
  rw [← integral_const_mul]
  apply setIntegral_mono_on hf ((F.integrableOn_div_ch hf).const_mul _) (F.measurableSet_ball T)
  intro x hx
  have hch := F.ch_pos x
  have hle := F.ch_le hx
  rw [mul_div_assoc', le_div_iff₀ hch]
  exact (mul_le_mul_of_nonneg_left hle (hf0 x)).trans_eq (mul_comm _ _)

end SpecFam

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- `∫_{‖t‖ ≤ 1} |ρ(h)|² ≤ cosh π · C(η)(1 + (h/2)^(1+η)/q)`. -/
theorem ball1_sq_ρ_le {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {h : ℕ} (hh : 1 ≤ h) :
    ∫ x in F.ball 1, ‖F.ρ x h‖ ^ 2 ∂F.ν ≤
      Real.cosh Real.pi * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q)) := by
  have h1 := F.setIntegral_le_cosh_mul (T := 1) (f := fun x => ‖F.ρ x h‖ ^ 2)
    (fun x => sq_nonneg _) (F.intρ h 1)
  rw [mul_one] at h1
  have h2 := S.LS_single F hLS hh (T := 1) le_rfl
  rw [one_pow] at h2
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.cosh_pos _).le)

set_option maxHeartbeats 1000000 in
/-- **The block `𝒥₀`**: integrability and the bound for `∫_{‖t‖ ≤ 1} m₀`. -/
theorem J0_block {Cls : ℝ → ℝ} (hLS : F.LS S.q Cls) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc) :
    IntegrableOn (fun x => S.m0 ψ₀ (F.ρ x) (F.t x)) (F.ball 1) F.ν ∧
    ∫ x in F.ball 1, S.m0 ψ₀ (F.ρ x) (F.t x) ∂F.ν ≤
      2 * S.Bk ^ 2 * (S.ℓ / 4 * (2 * S.C₀) ^ 2 * (S.ℓ *
        (Real.cosh Real.pi * Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) * (2 * S.M * (2 * S.C₀) ^ 2) +
          Eexc)) +
        2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs,
          Real.cosh Real.pi * (Cls S.η * (1 + ((h : ℝ) / 2) ^ (1 + S.η) / S.q))) := by
  classical
  have hℓ := S.ℓ_pos
  set μs : Measure ℝ := volume.restrict (Ioc (1 / 2 : ℝ) 1) with hμs
  set μσ : Measure ℝ := volume.restrict (Ioc (-S.ℓ) S.ℓ) with hμσ
  set μ2 : Measure (ℝ × ℝ) := μs.prod μσ with hμ2
  set ν1 : Measure F.Ω := F.ν.restrict (F.ball 1) with hν1
  have : IsFiniteMeasure ν1 := isFiniteMeasure_restrict.2 (F.finite_ball 1)
  -- a.e. on the box, `s ∈ (1/2, 1]`
  have hbox : ∀ᵐ p ∂μ2, p.1 ∈ Ioc (1 / 2 : ℝ) 1 ∧ p.2 ∈ Ioc (-S.ℓ) S.ℓ := by
    rw [hμ2, hμs, hμσ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact hp
  -- the weight `V^(2|Im t|)`
  have hV1 : 1 ≤ S.V := by linarith [S.V_ge]
  have hw_le : ∀ x, S.V ^ (2 * |(F.t x).im|) ≤ S.V := fun x => by
    calc S.V ^ (2 * |(F.t x).im|) ≤ S.V ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hV1 (by linarith [F.abs_im_le_half x])
      _ = S.V := Real.rpow_one _
  have hw0 : ∀ x, 0 ≤ S.V ^ (2 * |(F.t x).im|) := fun x => by positivity
  have hwm : Measurable fun x => S.V ^ (2 * |(F.t x).im|) := by
    have hm1 : Measurable fun x => |(F.t x).im| :=
      continuous_abs.measurable.comp (Complex.measurable_im.comp F.meas_t)
    exact measurable_const.pow (hm1.const_mul 2)
  -- integrability in `(s, σ)`
  have hgi : ∀ x, Integrable (fun p : ℝ × ℝ => ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2) μ2 := by
    intro x
    refine (integrable_const (2 * S.M * (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2)).mono' ?_ ?_
    · exact ((S.continuous_Ssum ψ₀ (F.ρ x)).norm.pow 2).aestronglyMeasurable
    · filter_upwards [hbox] with p hp
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact S.norm_sq_Ssum_le ψ₀ (F.ρ x) (by linarith [hp.1.1]) p.2
  -- the `(s, σ)`-integral as an integral over the box
  have hI : ∀ x, (∫ s in (1 / 2 : ℝ)..1, ∫ σ in (-S.ℓ)..S.ℓ, ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2) =
      ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 := by
    intro x
    rw [integral_prod _ (hgi x), intervalIntegral.integral_of_le (by norm_num)]
    congr 1
    ext s
    rw [intervalIntegral.integral_of_le (by linarith)]
  -- joint integrability
  have hDi : Integrable (fun x => 2 * S.M * (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) ν1 :=
    (F.integrableOn_sum_sq_ρ S.Hs 1).const_mul _
  have hGi : Integrable (Function.uncurry fun x (p : ℝ × ℝ) =>
      S.V ^ (2 * |(F.t x).im|) * ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2) (ν1.prod μ2) := by
    refine ((hDi.const_mul S.V).comp_fst μ2).mono' ?_ ?_
    · have h1 : Measurable fun z : F.Ω × (ℝ × ℝ) => S.V ^ (2 * |(F.t z.1).im|) :=
        hwm.comp measurable_fst
      have h2 : Measurable fun z : F.Ω × (ℝ × ℝ) => ‖S.Ssum ψ₀ (F.ρ z.1) z.2.1 z.2.2‖ ^ 2 :=
        (S.measurable_Ssum_joint ψ₀ F).norm.pow_const 2
      exact (h1.mul h2).aestronglyMeasurable
    · have hmeas : MeasurableSet {z : F.Ω × (ℝ × ℝ) | z.2.1 ∈ Ioc (1 / 2 : ℝ) 1} :=
        measurableSet_Ioc.preimage (measurable_fst.comp measurable_snd)
      have hae : ∀ᵐ z ∂(ν1.prod μ2), z.2.1 ∈ Ioc (1 / 2 : ℝ) 1 :=
        (Measure.ae_prod_iff_ae_ae hmeas).2 (Eventually.of_forall fun x => by
          filter_upwards [hbox] with p hp
          exact hp.1)
      filter_upwards [hae] with z hz
      show ‖S.V ^ (2 * |(F.t z.1).im|) * ‖S.Ssum ψ₀ (F.ρ z.1) z.2.1 z.2.2‖ ^ 2‖ ≤
        S.V * (2 * S.M * (2 * S.C₀) ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ z.1 h‖ ^ 2)
      rw [Real.norm_of_nonneg (mul_nonneg (hw0 _) (sq_nonneg _))]
      exact mul_le_mul (hw_le _) (S.norm_sq_Ssum_le ψ₀ (F.ρ z.1) (by linarith [hz.1]) z.2.2)
        (sq_nonneg _) (by linarith)
  -- integrability of the first part
  have hint1 : Integrable (fun x => S.V ^ (2 * |(F.t x).im|) *
      ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2) ν1 := by
    refine hGi.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
    show ∫ p, S.V ^ (2 * |(F.t x).im|) * ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 = _
    exact integral_const_mul (S.V ^ (2 * |(F.t x).im|)) _
  -- the bound for the first part (Fubini, then `J0_inner` for each `(s, σ)`)
  have hbound1 : ∫ x, S.V ^ (2 * |(F.t x).im|) *
      ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 ∂ν1 ≤
      S.ℓ * (Real.cosh Real.pi * Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) *
        (2 * S.M * (2 * S.C₀) ^ 2) + Eexc) := by
    have e1 : ∫ x, S.V ^ (2 * |(F.t x).im|) * ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 ∂ν1 =
        ∫ x, ∫ p, S.V ^ (2 * |(F.t x).im|) * ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 ∂ν1 := by
      congr 1; ext x; exact (integral_const_mul _ _).symm
    rw [e1, integral_integral_swap hGi]
    have hR := hGi.integral_prod_right
    have hvol : μ2.real univ = S.ℓ := by
      rw [measureReal_def, ← Set.univ_prod_univ, hμ2, Measure.prod_prod, hμs, hμσ,
        Measure.restrict_apply_univ, Measure.restrict_apply_univ, Real.volume_Ioc,
        Real.volume_Ioc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
        ENNReal.toReal_ofReal (by linarith)]
      ring
    calc ∫ p, ∫ x, S.V ^ (2 * |(F.t x).im|) * ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂ν1 ∂μ2
        ≤ ∫ _p, (Real.cosh Real.pi * Cls S.η * (1 + S.M ^ (1 + S.η) / S.q) *
            (2 * S.M * (2 * S.C₀) ^ 2) + Eexc) ∂μ2 := by
          apply integral_mono_ae hR (integrable_const _)
          filter_upwards [hbox] with p hp
          exact S.J0_inner ψ₀ F hLS hE ⟨hp.1.1.le, hp.1.2⟩ p.2
      _ = _ := by rw [integral_const, smul_eq_mul, hvol]
  -- assembling
  have hint2 : Integrable (fun x => ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) ν1 :=
    F.integrableOn_sum_sq_ρ S.Hs 1
  have hm0 : ∀ x, S.m0 ψ₀ (F.ρ x) (F.t x) = 2 * S.Bk ^ 2 *
      (S.ℓ / 4 * (2 * S.C₀) ^ 2 * (S.V ^ (2 * |(F.t x).im|) *
        ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2) +
      2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ‖F.ρ x h‖ ^ 2) := by
    intro x
    unfold m0
    rw [hI x]
    ring
  have hint : Integrable (fun x => S.m0 ψ₀ (F.ρ x) (F.t x)) ν1 := by
    refine (((hint1.const_mul (S.ℓ / 4 * (2 * S.C₀) ^ 2)).add
      (hint2.const_mul (2 * S.M * S.eps0 ^ 2))).const_mul (2 * S.Bk ^ 2)).congr
      (Eventually.of_forall fun x => ?_)
    exact (hm0 x).symm
  refine ⟨hint, ?_⟩
  have e : ∫ x, S.m0 ψ₀ (F.ρ x) (F.t x) ∂ν1 = 2 * S.Bk ^ 2 *
      (S.ℓ / 4 * (2 * S.C₀) ^ 2 * ∫ x, S.V ^ (2 * |(F.t x).im|) *
        ∫ p, ‖S.Ssum ψ₀ (F.ρ x) p.1 p.2‖ ^ 2 ∂μ2 ∂ν1 +
      2 * S.M * S.eps0 ^ 2 * ∑ h ∈ S.Hs, ∫ x, ‖F.ρ x h‖ ^ 2 ∂ν1) := by
    rw [integral_congr_ae (Eventually.of_forall hm0), integral_const_mul,
      integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul, integral_finsetSum _ (fun h _ =>
        show Integrable (fun x => ‖F.ρ x h‖ ^ 2) ν1 from F.intρ h 1)]
  rw [e]
  have hc1 : 0 ≤ S.ℓ / 4 * (2 * S.C₀) ^ 2 := by positivity
  have hc2 : 0 ≤ 2 * S.M * S.eps0 ^ 2 := by have := S.M_pos; positivity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hbound1 hc1)
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h hh =>
      S.ball1_sq_ρ_le F hLS (S.le_of_mem_Hs hh).1) hc2)

/-- **The exceptional sums on `𝒥₀`**, by Lemma 10.5 with `Y = V`. -/
theorem J0_exc {θ C' : ℝ} (hA : F.ExcA S.q θ S.η C') {CG : ℝ} (hCG : 0 < CG)
    (hG : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∀ k ≤ 3, ∀ y,
      ‖iteratedDeriv k (S.Gfun ψ₀ s σ) y‖ ≤ CG * S.L ^ k) :
    ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
        ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤
      C' * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * (1 + S.V / max S.M S.q) ^ (2 * θ) *
        (1 + S.M / S.q) * S.M := by
  intro s hs σ
  have := hA S.M S.V S.L CG S.hM1 (by linarith [S.V_ge]) S.one_le_L hCG (S.Gfun ψ₀ s σ)
    (S.contDiff_Gfun ψ₀ s σ)
    (fun y hy => ⟨(S.Gfun_support ψ₀ s σ y hy).1.le, (S.Gfun_support ψ₀ s σ y hy).2⟩)
    (hG s hs σ)
  simpa only [Setup.Ssum, Setup.Hs] using this

end Setup

end Triples
