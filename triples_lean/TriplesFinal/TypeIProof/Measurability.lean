import TriplesFinal.TypeIProof.BlockJ0DI

/-!
# Measurability of the coefficients `B(ρ_t, t)`

`(ν, y) ↦ K_ν(y)` and `t ↦ Ψ_h(t)` are measurable (as parametric integrals of jointly continuous
functions), so `x ↦ B(ρ_x, t_x)` is measurable for every spectral family. This discharges the
hypothesis `hBm` of `spectral_side` (`spectral_side'`).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

/-- `(ν, y) ↦ K_ν(y)` is measurable. -/
theorem measurable_besselK_joint : Measurable (fun p : ℂ × ℝ => besselK p.1 p.2) := by
  have hc : Continuous (fun z : (ℂ × ℝ) × ℝ =>
      Complex.exp (-((z.1.2 * Real.cosh z.2 : ℝ) : ℂ) + z.1.1 * z.2)) := by fun_prop
  have h := hc.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have e : (fun p : ℂ × ℝ => besselK p.1 p.2) = fun p => (1 / 2 : ℂ) *
      ∫ σ : ℝ, Complex.exp (-((p.2 * Real.cosh σ : ℝ) : ℂ) + p.1 * σ) := rfl
  rw [e]
  exact measurable_const.mul h.measurable

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- `t ↦ Ψ_h(t)` is measurable. -/
theorem measurable_PsiH (h : ℝ) :
    Measurable (fun t : ℂ => PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t) := by
  have hg := S.continuous_gMh h
  have hm : Measurable (fun z : ℂ × ℝ => gMh S.ψ₁ S.ψ₂ S.X S.K h z.2 *
      besselK (I * z.1) (2 * Real.pi * h * S.Y * z.2)) :=
    (hg.measurable.comp measurable_snd).mul (measurable_besselK_joint.comp
      ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  have h2 := hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc (1 / 2 : ℝ) 1))
  have e : (fun t : ℂ => PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h t) = fun t =>
      ∫ s in Ioc (1 / 2 : ℝ) 1, gMh S.ψ₁ S.ψ₂ S.X S.K h s *
        besselK (I * t) (2 * Real.pi * h * S.Y * s) := by
    funext t
    unfold PsiH
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [e]
  exact h2.measurable

/-- **`x ↦ B(ρ_x, t_x)` is measurable.** -/
theorem measurable_B_comp : Measurable fun x => S.B ψ₀ (F.ρ x) (F.t x) := by
  have e : (fun x => S.B ψ₀ (F.ρ x) (F.t x)) = fun x => (S.Bk : ℂ) *
      ∑ h ∈ S.Hs, (ψ₀.ψ₀ (h / S.M) : ℂ) * (starRingEnd ℂ) (F.ρ x h) *
        PsiH S.ψ₁ S.ψ₂ S.X S.K S.Y h (F.t x) := by
    funext x; exact S.B_eq ψ₀ (F.ρ x) (F.t x)
  rw [e]
  refine measurable_const.mul (Finset.measurable_sum _ fun h _ => ?_)
  exact (measurable_const.mul (Complex.continuous_conj.measurable.comp (F.meas_ρ h))).mul
    ((S.measurable_PsiH h).comp F.meas_t)

set_option maxHeartbeats 1000000 in
/-- **The spectral side** for a spectral family (`spectral_side` with the measurability of
`B` discharged):
`∫ |B(ρ_t, t)| |U| ≤ √A₀ √(256P/π) + √A₁ √(256 T₁² P/π) + √W / (1 - 1/√2)`. -/
theorem spectral_side' (hB : BesselAssumptions) {Cls : ℝ → ℝ}
    (hLS : F.LS S.q Cls) {P : ℝ} (hP : 0 ≤ P) (hHS : F.HS P) {Eexc : ℝ}
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in F.exc, S.V ^ (2 * (F.t x).im) *
      ‖S.Ssum ψ₀ (F.ρ x) s σ‖ ^ 2 ∂F.ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck : ℝ} (hk : 3 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k)) :
    Integrable (fun x => ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖) F.ν ∧
      ∫ x, ‖S.B ψ₀ (F.ρ x) (F.t x)‖ * ‖F.U x‖ ∂F.ν ≤
        Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * P) +
        Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)) *
          Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * P) +
        Real.sqrt (S.Wtail Cls C6 CGt k Ck P) * (1 - Real.sqrt (1 / 2))⁻¹ :=
  S.spectral_side ψ₀ F hB hLS hP hHS (S.measurable_B_comp ψ₀ F) hE hCψ hψ hCd hMd hC6 hM6 hGt
    hk hCk hMk

end Setup

end Triples
