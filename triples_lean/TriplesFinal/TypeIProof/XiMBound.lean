import TriplesFinal.TypeIProof.SpectralBound
import TriplesFinal.Heegner.Representatives

/-!
# The bound for `Ξ_M`

The spectral expansion of `Ξ_M` (Lemma 10.1) splits it into the discrete and the continuous
spectrum; both are bounded by `spectral_side'` (`discrete_side`, `continuous_side`), and the
bound is simplified by `spectral_rhs_le`:
`|Ξ_M| ≤ 2K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √((1 + M/q) M) √𝒫`.

Paper: §12, equation (12.2).
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups
open SymMat

/-- Enumerating a finite set of symmetric matrices. -/
theorem finsum_mem_eq_sum_enum {R : Set SymMat} (hR : R.Finite) {β : Type*} [AddCommMonoid β]
    (f : SymMat → β) :
    ∑ᶠ g ∈ R, f g = ∑ i : Fin hR.toFinset.card, f (hR.toFinset.equivFin.symm i) := by
  rw [finsum_mem_eq_finite_toFinset_sum f hR, ← Finset.sum_coe_sort hR.toFinset f]
  exact (Equiv.sum_comp hR.toFinset.equivFin.symm (fun x => f x)).symm

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

set_option maxHeartbeats 1000000 in
/-- **The continuous spectrum**: `|(1/4π) ∑_𝔰 ∫ B_𝔰(r) U_𝔰(r) dr|` is bounded by the expression
of `spectral_side'` with `P = 𝒫` the pair count. -/
theorem continuous_side {q : ℕ} (D : SpectralData q) (hq : S.q = q)
    (hEC : D.EisensteinContinuous) {n : ℕ} (z : Fin n → ℍ)
    (hB : BesselAssumptions) {Cls : ℝ → ℝ} (hDI2 : D.LargeSieveDI2 Cls) (hPT : D.PreTrace)
    (hSC : SelbergConvolution) {Eexc : ℝ} (hE0 : 0 ≤ Eexc)
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
    ‖(1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, S.B ψ₀ (fun m => D.ρEis 𝔰 r m) r *
        ∑ i, D.Eis 𝔰 r (z i)‖ ≤
      Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * (pairCountPts q z : ℝ)) +
      Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls C6 CGt 1 S.T₁)) *
        Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * (pairCountPts q z : ℝ)) +
      Real.sqrt (S.Wtail Cls C6 CGt k Ck (pairCountPts q z : ℝ)) *
        (1 - Real.sqrt (1 / 2))⁻¹ := by
  have hLS : (D.contFam hEC z).LS S.q Cls := by rw [hq]; exact D.contFam_LS hEC z hDI2
  have hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in (D.contFam hEC z).exc,
      S.V ^ (2 * ((D.contFam hEC z).t x).im) *
        ‖S.Ssum ψ₀ ((D.contFam hEC z).ρ x) s σ‖ ^ 2 ∂(D.contFam hEC z).ν ≤ Eexc := by
    intro s _ σ
    rw [D.contFam_exc hEC z, Measure.restrict_empty, integral_zero_measure]
    exact hE0
  obtain ⟨hint, hle⟩ := S.spectral_side' ψ₀ (D.contFam hEC z) hB hLS
    (P := (pairCountPts q z : ℝ)) (Nat.cast_nonneg _) (D.contFam_HS hEC z hPT hSC) hE hCψ hψ hCd
    hMd hC6 hM6 hGt hk hCk hMk
  refine le_trans ?_ hle
  rw [D.contFam_integral hEC z hint]
  have hpi := Real.pi_pos
  rw [norm_mul]
  have h4 : ‖(1 / (4 * Real.pi) : ℂ)‖ = 1 / (4 * Real.pi) := by
    rw [show (1 / (4 * Real.pi) : ℂ) = ((1 / (4 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h4]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun 𝔰 _ => ?_)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext r
  rw [norm_mul]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The bound for `Ξ_M`** (equation (12.2), before the optimisation in `M`):
`|Ξ_M| ≤ 2K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √W √𝒫`, with `W = (1 + M/q) M` and `𝒫` the pair count. -/
theorem XiM_le {q : ℕ} (D : SpectralData q) (hq : q = 4 * S.E * S.d)
    (hB : BesselAssumptions) (hSC : SelbergConvolution) (hPE : D.PoincareExpansion)
    (hPT : D.PreTrace) (hEC : D.EisensteinContinuous) {Cls : ℝ → ℝ} (hDI2 : D.LargeSieveDI2 Cls)
    {Λ : Set SymMat} (hΛ : IsOrbitReps ((S.E : ℤ) * S.H) Λ) {T : Set SL(2, ℤ)}
    (hT : IsCosetReps q T) {n : ℕ} (z : Fin n → ℍ)
    (hUj : ∀ j, D.Uj (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) j = ∑ i, D.u j (z i))
    (hUs : ∀ 𝔰 r, D.Us (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) 𝔰 r =
      ∑ i, D.Eis 𝔰 r (z i))
    {Eexc KE 𝔈 : ℝ} (hKE : 0 ≤ KE) (h𝔈 : 1 ≤ 𝔈) (hE0 : 0 ≤ Eexc)
    (hEle : Eexc ≤ KE * (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W))
    (hE : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∫ x in (D.discFam z).exc,
      S.V ^ (2 * ((D.discFam z).t x).im) *
        ‖S.Ssum ψ₀ ((D.discFam z).ρ x) s σ‖ ^ 2 ∂(D.discFam z).ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6' : ℝ} (hC6' : 0 ≤ C6')
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6' * S.L ^ 6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck Ckt : ℝ} (hk : 3 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k))
    (hCk0 : 0 ≤ Ck * S.T₁ ^ (-(k - 3))) (hCkt : Ck * S.T₁ ^ (-(k - 3)) * S.Q ≤ Ckt * S.L ^ 3) :
    ‖XiM ψ₀ S.E S.H S.d S.κ S.X S.K S.ψ₁ S.ψ₂ S.M‖ ≤
      2 * (S.Kspec Cls KE Cψ Cd C6' CGt Ckt * (S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈) *
        Real.sqrt S.W * Real.sqrt (pairCountPts q z : ℝ)) := by
  obtain ⟨_, heq⟩ := D.expansion hPE ψ₀ S.hyp hq hΛ hT S.hM1
  rw [heq]
  have hq' : S.q = q := by unfold Setup.q; rw [hq]
  have hC6 : 0 ≤ C6' * S.L ^ 6 := by have := S.L_pos; positivity
  have hLS : (D.discFam z).LS S.q Cls := by rw [hq']; exact D.discFam_LS z hDI2
  have hCls : 0 ≤ Cls S.η := S.Cls_nonneg (D.discFam z) hLS
  obtain ⟨hs, hdisc⟩ := S.discrete_side ψ₀ D hq' z hB hDI2 hPT hSC hE hCψ hψ hCd hMd hC6 hM6 hGt
    hk hCk hMk
  have hcont := S.continuous_side ψ₀ D hq' hEC z hB hDI2 hPT hSC hE0 hCψ hψ hCd hMd hC6 hM6 hGt
    hk hCk hMk
  have hrhs := S.spectral_rhs_le hCls hKE h𝔈 hEle (Cψ := Cψ) (Cd := Cd) (C6' := C6')
    (CGt := CGt) (P := (pairCountPts q z : ℝ)) (Nat.cast_nonneg _) hCk0 hCkt
  -- the discrete spectrum
  have e1 : ∀ j, D.Bj ψ₀ S.E S.H S.X S.K S.ψ₁ S.ψ₂ S.M j *
      D.Uj (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) j =
      S.B ψ₀ (fun m => D.ρ j m) (D.t j) * ∑ i, D.u j (z i) := fun j => by
    rw [hUj]; rfl
  have h1 : ‖∑' j, D.Bj ψ₀ S.E S.H S.X S.K S.ψ₁ S.ψ₂ S.M j *
      D.Uj (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) j‖ ≤
      ∑' j, ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j)‖ * ‖∑ i, D.u j (z i)‖ := by
    simp only [e1]
    have hs' : Summable fun j => ‖S.B ψ₀ (fun m => D.ρ j m) (D.t j) * ∑ i, D.u j (z i)‖ :=
      hs.congr fun j => (norm_mul _ _).symm
    refine (norm_tsum_le_tsum_norm hs').trans (le_of_eq ?_)
    congr 1
    funext j
    exact norm_mul _ _
  -- the continuous spectrum
  have e2 : (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, D.Bs ψ₀ S.E S.H S.X S.K S.ψ₁ S.ψ₂ S.M 𝔰 r *
      D.Us (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) 𝔰 r =
      (1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, S.B ψ₀ (fun m => D.ρEis 𝔰 r m) r *
        ∑ i, D.Eis 𝔰 r (z i) := by
    congr 1
    apply Finset.sum_congr rfl
    intro 𝔰 _
    congr 1
    funext r
    rw [hUs]
    rfl
  rw [e2]
  set R := Real.sqrt (S.boundJ0 Cls Eexc) * Real.sqrt (256 / Real.pi * (pairCountPts q z : ℝ)) +
    Real.sqrt (3 * (2 * S.boundMain Cls Cψ Cd + S.boundRem Cls (C6' * S.L ^ 6) CGt 1 S.T₁)) *
      Real.sqrt (256 / Real.pi * S.T₁ ^ 2 * (pairCountPts q z : ℝ)) +
    Real.sqrt (S.Wtail Cls (C6' * S.L ^ 6) CGt k Ck (pairCountPts q z : ℝ)) *
      (1 - Real.sqrt (1 / 2))⁻¹ with hR
  calc _ ≤ ‖∑' j, D.Bj ψ₀ S.E S.H S.X S.K S.ψ₁ S.ψ₂ S.M j *
        D.Uj (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) j‖ +
        ‖(1 / (4 * Real.pi) : ℂ) * ∑ 𝔰, ∫ r : ℝ, S.B ψ₀ (fun m => D.ρEis 𝔰 r m) r *
          ∑ i, D.Eis 𝔰 r (z i)‖ := norm_add_le _ _
    _ ≤ R + R := add_le_add (h1.trans hdisc) hcont
    _ ≤ _ := by linarith

end Setup

end Triples
