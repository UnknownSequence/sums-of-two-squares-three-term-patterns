import TriplesFinal.Poisson.FourierBump
import TriplesFinal.Analysis.DerivBounds
import TriplesFinal.Analysis.FourierDecay
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Lemma 11.3: the Mellin transforms `M_h(w)`

With `w₁(s) = s^(-1/2) ψ₁(1/s)`, `a_h(s) = ψ̂₂(hXs/K)` and
`M_h(w) = ∫_{1/2}^{1} w₁(s) a_h(s) s^(-w) ds`: let `h > 0` with `hX/K ≤ 4(qX)^η`. Then
`‖(w₁ a_h)^(k)‖_∞ ≪_k L^k` on `[1/2, 1]`; for `Re w ≤ 0`, `|M_h(w)| ≪_k L^k (1 + |w|)^(-k)`;
and for `Re w = 0`, `|∂_h M_h(w)| ≪ X/K`. Here `L = Δ + 8(qX)^η`.

Proof.
* `|ψ̂₂^(i)| ≤ (2π)^i ‖ψ₂‖₁ ≤ (2π)^i 2C₀` (`norm_iteratedDeriv_fourier_le`, from
  `Real.iteratedDeriv_fourier`), so `|a_h^(i)| ≤ (hX/K)^i (2π)^i 2C₀`.
* `w₁ = s^(-1/2) · (ψ₁ ∘ inv)`: the derivatives of `s^(-1/2)` and of `1/s` are bounded on
  `[1/2, 1]` (compactness), and Faà di Bruno gives `|(ψ₁ ∘ inv)^(j)| ≪_j Δ^j`; by Leibniz,
  `|w₁^(j)| ≪_j Δ^j` (`exists_bound_w1`) and `|(w₁a_h)^(k)| ≪_k L^k` (`exists_bound_gMh`), since
  `Δ ≤ L` and `hX/K ≤ L`.
* `g = w₁a_h` is smooth on `ℝ` and supported in `[1/2, 1]`, so all its derivatives vanish at
  `1/2` and `1`. Integrating by parts `k` times (`integral_parts`),
  `M_h(w) = (-1)^k ∏_{i=1}^k (i - w)^(-1) ∫ g^(k)(s) s^(k-w) ds`, with `|i - w| ≥ (1 + |w|)/2`
  for `Re w ≤ 0` and `|s^(k-w)| ≤ 1`.
* `∂_h M_h(w) = ∫ w₁(s) (Xs/K) ψ̂₂'(hXs/K) s^(-w) ds` by differentiation under the integral sign
  (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).

Paper: §11, Lemma 11.3.
-/

namespace Triples

open MeasureTheory Complex
open scoped ContDiff FourierTransform Nat

/-- `w₁(s) = s^(-1/2) ψ₁(1/s)`. -/
noncomputable def w1 (ψ₁ : ℝ → ℂ) (s : ℝ) : ℂ := ((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ₁ (1 / s)

/-- `a_h(s) = ψ̂₂(hXs/K)`. -/
noncomputable def ah (ψ₂ : ℝ → ℂ) (X K h s : ℝ) : ℂ := fourier ψ₂ (h * X * s / K)

/-- `M_h(w) = ∫_{1/2}^{1} w₁(s) a_h(s) s^(-w) ds`. -/
noncomputable def Mh (ψ₁ ψ₂ : ℝ → ℂ) (X K h : ℝ) (w : ℂ) : ℂ :=
  ∫ s in (1 / 2 : ℝ)..1, w1 ψ₁ s * ah ψ₂ X K h s * (s : ℂ) ^ (-w)

/-- Iterated derivatives of a function smooth on an open set are bounded on compact subsets. -/
theorem exists_bound_iteratedDeriv_on {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f U) (i : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ s ∈ S, ‖iteratedDeriv i f s‖ ≤ a := by
  have hc : ContinuousOn (iteratedDerivWithin i f U) U :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) hU.uniqueDiffOn
  obtain ⟨a, ha⟩ := hS.exists_bound_of_continuousOn (hc.mono hSU)
  refine ⟨max a 0, le_max_right _ _, fun s hs => ?_⟩
  rw [← iteratedDerivWithin_of_isOpen hU (hSU hs)]
  exact (ha s hs).trans (le_max_left _ _)

/-- Uniform version for the first `n + 1` derivatives. -/
theorem exists_bound_iteratedDeriv_on_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {f : ℝ → F} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ i ≤ n, ∀ s ∈ S, ‖iteratedDeriv i f s‖ ≤ a := by
  choose a ha0 ha using fun i => exists_bound_iteratedDeriv_on hU hS hSU hf i
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), a i, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (n + 1)) => ha0 i)
    linarith
  · intro i hi s hs
    have h1 : a i ≤ ∑ i ∈ Finset.range (n + 1), a i :=
      Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_range.2 (by omega))
    linarith [ha i s hs]

/-! ### The derivatives of `ψ̂₂` -/

section FourierDeriv

variable {ψ : ℝ → ℂ}

theorem integrable_pow_smul_of_support (hψ : Continuous ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1)
    (n : ℕ) : Integrable (fun x : ℝ => x ^ n • ψ x) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro t ht
  by_cases h : ψ t = 0
  · simp [h]
  · exact absurd (Set.mem_Icc.2 (hs t h)) ht

theorem contDiff_fourier_of_support (hψ : Continuous ψ)
    (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) : ContDiff ℝ ∞ (𝓕 ψ) := by
  apply Real.contDiff_fourier (N := ⊤)
  intro n _
  have := (integrable_pow_smul_of_support hψ hs n).norm
  refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp

/-- `|ψ̂^(i)(ξ)| ≤ (2π)^i 2B` for `ψ` supported in `[-1, 1]` with `|ψ| ≤ B`. -/
theorem norm_iteratedDeriv_fourier_le (hψ : Continuous ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1)
    {B : ℝ} (hB : ∀ t, ‖ψ t‖ ≤ B) (i : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv i (𝓕 ψ) ξ‖ ≤ (2 * Real.pi) ^ i * B * 2 := by
  rw [Real.iteratedDeriv_fourier (N := ⊤) (fun n _ => integrable_pow_smul_of_support hψ hs n)
    (by exact_mod_cast le_top)]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans ?_
  have hsupp : ∀ v : ℝ, (-2 * Real.pi * I * (v : ℂ)) ^ i • ψ v ≠ 0 → -1 ≤ v ∧ v ≤ 1 := by
    intro v hv
    apply hs v
    intro h
    apply hv
    rw [h, smul_zero]
  have hM : ∀ v : ℝ, ‖(-2 * Real.pi * I * (v : ℂ)) ^ i • ψ v‖ ≤ (2 * Real.pi) ^ i * B := by
    intro v
    by_cases hv : ψ v = 0
    · rw [hv, smul_zero, norm_zero]
      have := (norm_nonneg (ψ v)).trans (hB v)
      positivity
    · obtain ⟨h1, h2⟩ := hs v hv
      rw [norm_smul, norm_pow]
      have hn : ‖(-2 * Real.pi * I * (v : ℂ))‖ ≤ 2 * Real.pi := by
        have : |v| ≤ 1 := abs_le.2 ⟨h1, h2⟩
        have e : ‖(-2 * Real.pi * I * (v : ℂ))‖ = 2 * Real.pi * |v| := by
          simp [abs_of_pos Real.pi_pos]
        rw [e]; nlinarith [Real.pi_pos]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hn i) (hB v) (norm_nonneg _)
        (by positivity)
  have := integral_norm_le_of_support (by norm_num) hsupp hM
  calc _ ≤ (2 * Real.pi) ^ i * B * (1 - (-1)) := this
    _ = (2 * Real.pi) ^ i * B * 2 := by ring

end FourierDeriv

/-! ### Derivatives of `a_h` and `w₁` -/

theorem ah_eq (ψ₂ : ℝ → ℂ) (X K h : ℝ) :
    (fun s => ah ψ₂ X K h s) = fun s => 𝓕 ψ₂ ((h * X / K) * s) := by
  ext s
  unfold ah
  rw [fourier_eq_fourierIntegral, show h * X * s / K = h * X / K * s by ring]

/-- `|a_h^(i)(s)| ≤ |hX/K|^i (2π)^i 2B`. -/
theorem norm_iteratedDeriv_ah_le {ψ₂ : ℝ → ℂ} (hψ : Continuous ψ₂)
    (hs : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {B : ℝ} (hB : ∀ t, ‖ψ₂ t‖ ≤ B) (X K h : ℝ) (i : ℕ)
    (s : ℝ) :
    ‖iteratedDeriv i (fun s => ah ψ₂ X K h s) s‖ ≤ |h * X / K| ^ i * ((2 * Real.pi) ^ i * B * 2) := by
  rw [ah_eq, iteratedDeriv_comp_const_smul ((contDiff_fourier_of_support hψ hs).of_le
    (by exact_mod_cast le_top)), norm_smul, norm_pow, Real.norm_eq_abs]
  gcongr
  exact norm_iteratedDeriv_fourier_le hψ hs hB i _

theorem contDiff_ah {ψ₂ : ℝ → ℂ} (hψ : Continuous ψ₂) (hs : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1)
    (X K h : ℝ) : ContDiff ℝ ∞ (fun s => ah ψ₂ X K h s) := by
  rw [ah_eq]
  exact (contDiff_fourier_of_support hψ hs).comp (contDiff_const.mul contDiff_id)

/-- `s ↦ s^(-1/2)` as a complex function. -/
theorem contDiffOn_rpow_neg_half :
    ContDiffOn ℝ ∞ (fun s : ℝ => (((s ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) (Set.Ioi 0) := by
  intro s hs
  have : ContDiffAt ℝ ∞ (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) s :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hs)
  exact (ofRealCLM.contDiff.contDiffAt.comp s this).contDiffWithinAt

theorem contDiffOn_inv_Ioi : ContDiffOn ℝ ∞ (fun s : ℝ => s⁻¹) (Set.Ioi 0) :=
  fun _ hs => (contDiffAt_inv ℝ (ne_of_gt hs)).contDiffWithinAt

theorem w1_eq (ψ₁ : ℝ → ℂ) : w1 ψ₁ = fun s => (((s ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) *
    (ψ₁ ∘ (fun s : ℝ => s⁻¹)) s := by
  ext s
  simp [w1, one_div]

theorem contDiffOn_w1 {ψ₁ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ₁) :
    ContDiffOn ℝ ∞ (w1 ψ₁) (Set.Ioi 0) := by
  rw [w1_eq]
  exact contDiffOn_rpow_neg_half.mul (hψ.comp_contDiffOn contDiffOn_inv_Ioi)

/-- **Derivative bound for `w₁`** on `[1/2, 1]`: `|w₁^(j)| ≤ A Δ^j`. -/
theorem exists_bound_w1 (Cν : ℕ → ℝ) (j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Δ : ℝ) (ψ₁ : ℝ → ℂ), 1 ≤ Δ → ContDiff ℝ ∞ ψ₁ →
      (∀ ν t, ‖iteratedDeriv ν ψ₁ t‖ ≤ Cν ν * Δ ^ ν) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, ‖iteratedDeriv j (w1 ψ₁) s‖ ≤ A * Δ ^ j := by
  have hS : Set.Icc (1 / 2 : ℝ) 1 ⊆ Set.Ioi 0 := fun _ hs => by
    simp only [Set.mem_Icc] at hs; simp only [Set.mem_Ioi]; linarith
  obtain ⟨a, ha1, ha⟩ := exists_bound_iteratedDeriv_on_le isOpen_Ioi isCompact_Icc hS
    contDiffOn_rpow_neg_half j
  obtain ⟨D, hD1, hD⟩ := exists_bound_iteratedDeriv_on_le isOpen_Ioi isCompact_Icc hS
    contDiffOn_inv_Ioi j
  set S : ℝ := ∑ l ∈ Finset.range (j + 1), |Cν l| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun l _ => abs_nonneg _)
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a * ((j - i) ! * S * D ^ (j - i)),
    by positivity, ?_⟩
  intro Δ ψ₁ hΔ hψ hCν s hs
  have hs0 : s ∈ Set.Ioi (0 : ℝ) := hS hs
  rw [w1_eq]
  have hL := norm_iteratedDeriv_mul_le_of_isOpen isOpen_Ioi contDiffOn_rpow_neg_half
    (hψ.comp_contDiffOn contDiffOn_inv_Ioi) hs0 j
  refine hL.trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := ha i hi' s hs
  -- Faà di Bruno for `ψ₁ ∘ inv`
  have h2 : ‖iteratedDeriv (j - i) (ψ₁ ∘ fun s : ℝ => s⁻¹) s‖ ≤
      (j - i) ! * (S * Δ ^ (j - i)) * D ^ (j - i) := by
    apply norm_iteratedDeriv_comp_le_of_isOpen isOpen_Ioi isOpen_univ hψ.contDiffOn
      contDiffOn_inv_Ioi (Set.mapsTo_univ _ _) hs0
    · intro l hl
      calc ‖iteratedDeriv l ψ₁ s⁻¹‖ ≤ Cν l * Δ ^ l := hCν l _
        _ ≤ |Cν l| * Δ ^ (j - i) := by
            have h3 : Δ ^ l ≤ Δ ^ (j - i) := pow_le_pow_right₀ hΔ hl
            have h4 : Cν l ≤ |Cν l| := le_abs_self _
            have h5 : 0 ≤ Δ ^ l := by positivity
            calc Cν l * Δ ^ l ≤ |Cν l| * Δ ^ l := by gcongr
              _ ≤ |Cν l| * Δ ^ (j - i) := by gcongr
        _ ≤ S * Δ ^ (j - i) := by
            gcongr
            exact Finset.single_le_sum (f := fun l => |Cν l|) (fun l _ => abs_nonneg _)
              (Finset.mem_range.2 (by omega))
    · intro l hl1 hl2
      calc ‖iteratedDeriv l (fun s : ℝ => s⁻¹) s‖ ≤ D := hD l (by omega) s hs
        _ = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ l := pow_le_pow_right₀ hD1 hl1
  have hΔi : Δ ^ (j - i) ≤ Δ ^ j := pow_le_pow_right₀ hΔ (by omega)
  calc (j.choose i : ℝ) * ‖iteratedDeriv i (fun s : ℝ => (((s ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) s‖ *
        ‖iteratedDeriv (j - i) (ψ₁ ∘ fun s : ℝ => s⁻¹) s‖
      ≤ (j.choose i : ℝ) * a * ((j - i) ! * (S * Δ ^ (j - i)) * D ^ (j - i)) := by
        gcongr
    _ ≤ (j.choose i : ℝ) * a * ((j - i) ! * (S * Δ ^ j) * D ^ (j - i)) := by
        gcongr
    _ = (j.choose i : ℝ) * a * ((j - i) ! * S * D ^ (j - i)) * Δ ^ j := by ring

/-! ### The function `g = w₁ a_h` -/

/-- `g = w₁ a_h`. -/
noncomputable def gMh (ψ₁ ψ₂ : ℝ → ℂ) (X K h : ℝ) (s : ℝ) : ℂ := w1 ψ₁ s * ah ψ₂ X K h s

theorem w1_support {ψ₁ : ℝ → ℂ} (hs : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) {s : ℝ}
    (h : w1 ψ₁ s ≠ 0) : 1 / 2 ≤ s ∧ s ≤ 1 := by
  have hψ : ψ₁ (1 / s) ≠ 0 := fun h' => h (by rw [w1, h', mul_zero])
  obtain ⟨h1, h2⟩ := hs _ hψ
  have hs0 : 0 < s := by
    by_contra hs0
    push Not at hs0
    have : 1 / s ≤ 0 := by
      rcases eq_or_lt_of_le hs0 with h0 | h0
      · rw [h0]; simp
      · exact (div_neg_of_pos_of_neg one_pos h0).le
    linarith
  constructor
  · rw [div_le_iff₀ hs0] at h2; linarith
  · rw [le_div_iff₀ hs0] at h1; linarith

theorem gMh_support {ψ₁ ψ₂ : ℝ → ℂ} (hs : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (X K h : ℝ) {s : ℝ}
    (h' : gMh ψ₁ ψ₂ X K h s ≠ 0) : 1 / 2 ≤ s ∧ s ≤ 1 :=
  w1_support hs (left_ne_zero_of_mul h')

theorem contDiff_gMh {ψ₁ ψ₂ : ℝ → ℂ} (hψ₁ : ContDiff ℝ ∞ ψ₁)
    (hs₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2) (hψ₂ : Continuous ψ₂)
    (hs₂ : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) (X K h : ℝ) :
    ContDiff ℝ ∞ (gMh ψ₁ ψ₂ X K h) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s ∈ tsupport (gMh ψ₁ ψ₂ X K h)
  · have hs' := tsupport_subset_Icc_of_support (fun u hu => gMh_support hs₁ X K h hu) hs
    have hs0 : (0 : ℝ) < s := by linarith [hs'.1]
    have h1 : ContDiffAt ℝ ∞ (w1 ψ₁) s :=
      (contDiffOn_w1 hψ₁).contDiffAt (isOpen_Ioi.mem_nhds hs0)
    exact h1.mul (contDiff_ah hψ₂ hs₂ X K h).contDiffAt
  · have h : gMh ψ₁ ψ₂ X K h =ᶠ[nhds s] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hs
    exact contDiffAt_const.congr_of_eventuallyEq h

/-- **Derivative bound for `w₁ a_h`** on `[1/2, 1]`: `|(w₁a_h)^(k)| ≤ A L^k` when `Δ ≤ L` and
`|hX/K| ≤ L`. -/
theorem exists_bound_gMh (Cν : ℕ → ℝ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Δ X K h L : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), 1 ≤ Δ → ContDiff ℝ ∞ ψ₁ →
      Continuous ψ₂ → (∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) →
      (∀ ν t, ‖iteratedDeriv ν ψ₁ t‖ ≤ Cν ν * Δ ^ ν) → (∀ t, ‖ψ₂ t‖ ≤ Cν 0) →
      Δ ≤ L → |h * X / K| ≤ L →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, ‖iteratedDeriv k (gMh ψ₁ ψ₂ X K h) s‖ ≤ A * L ^ k := by
  choose A hA0 hA using fun j => exists_bound_w1 Cν j
  refine ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A j *
      ((2 * Real.pi) ^ (k - j) * |Cν 0| * 2),
    Finset.sum_nonneg (fun j _ => by have := hA0 j; positivity), ?_⟩
  intro Δ X K h L ψ₁ ψ₂ hΔ hψ₁ hψ₂ hs₂ hC₁ hC₂ hΔL hcL s hs
  have hs0 : s ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Icc] at hs; simp only [Set.mem_Ioi]; linarith
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) hcL
  have hB : ∀ t, ‖ψ₂ t‖ ≤ |Cν 0| := fun t => (hC₂ t).trans (le_abs_self _)
  have hL := norm_iteratedDeriv_mul_le_of_isOpen isOpen_Ioi (contDiffOn_w1 hψ₁)
    (contDiff_ah hψ₂ hs₂ X K h).contDiffOn hs0 k
  refine (le_of_eq_of_le rfl hL).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have h1 := hA j Δ ψ₁ hΔ hψ₁ hC₁ s hs
  have h2 := norm_iteratedDeriv_ah_le hψ₂ hs₂ hB X K h (k - j) s
  have hΔj : Δ ^ j ≤ L ^ j := pow_le_pow_left₀ (by linarith) hΔL j
  have hcj : |h * X / K| ^ (k - j) ≤ L ^ (k - j) := pow_le_pow_left₀ (abs_nonneg _) hcL _
  have hLk : L ^ j * L ^ (k - j) = L ^ k := by rw [← pow_add]; congr 1; omega
  have hA0' := hA0 j
  calc (k.choose j : ℝ) * ‖iteratedDeriv j (w1 ψ₁) s‖ *
        ‖iteratedDeriv (k - j) (fun s => ah ψ₂ X K h s) s‖
      ≤ (k.choose j : ℝ) * (A j * Δ ^ j) *
        (|h * X / K| ^ (k - j) * ((2 * Real.pi) ^ (k - j) * |Cν 0| * 2)) := by gcongr
    _ ≤ (k.choose j : ℝ) * (A j * L ^ j) *
        (L ^ (k - j) * ((2 * Real.pi) ^ (k - j) * |Cν 0| * 2)) := by gcongr
    _ = (k.choose j : ℝ) * A j * ((2 * Real.pi) ^ (k - j) * |Cν 0| * 2) *
        (L ^ j * L ^ (k - j)) := by ring
    _ = _ := by rw [hLk]

/-! ### Integration by parts -/

open Filter Topology in
/-- A smooth function supported in `[a, b]` has all derivatives `0` at `a` and `b`. -/
theorem iteratedDeriv_eq_zero_at_endpoints {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {a b : ℝ}
    (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) (j : ℕ) :
    iteratedDeriv j g a = 0 ∧ iteratedDeriv j g b = 0 := by
  have hc : Continuous (iteratedDeriv j g) := hg.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hzero : ∀ s, s ∉ Set.Icc a b → iteratedDeriv j g s = 0 := fun s hs =>
    iteratedDeriv_eq_zero_of_notMem_tsupport
      (fun h => hs (tsupport_subset_Icc_of_support hsupp h)) j
  constructor
  · have h1 : Tendsto (iteratedDeriv j g) (𝓝[<] a) (𝓝 (iteratedDeriv j g a)) :=
      (hc.tendsto a).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (iteratedDeriv j g) (𝓝[<] a) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hzero s (fun h => absurd h.1 (not_le.2 hs))).symm
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (iteratedDeriv j g) (𝓝[>] b) (𝓝 (iteratedDeriv j g b)) :=
      (hc.tendsto b).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (iteratedDeriv j g) (𝓝[>] b) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hzero s (fun h => absurd h.2 (not_le.2 hs))).symm
    exact tendsto_nhds_unique h1 h2

theorem continuousOn_cpow_Icc (r : ℂ) :
    ContinuousOn (fun s : ℝ => (s : ℂ) ^ r) (Set.Icc (1 / 2 : ℝ) 1) := by
  intro s hs
  have hs0 : (0 : ℝ) < s := by simp only [Set.mem_Icc] at hs; linarith
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.cpow continuous_ofReal.continuousAt continuousAt_const
  simp [Complex.slitPlane, hs0]

/-- One integration by parts: `∫ g^(j) s^(j-w) = -(j+1-w)⁻¹ ∫ g^(j+1) s^(j+1-w)` over
`[1/2, 1]`, for `g` smooth and supported in `[1/2, 1]` and `Re w ≤ 0`. -/
theorem integral_parts_step {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hsupp : ∀ s, g s ≠ 0 → 1 / 2 ≤ s ∧ s ≤ 1) {w : ℂ} (hw : w.re ≤ 0) (j : ℕ) :
    ∫ s in (1 / 2 : ℝ)..1, iteratedDeriv j g s * (s : ℂ) ^ ((j : ℂ) - w) =
      -((j : ℂ) + 1 - w)⁻¹ *
        ∫ s in (1 / 2 : ℝ)..1, iteratedDeriv (j + 1) g s * (s : ℂ) ^ (((j + 1 : ℕ) : ℂ) - w) := by
  set r : ℂ := (j : ℂ) - w with hr
  have hr1 : r + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hr] at this
    linarith
  have hrm1 : r ≠ -1 := fun h => hr1 (by rw [h]; ring)
  have hab := iteratedDeriv_eq_zero_at_endpoints hg hsupp j
  have hu : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1,
      HasDerivAt (iteratedDeriv j g) (iteratedDeriv (j + 1) g x) x := by
    intro x _
    have hd : Differentiable ℝ (iteratedDeriv j g) :=
      hg.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)
    rw [iteratedDeriv_succ]
    exact (hd x).hasDerivAt
  have hv : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1)) ((x : ℂ) ^ r) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact hasDerivAt_ofReal_cpow_const' (by simp only [Set.mem_Icc] at hx; linarith) hrm1
  have hu' : IntervalIntegrable (iteratedDeriv (j + 1) g) volume (1 / 2 : ℝ) 1 :=
    (hg.continuous_iteratedDeriv (j + 1) (by exact_mod_cast le_top)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume (1 / 2 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    exact continuousOn_cpow_Icc r
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [hab.1, hab.2, zero_mul, zero_mul, sub_zero, zero_sub] at h
  rw [h]
  have hcast : (((j + 1 : ℕ) : ℂ) - w) = r + 1 := by rw [hr]; push_cast; ring
  have hr1' : (j : ℂ) + 1 - w = r + 1 := by rw [hr]; ring
  rw [hcast, hr1', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1
  ext x
  field_simp

/-- `k` integrations by parts. -/
theorem integral_parts {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hsupp : ∀ s, g s ≠ 0 → 1 / 2 ≤ s ∧ s ≤ 1) {w : ℂ} (hw : w.re ≤ 0) (k : ℕ) :
    ∫ s in (1 / 2 : ℝ)..1, g s * (s : ℂ) ^ (-w) =
      (-1) ^ k * (∏ i ∈ Finset.range k, ((i : ℂ) + 1 - w))⁻¹ *
        ∫ s in (1 / 2 : ℝ)..1, iteratedDeriv k g s * (s : ℂ) ^ ((k : ℂ) - w) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [ih, integral_parts_step hg hsupp hw k, Finset.prod_range_succ, mul_inv, pow_succ]
    ring

/-- `|i + 1 - w| ≥ (1 + |w|)/2` for `Re w ≤ 0`. -/
theorem norm_succ_sub_ge (i : ℕ) {w : ℂ} (hw : w.re ≤ 0) :
    (1 + ‖w‖) / 2 ≤ ‖(i : ℂ) + 1 - w‖ := by
  have h1 : |((i : ℂ) + 1 - w).re| ≤ ‖(i : ℂ) + 1 - w‖ := Complex.abs_re_le_norm _
  have h2 : |((i : ℂ) + 1 - w).im| ≤ ‖(i : ℂ) + 1 - w‖ := Complex.abs_im_le_norm _
  have hre : ((i : ℂ) + 1 - w).re = i + 1 - w.re := by simp
  have him : ((i : ℂ) + 1 - w).im = -w.im := by simp
  rw [hre, abs_of_nonneg (by have : (0 : ℝ) ≤ i := i.cast_nonneg; linarith)] at h1
  rw [him, abs_neg] at h2
  have h3 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
  rw [abs_of_nonpos hw] at h3
  have : (0 : ℝ) ≤ i := i.cast_nonneg
  linarith

/-! ### Lemma 11.3 -/

theorem HypH.Xpos {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) : 0 < X := by
  have hE : (4 : ℝ) ≤ E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH.hH
  have h1 : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by push_cast; positivity)
  exact lt_of_lt_of_le h1 hH.hX

theorem HypH.norm_le_C0 {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) (t : ℝ) : ‖ψ₂ t‖ ≤ Cν 0 := by
  have := hH.deriv₂ 0 t
  simpa using this

/-- **Lemma 11.3**, the derivative bounds and the decay of `M_h`. -/
theorem Mh_bound (Cν : ℕ → ℝ) (k : ℕ) {η : ℝ} (_hη : 0 < η) :
    ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ∀ h : ℝ, 0 < h → h * X / K ≤ 4 * (((4 * E * d : ℕ) : ℝ) * X) ^ η →
        (∀ s ∈ Set.Icc (1 / 2 : ℝ) 1,
          ‖iteratedDeriv k (fun s => w1 ψ₁ s * ah ψ₂ X K h s) s‖ ≤ C * Lpar E d Δ X η ^ k) ∧
        (∀ w : ℂ, w.re ≤ 0 →
          ‖Mh ψ₁ ψ₂ X K h w‖ ≤ C * Lpar E d Δ X η ^ k * (1 + ‖w‖) ^ (-(k : ℝ))) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_gMh Cν k
  refine ⟨2 ^ k * A, ?_⟩
  intro E H d κ Δ X K ψ₁ ψ₂ hH h hh hhX
  set L := Lpar E d Δ X η with hLdef
  have hX0 := hH.Xpos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hq0 : 0 ≤ (((4 * E * d : ℕ) : ℝ) * X) ^ η := Real.rpow_nonneg (by positivity) _
  have hΔ1 := hH.hΔ
  have hΔL : Δ ≤ L := by rw [hLdef, Lpar]; linarith
  have hcL : |h * X / K| ≤ L := by
    rw [abs_of_pos (by positivity), hLdef, Lpar]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hder := hA Δ X K h L ψ₁ ψ₂ hΔ1 hH.smooth₁ hH.smooth₂.continuous hH.supp₂ hH.deriv₁
    hH.norm_le_C0 hΔL hcL
  have h2k : A * L ^ k ≤ 2 ^ k * A * L ^ k := by
    have : 0 ≤ A * L ^ k := by positivity
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  constructor
  · intro s hs
    exact (hder s hs).trans h2k
  · intro w hw
    have hg := contDiff_gMh hH.smooth₁ hH.supp₁ hH.smooth₂.continuous hH.supp₂ X K h
    have hsupp : ∀ s, gMh ψ₁ ψ₂ X K h s ≠ 0 → 1 / 2 ≤ s ∧ s ≤ 1 :=
      fun s hs => gMh_support hH.supp₁ X K h hs
    have hparts := integral_parts hg hsupp hw k
    have hMh : Mh ψ₁ ψ₂ X K h w = ∫ s in (1 / 2 : ℝ)..1, gMh ψ₁ ψ₂ X K h s * (s : ℂ) ^ (-w) :=
      rfl
    rw [hMh, hparts, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_inv, norm_prod]
    -- the product
    have hw0 : 0 < 1 + ‖w‖ := by positivity
    have hprod : ((1 + ‖w‖) / 2) ^ k ≤ ∏ i ∈ Finset.range k, ‖(i : ℂ) + 1 - w‖ := by
      calc ((1 + ‖w‖) / 2) ^ k = ∏ _i ∈ Finset.range k, (1 + ‖w‖) / 2 := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ i ∈ Finset.range k, ‖(i : ℂ) + 1 - w‖ :=
            Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => norm_succ_sub_ge i hw)
    -- the integral
    have hint : ‖∫ s in (1 / 2 : ℝ)..1, iteratedDeriv k (gMh ψ₁ ψ₂ X K h) s *
        (s : ℂ) ^ ((k : ℂ) - w)‖ ≤ A * L ^ k * |1 - 1 / 2| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le (by norm_num)] at hs
      have hs' : s ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      have hs0 : 0 < s := by linarith [hs.1]
      rw [norm_mul]
      have hcp : ‖(s : ℂ) ^ ((k : ℂ) - w)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hs0]
        apply Real.rpow_le_one hs0.le hs.2
        simp only [Complex.sub_re, Complex.natCast_re]
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        linarith
      calc ‖iteratedDeriv k (gMh ψ₁ ψ₂ X K h) s‖ * ‖(s : ℂ) ^ ((k : ℂ) - w)‖
          ≤ A * L ^ k * 1 := mul_le_mul (hder s hs') hcp (norm_nonneg _) (by positivity)
        _ = A * L ^ k := mul_one _
    have hinv : (∏ i ∈ Finset.range k, ‖(i : ℂ) + 1 - w‖)⁻¹ ≤ (((1 + ‖w‖) / 2) ^ k)⁻¹ :=
      inv_anti₀ (by positivity) hprod
    have hrpow : (1 + ‖w‖) ^ (-(k : ℝ)) = ((1 + ‖w‖) ^ k)⁻¹ := by
      rw [Real.rpow_neg hw0.le, Real.rpow_natCast]
    rw [hrpow]
    have hpos : 0 ≤ 2 ^ k * A * L ^ k * ((1 + ‖w‖) ^ k)⁻¹ := by positivity
    calc (∏ i ∈ Finset.range k, ‖(i : ℂ) + 1 - w‖)⁻¹ *
          ‖∫ s in (1 / 2 : ℝ)..1, iteratedDeriv k (gMh ψ₁ ψ₂ X K h) s * (s : ℂ) ^ ((k : ℂ) - w)‖
        ≤ (((1 + ‖w‖) / 2) ^ k)⁻¹ * (A * L ^ k * |1 - 1 / 2|) :=
          mul_le_mul hinv hint (norm_nonneg _) (by positivity)
      _ = 2 ^ k * A * L ^ k * ((1 + ‖w‖) ^ k)⁻¹ * (1 / 2) := by
          rw [div_pow, inv_div, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
          field_simp
      _ ≤ 2 ^ k * A * L ^ k * ((1 + ‖w‖) ^ k)⁻¹ := by linarith
/-- `|w₁(s)| ≤ 2 C₀` on `[1/2, 1]`. -/
theorem norm_w1_le {ψ₁ : ℝ → ℂ} {B : ℝ} (hB : ∀ t, ‖ψ₁ t‖ ≤ B) {s : ℝ}
    (hs : s ∈ Set.Icc (1 / 2 : ℝ) 1) : ‖w1 ψ₁ s‖ ≤ 2 * B := by
  have hs0 : 0 < s := by simp only [Set.mem_Icc] at hs; linarith
  unfold w1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
  have h1 : s ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    calc s ^ (-(1 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hs.1 (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ = 2 := by rw [Real.rpow_neg_one]; norm_num
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h2 := hB (1 / s)
  calc s ^ (-(1 / 2 : ℝ)) * ‖ψ₁ (1 / s)‖ ≤ 2 * B :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)

theorem continuousOn_w1 {ψ₁ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ₁) :
    ContinuousOn (w1 ψ₁) (Set.Icc (1 / 2 : ℝ) 1) :=
  (contDiffOn_w1 hψ).continuousOn.mono (fun s hs => by
    simp only [Set.mem_Icc] at hs; simp only [Set.mem_Ioi]; linarith)

/-- **Lemma 11.3**, the derivative in `h`: `h ↦ M_h(w)` is differentiable and
`|∂_h M_h(w)| ≪ X/K` on `Re w = 0`. -/
theorem Mh_deriv_bound' (Cν : ℕ → ℝ) {η : ℝ} (_hη : 0 < η) :
    ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ∀ h : ℝ, 0 < h → h * X / K ≤ 4 * (((4 * E * d : ℕ) : ℝ) * X) ^ η →
        ∀ w : ℂ, w.re = 0 → DifferentiableAt ℝ (fun h' => Mh ψ₁ ψ₂ X K h' w) h ∧
          ‖deriv (fun h' => Mh ψ₁ ψ₂ X K h' w) h‖ ≤ C * X / K := by
  refine ⟨8 * Real.pi * Cν 0 ^ 2, ?_⟩
  intro E H d κ Δ X K ψ₁ ψ₂ hH h _ _ w hw
  have hX0 := hH.Xpos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hB₂ : ∀ t, ‖ψ₂ t‖ ≤ |Cν 0| := fun t => (hH.norm_le_C0 t).trans (le_abs_self _)
  have hB₁ : ∀ t, ‖ψ₁ t‖ ≤ |Cν 0| := fun t => by
    have := hH.deriv₁ 0 t
    simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
    exact this.trans (le_abs_self _)
  have hFc : ContDiff ℝ ∞ (𝓕 ψ₂) := contDiff_fourier_of_support hH.smooth₂.continuous hH.supp₂
  have hFd : Differentiable ℝ (𝓕 ψ₂) := hFc.differentiable (by exact_mod_cast WithTop.top_ne_zero)
  have hFdc : Continuous (deriv (𝓕 ψ₂)) := hFc.continuous_deriv (by exact_mod_cast le_top)
  have hFd1 : ∀ ξ, ‖deriv (𝓕 ψ₂) ξ‖ ≤ 2 * Real.pi * |Cν 0| * 2 := by
    intro ξ
    have := norm_iteratedDeriv_fourier_le hH.smooth₂.continuous hH.supp₂ hB₂ 1 ξ
    rwa [iteratedDeriv_one, pow_one] at this
  -- the integrand and its derivative in `h`
  set F : ℝ → ℝ → ℂ := fun h' t => w1 ψ₁ t * ah ψ₂ X K h' t * (t : ℂ) ^ (-w) with hF
  set F' : ℝ → ℝ → ℂ := fun h' t =>
    w1 ψ₁ t * (((X * t / K : ℝ) : ℂ) * deriv (𝓕 ψ₂) (h' * (X * t / K))) * (t : ℂ) ^ (-w)
    with hF'
  have hah : ∀ h' t, ah ψ₂ X K h' t = 𝓕 ψ₂ (h' * (X * t / K)) := by
    intro h' t
    unfold ah
    rw [fourier_eq_fourierIntegral, show h' * X * t / K = h' * (X * t / K) by ring]
  have hIcc : Set.uIoc (1 / 2 : ℝ) 1 ⊆ Set.Icc (1 / 2 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num)]; exact Set.Ioc_subset_Icc_self
  have hcpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-w)) (Set.Icc (1 / 2 : ℝ) 1) :=
    continuousOn_cpow_Icc (-w)
  have hFcont : ∀ h', ContinuousOn (F h') (Set.Icc (1 / 2 : ℝ) 1) := by
    intro h'
    simp only [hF]
    apply ContinuousOn.mul _ hcpow
    apply (continuousOn_w1 hH.smooth₁).mul
    exact (contDiff_ah hH.smooth₂.continuous hH.supp₂ X K h').continuous.continuousOn
  have hF'cont : ContinuousOn (F' h) (Set.Icc (1 / 2 : ℝ) 1) := by
    simp only [hF']
    apply ContinuousOn.mul _ hcpow
    apply (continuousOn_w1 hH.smooth₁).mul
    apply Continuous.continuousOn
    exact (continuous_ofReal.comp (by fun_prop)).mul (hFdc.comp (by fun_prop))
  -- the bound for `F'`
  set bound : ℝ := 2 * |Cν 0| * (X / K * (2 * Real.pi * |Cν 0| * 2)) with hbound
  have hF'le : ∀ h' t, t ∈ Set.Icc (1 / 2 : ℝ) 1 → ‖F' h' t‖ ≤ bound := by
    intro h' t ht
    have ht0 : 0 < t := by simp only [Set.mem_Icc] at ht; linarith
    simp only [hF']
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-w).re = 0 := by simp [hw]
    rw [hre, Real.rpow_zero, mul_one]
    have h1 := norm_w1_le hB₁ ht
    have h2 : |X * t / K| ≤ X / K := by
      rw [abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_right _ hK0.le
      nlinarith [ht.2]
    have h3 := hFd1 (h' * (X * t / K))
    calc ‖w1 ψ₁ t‖ * (|X * t / K| * ‖deriv (𝓕 ψ₂) (h' * (X * t / K))‖)
        ≤ (2 * |Cν 0|) * (X / K * (2 * Real.pi * |Cν 0| * 2)) := by gcongr
      _ = bound := rfl
  have hderiv : ∀ h' t, HasDerivAt (fun h'' => F h'' t) (F' h' t) h' := by
    intro h' t
    simp only [hF, hF', hah]
    have h1 : HasDerivAt (fun h'' : ℝ => h'' * (X * t / K)) (X * t / K) h' := by
      simpa using (hasDerivAt_id h').mul_const (X * t / K)
    have h2 := (hFd (h' * (X * t / K))).hasDerivAt.scomp h' h1
    have h3 := (h2.const_mul (w1 ψ₁ t)).mul_const ((t : ℂ) ^ (-w))
    convert h3 using 1
    simp
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := h) (a := 1 / 2) (b := 1) (μ := volume) (bound := fun _ => bound)
    Filter.univ_mem
    (Filter.Eventually.of_forall (fun h' => ((hFcont h').mono hIcc).aestronglyMeasurable
      measurableSet_uIoc))
    ((hFcont h).intervalIntegrable_of_Icc (by norm_num))
    ((hF'cont.mono hIcc).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall (fun t ht h' _ => hF'le h' t (hIcc ht)))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ h' _ => hderiv h' t))
  have heq : (fun h' => Mh ψ₁ ψ₂ X K h' w) = fun h' => ∫ t in (1 / 2 : ℝ)..1, F h' t := rfl
  rw [heq, hmain.2.deriv]
  refine ⟨hmain.2.differentiableAt, ?_⟩
  calc ‖∫ t in (1 / 2 : ℝ)..1, F' h t‖ ≤ bound * |1 - 1 / 2| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hF'le h t (hIcc ht))
    _ ≤ 8 * Real.pi * Cν 0 ^ 2 * X / K := by
        rw [hbound, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
        have hC : |Cν 0| ^ 2 = Cν 0 ^ 2 := sq_abs _
        have hXK : 0 ≤ X / K := by positivity
        have : 2 * |Cν 0| * (X / K * (2 * Real.pi * |Cν 0| * 2)) * (1 / 2) =
            4 * Real.pi * |Cν 0| ^ 2 * (X / K) := by ring
        rw [this, hC]
        have hpi := Real.pi_pos
        have h0 : 0 ≤ Real.pi * Cν 0 ^ 2 * (X / K) := by positivity
        rw [show 8 * Real.pi * Cν 0 ^ 2 * X / K = 8 * (Real.pi * Cν 0 ^ 2 * (X / K)) by ring]
        nlinarith

/-- **Lemma 11.3**, the derivative in `h`: `|∂_h M_h(w)| ≪ X/K` on `Re w = 0`. -/
theorem Mh_deriv_bound (Cν : ℕ → ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ∀ h : ℝ, 0 < h → h * X / K ≤ 4 * (((4 * E * d : ℕ) : ℝ) * X) ^ η →
        ∀ w : ℂ, w.re = 0 → ‖deriv (fun h' => Mh ψ₁ ψ₂ X K h' w) h‖ ≤ C * X / K := by
  obtain ⟨C, hC⟩ := Mh_deriv_bound' Cν hη
  exact ⟨C, fun E H d κ Δ X K ψ₁ ψ₂ hH h hh hhX w hw => (hC E H d κ Δ X K ψ₁ ψ₂ hH h hh hhX w hw).2⟩

end Triples
