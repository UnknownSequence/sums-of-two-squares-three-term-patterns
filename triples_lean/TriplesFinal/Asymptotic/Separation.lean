import TriplesFinal.Asymptotic.ErrorSetup
import TriplesFinal.Asymptotic.WeightFourier
import TriplesFinal.Asymptotic.DyadicPartition

/-!
# Separation of variables in the error term (proof of Lemma 7.3)

Fix `K > 0` and put `u₀ = log(2^((v-2)/2) K/√x)`, `f = f_{u₀}` (`WeightFourier`),

* `ψ_{1,ξ}(s) = ψ₀(s) e^{2πiξ log s}` (`psiOne`), with `ψ₀` the dyadic partition;
* `ψ_{2,ξ}(s) = G_ξ(T(Xs)/x)` with `G_ξ(u) = F(u) e^{-πiξ log u}` (`psiTwo`).

**The key identity** (`IsGood.psi0_mul_Phi_eq`): for `k ≥ 0` and `t ∈ ℝ`,
`ψ₀(k/K) Φ_k(t) = ∫ 𝓕f(ξ) ψ_{1,ξ}(k/K) ψ_{2,ξ}(t/X) dξ`. On the support,
`W(2^((v-2)/2) k/√T(t)) = W(e^(u₀ + v))` with `v = log(k/K) - ½ log(T(t)/x) ∈ [0, 2]`, and the
Fourier inversion formula for `f` splits `e^{2πiξv}`.

Summing over `ℓ` (a finite sum) and integrating over `t` (Fubini) gives
`ψ₀(k/K) e(k) = ∫ (...) dξ` (`IsGood.psi0_mul_ek_eq`), and summing over `k ≡ κ (mod 4)`,
`k ≤ 2K`, with `μ = dk` (`sum_moduli_eq`) and `ϱ(dk) = ϱ_{E,H}(dk)`:

`∑_{k ≡ κ (4)} ψ₀(k/K) e(k) = ∫ 𝓕f(ξ) Ξ_ξ dξ` (`IsGood.sum_psi0_ek_eq`),

where `Ξ_ξ` is the sum `Ξ` of (6.1) with moduli of size `dK` and the weights `ψ_{1,ξ}, ψ_{2,ξ}`.

Paper: §7.3, proof of Lemma 7.3 (the paper uses Mellin inversion of `W` on `Re w = 1`).
-/

namespace Triples

open MeasureTheory Complex
open scoped FourierTransform

/-- The moduli `μ ≡ κd (mod 4d)`, `1 ≤ μ ≤ 2dK`, are the `μ = dk` with `k ≡ κ (mod 4)`,
`1 ≤ k ≤ 2K`. -/
theorem sum_moduli_eq {d κ : ℕ} (hd : 0 < d) (hκ : κ < 4) {K : ℝ} (hK : 0 < K) {M : Type*}
    [AddCommMonoid M] (g : ℕ → M) :
    ∑ μ ∈ moduli d κ (d * K), g μ =
      ∑ k ∈ (Finset.Icc 1 ⌊2 * K⌋₊).filter (fun k => k % 4 = κ), g (d * k) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hmod : ∀ μ ∈ moduli d κ (d * K), ∃ q, μ = d * (4 * q + κ) := by
    intro μ hμ
    simp only [moduli, Finset.mem_filter] at hμ
    have h1 := Nat.div_add_mod μ (4 * d)
    rw [hμ.2, Nat.mod_eq_of_lt (by nlinarith)] at h1
    set q := μ / (4 * d)
    exact ⟨q, by linarith [h1]⟩
  symm
  apply Finset.sum_nbij' (fun k => d * k) (fun μ => μ / d)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, moduli] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hk4⟩ := hk
    refine ⟨⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩, ?_⟩
    · apply Nat.le_floor
      have : (k : ℝ) ≤ 2 * K := (Nat.le_floor_iff (by positivity)).1 hk2
      push_cast
      nlinarith
    · rw [show 4 * d = d * 4 by ring, Nat.mul_mod_mul_left, mul_comm κ d, Nat.mul_mod_mul_left,
        hk4, Nat.mod_eq_of_lt hκ]
  · intro μ hμ
    obtain ⟨q, hq⟩ := hmod μ hμ
    simp only [moduli, Finset.mem_filter, Finset.mem_Icc] at hμ
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hq, Nat.mul_div_cancel_left _ hd]
    obtain ⟨⟨hμ1, hμ2⟩, -⟩ := hμ
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · rcases Nat.eq_zero_or_pos (4 * q + κ) with h | h
      · rw [hq, h, mul_zero] at hμ1; omega
      · exact h
    · apply Nat.le_floor
      have h1 : (μ : ℝ) ≤ 2 * (d * K) :=
        (Nat.le_floor_iff (by positivity)).1 hμ2
      rw [hq] at h1
      push_cast at h1 ⊢
      nlinarith
  · intro k _
    rw [Nat.mul_div_cancel_left _ hd]
  · intro μ hμ
    obtain ⟨q, hq⟩ := hmod μ hμ
    rw [hq, Nat.mul_div_cancel_left _ hd]
  · intro k _
    rfl

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- `ψ_{1,ξ}(s) = ψ₀(s) e^{2πiξ log s}`. -/
noncomputable def psiOne (ξ : ℝ) : ℝ → ℂ :=
  phaseFn (fun s => (Dyadic.psi0 s : ℂ)) (2 * Real.pi * ξ)

/-- `G_ξ(u) = F(u) e^{-πiξ log u}`. -/
noncomputable def Gphase (F : Cutoff) (ξ : ℝ) : ℝ → ℂ :=
  phaseFn (fun u => (F.F u : ℂ)) (-(Real.pi * ξ))

variable (P) in
/-- `ψ_{2,ξ}(s) = G_ξ(T(Xs)/x)`. -/
noncomputable def psiTwo (F : Cutoff) (d : ℕ) (x ξ : ℝ) (s : ℝ) : ℂ :=
  Gphase F ξ (P.Treal d (P.Xpar d x * s) / x)

variable (P) in
/-- `u₀ = log(2^((v-2)/2) K/√x)`. -/
noncomputable def uzero (x K : ℝ) : ℝ :=
  Real.log ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) * K / Real.sqrt x)

variable (P) in
/-- The function `f_{u₀}` of `WeightFourier` for `u₀ = log(2^((v-2)/2) K/√x)`. -/
noncomputable def fK (W : HyperbolaWeight) (x K : ℝ) : ℝ → ℂ := WeightFourier.fW W (P.uzero x K)

theorem psi0_le_one (t : ℝ) : Dyadic.psi0 t ≤ 1 := by
  unfold Dyadic.psi0 Dyadic.chi
  have h1 := Real.smoothTransition.nonneg ((t / Real.sqrt 2 - 1) / (Real.sqrt 2 - 1))
  have h2 := Real.smoothTransition.le_one ((t - 1) / (Real.sqrt 2 - 1))
  linarith

theorem norm_cexp_mul_I (r : ℝ) : ‖Complex.exp (r * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I r

theorem norm_phaseFn_le {g : ℝ → ℂ} (hg : ∀ u, ‖g u‖ ≤ 1) (c u : ℝ) : ‖phaseFn g c u‖ ≤ 1 := by
  unfold phaseFn
  rw [norm_mul]
  have : ‖Complex.exp (c * Real.log u * I)‖ = 1 := by
    rw [show (c * Real.log u * I : ℂ) = ((c * Real.log u : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_cexp_mul_I _
  rw [this, mul_one]
  exact hg u

theorem norm_psiOne_le (ξ s : ℝ) : ‖psiOne ξ s‖ ≤ 1 :=
  norm_phaseFn_le (fun u => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Dyadic.psi0_nonneg u)]
    exact psi0_le_one u) _ _

theorem norm_Gphase_le (F : Cutoff) (ξ u : ℝ) : ‖Gphase F ξ u‖ ≤ 1 :=
  norm_phaseFn_le (fun u => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (F.nonneg u)]
    exact F.le_one u) _ _

theorem norm_psiTwo_le (F : Cutoff) (d : ℕ) (x ξ s : ℝ) : ‖P.psiTwo F d x ξ s‖ ≤ 1 :=
  norm_Gphase_le F ξ _

/-- `e^{2πiξ a} e^{-πiξ b} = e^{2πiξ (a - b/2)}`. -/
theorem cexp_split (ξ a b : ℝ) :
    Complex.exp ((2 * Real.pi * ξ : ℝ) * a * I) * Complex.exp ((-(Real.pi * ξ) : ℝ) * b * I) =
      Complex.exp (((2 * Real.pi * ξ * (a - b / 2) : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The key identity**: `ψ₀(k/K) Φ_k(t) = ∫ 𝓕f(ξ) ψ_{1,ξ}(k/K) ψ_{2,ξ}(t/X) dξ`. -/
theorem IsGood.psi0_mul_Phi_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) {K : ℝ} (hK : 0 < K) (k : ℕ) (t : ℝ) :
    ((Dyadic.psi0 (k / K) * P.Phi F W d x k t : ℝ) : ℂ) =
      ∫ ξ : ℝ, 𝓕 (P.fK W x K) ξ * (psiOne ξ (k / K) * P.psiTwo F d x ξ (t / P.Xpar d x)) := by
  have hX0 := (hd.Xpar_spec hx).1
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  have hXt : P.Xpar d x * (t / P.Xpar d x) = t := by field_simp
  have hpsiTwo : ∀ ξ, P.psiTwo F d x ξ (t / P.Xpar d x) =
      (F.F (P.Treal d t / x) : ℂ) * Complex.exp ((-(Real.pi * ξ) : ℝ) * Real.log (P.Treal d t / x) * I) := by
    intro ξ
    simp only [psiTwo, Gphase, phaseFn, hXt]
  by_cases h1 : Dyadic.psi0 (k / K) = 0
  · simp [h1, psiOne, phaseFn]
  by_cases h2 : F.F (P.Treal d t / x) = 0
  · simp [hpsiTwo, h2, Phi]
  -- the main case
  obtain ⟨hy1, hy2⟩ := Dyadic.psi0_support h1
  obtain ⟨hz1, hz2⟩ := Treal_mem_of_F_ne_zero F hx0 h2
  have hT0 := hd.Treal_pos t
  set y : ℝ := k / K with hy
  set z : ℝ := P.Treal d t / x with hz
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := div_pos hT0 hx0
  have hz1' : 1 / 2 ≤ z := by rw [hz, le_div_iff₀ hx0]; linarith
  have hz2' : z ≤ 1 := by rw [hz, div_le_one hx0]; exact hz2
  set v : ℝ := Real.log y - Real.log z / 2 with hv
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hly2 : Real.log y ≤ Real.log 2 := Real.log_le_log hy0 hy2
  have hlz0 : Real.log z ≤ 0 := Real.log_nonpos hz0.le hz2'
  have hlz2 : -Real.log 2 ≤ Real.log z := by
    have := Real.log_le_log (by norm_num) hz1'
    rw [one_div, Real.log_inv] at this
    exact this
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hv2 : v ≤ 2 := by rw [hv]; linarith
  -- `W(2^((v-2)/2) k/√T) = W(exp(u₀ + v))`
  set c : ℝ := (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) with hc
  have hc0 : 0 < c := by positivity
  have hk0 : (0 : ℝ) < k := by
    have : (0 : ℝ) < y * K := mul_pos hy0 hK
    rwa [hy, div_mul_cancel₀ _ hK.ne'] at this
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsT : 0 < Real.sqrt (P.Treal d t) := Real.sqrt_pos.2 hT0
  have hexp : Real.exp (P.uzero x K + v) = c * k / Real.sqrt (P.Treal d t) := by
    have e1 : Real.exp (P.uzero x K) = c * K / Real.sqrt x := by
      unfold uzero; rw [Real.exp_log (by positivity)]
    have e2 : Real.exp (Real.log z / 2) = Real.sqrt z := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz0]; ring_nf
    have e3 : Real.sqrt z = Real.sqrt (P.Treal d t) / Real.sqrt x := by
      rw [hz, Real.sqrt_div' _ hx0.le]
    rw [hv, sub_eq_add_neg, ← add_assoc, Real.exp_add, Real.exp_add, Real.exp_log hy0,
      Real.exp_neg, e1, e2, e3, hy]
    field_simp
  have hW := WeightFourier.W_exp_eq_integral W (P.uzero x K) hv0 hv2
  rw [hexp] at hW
  -- assemble
  have hPhi : P.Phi F W d x k t = F.F z * W.W (c * k / Real.sqrt (P.Treal d t)) := rfl
  rw [hPhi]
  push_cast
  rw [← hW, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hpsiTwo ξ]
  simp only [psiOne, phaseFn]
  have hsplit := cexp_split ξ (Real.log y) (Real.log z)
  rw [← hv] at hsplit
  calc (Dyadic.psi0 y : ℂ) * (F.F z * (Complex.exp (((2 * Real.pi * ξ * v : ℝ) : ℂ) * I) *
        𝓕 (P.fK W x K) ξ))
      = 𝓕 (P.fK W x K) ξ * ((Dyadic.psi0 y : ℂ) * (F.F z : ℂ) *
        Complex.exp (((2 * Real.pi * ξ * v : ℝ) : ℂ) * I)) := by ring
    _ = _ := by
      rw [← hsplit]
      push_cast
      ring

theorem continuous_psiOne_param (y : ℝ) : Continuous (fun ξ : ℝ => psiOne ξ y) := by
  unfold psiOne phaseFn
  fun_prop

theorem IsGood.continuous_psiTwo_uncurry {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx0 : 0 < x) (X : ℝ) :
    Continuous (fun p : ℝ × ℝ => P.psiTwo F d x p.2 (p.1 / X)) := by
  unfold psiTwo Gphase phaseFn
  have hq : Continuous (fun p : ℝ × ℝ => P.Treal d (P.Xpar d x * (p.1 / X)) / x) :=
    ((continuous_Treal d).comp (continuous_const.mul (continuous_fst.div_const X))).div_const x
  have hq0 : ∀ p : ℝ × ℝ, P.Treal d (P.Xpar d x * (p.1 / X)) / x ≠ 0 :=
    fun p => (div_pos (hd.Treal_pos _) hx0).ne'
  have hlog := hq.log hq0
  have hF := F.smooth.continuous.comp hq
  apply Continuous.mul
  · exact continuous_ofReal.comp hF
  · apply Continuous.cexp
    apply Continuous.mul _ continuous_const
    apply Continuous.mul
    · exact continuous_ofReal.comp (continuous_snd.const_mul Real.pi).neg
    · exact continuous_ofReal.comp hlog

theorem IsGood.continuous_psiTwo_param {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx0 : 0 < x) (X t : ℝ) : Continuous (fun ξ : ℝ => P.psiTwo F d x ξ (t / X)) := by
  have hg : Continuous (fun ξ : ℝ => ((t, ξ) : ℝ × ℝ)) :=
    (continuous_const : Continuous (fun _ : ℝ => t)).prodMk continuous_id
  have h := (hd.continuous_psiTwo_uncurry F hx0 X).comp hg
  exact h

/-- `ψ_{2,ξ}(t/X) = 0` for `|t| > X`. -/
theorem IsGood.psiTwo_eq_zero {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx : 33 * (d : ℝ) ≤ x) (ξ : ℝ) {t : ℝ} (ht : P.Xpar d x < |t|) :
    P.psiTwo F d x ξ (t / P.Xpar d x) = 0 := by
  have hX0 := (hd.Xpar_spec hx).1
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  have hXt : P.Xpar d x * (t / P.Xpar d x) = t := by field_simp
  have hT : x < P.Treal d t := by
    by_contra h
    push Not at h
    exact absurd (hd.abs_le_Xpar hx h) (not_le.2 ht)
  have hF : F.F (P.Treal d t / x) = 0 := F.F_eq_zero_of_gt (by rw [one_lt_div hx0]; exact hT)
  simp [psiTwo, Gphase, phaseFn, hXt, hF]

variable (P) in
/-- The integrand `𝓕f(ξ) ψ_{1,ξ}(y) ψ_{2,ξ}(t/X)`. -/
noncomputable def integrand (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x K y : ℝ)
    (t ξ : ℝ) : ℂ :=
  𝓕 (P.fK W x K) ξ * (psiOne ξ y * P.psiTwo F d x ξ (t / P.Xpar d x))

theorem integrable_fourier_fK (W : HyperbolaWeight) (x K : ℝ) : Integrable (𝓕 (P.fK W x K)) :=
  integrable_fourier_of_compactSupport (WeightFourier.contDiff_fW W _)
    (WeightFourier.hasCompactSupport_fW W _)

theorem continuous_fourier_fK (W : HyperbolaWeight) (x K : ℝ) : Continuous (𝓕 (P.fK W x K)) :=
  continuous_fourierTransform
    ((WeightFourier.contDiff_fW W _).continuous.integrable_of_hasCompactSupport
      (WeightFourier.hasCompactSupport_fW W _))

theorem norm_integrand_le (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x K y t ξ : ℝ) :
    ‖P.integrand F W d x K y t ξ‖ ≤ ‖𝓕 (P.fK W x K) ξ‖ := by
  unfold integrand
  rw [norm_mul, norm_mul]
  have h1 := norm_psiOne_le ξ y
  have h2 := norm_psiTwo_le (P := P) F d x ξ (t / P.Xpar d x)
  have h3 : ‖psiOne ξ y‖ * ‖P.psiTwo F d x ξ (t / P.Xpar d x)‖ ≤ 1 := by
    nlinarith [norm_nonneg (psiOne ξ y), norm_nonneg (P.psiTwo F d x ξ (t / P.Xpar d x))]
  nlinarith [norm_nonneg (𝓕 (P.fK W x K) ξ)]

theorem IsGood.integrable_integrand {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx0 : 0 < x) (K y t : ℝ) :
    Integrable (P.integrand F W d x K y t) := by
  apply (integrable_fourier_fK (P := P) W x K).norm.mono'
  · exact ((continuous_fourier_fK W x K).mul ((continuous_psiOne_param y).mul
      (hd.continuous_psiTwo_param F hx0 _ t))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ξ => norm_integrand_le F W d x K y t ξ)

theorem IsGood.integrable_integrand_prod {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) (K y : ℝ) :
    Integrable (Function.uncurry (P.integrand F W d x K y)) (volume.prod volume) := by
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  set X := P.Xpar d x
  have hind : Integrable (Set.indicator (Set.Icc (-X) X) (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have hprod := hind.mul_prod (integrable_fourier_fK (P := P) W x K).norm
  apply hprod.mono'
  · apply Continuous.aestronglyMeasurable
    unfold Function.uncurry integrand
    exact ((continuous_fourier_fK W x K).comp continuous_snd).mul
      (((continuous_psiOne_param y).comp continuous_snd).mul
        (hd.continuous_psiTwo_uncurry F hx0 X))
  · refine Filter.Eventually.of_forall (fun p => ?_)
    obtain ⟨t, ξ⟩ := p
    simp only [Function.uncurry_apply_pair]
    by_cases ht : |t| ≤ X
    · rw [Set.indicator_of_mem (by rw [Set.mem_Icc]; exact abs_le.1 ht), one_mul]
      exact norm_integrand_le F W d x K y t ξ
    · rw [Set.indicator_of_notMem (by rw [Set.mem_Icc]; intro h; exact ht (abs_le.2 h)),
        zero_mul]
      unfold integrand
      rw [hd.psiTwo_eq_zero F hx ξ (not_le.1 ht)]
      simp

/-- `∫ 𝓕f(ξ) ψ_{1,ξ}(y) ψ_{2,ξ}(t/X) dt = 𝓕f(ξ) ψ_{1,ξ}(y) X ∫ ψ_{2,ξ}`. -/
theorem IsGood.integral_integrand_t {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) (K y ξ : ℝ) :
    ∫ t, P.integrand F W d x K y t ξ =
      𝓕 (P.fK W x K) ξ * (psiOne ξ y * ((P.Xpar d x : ℂ) * ∫ s, P.psiTwo F d x ξ s)) := by
  have hX0 := (hd.Xpar_spec hx).1
  unfold integrand
  rw [integral_const_mul, integral_const_mul, Measure.integral_comp_div, abs_of_pos hX0,
    Complex.real_smul]

variable (P) in
/-- The integrand of `ψ₀(k/K) e(k)`. -/
noncomputable def ekIntegrand (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x K : ℝ) (k : ℕ)
    (ξ : ℝ) : ℂ :=
  𝓕 (P.fK W x K) ξ * (psiOne ξ (k / K) *
    ((∑ ℓ ∈ lattice P.Enat (P.Hnat d) (d * k) (P.Xpar d x), P.psiTwo F d x ξ (ℓ / P.Xpar d x)) -
      (rho (P.m d) (d * k) : ℂ) / ((d : ℂ) * k) * (P.Xpar d x : ℂ) *
        ∫ s : ℝ, P.psiTwo F d x ξ s))

theorem IsGood.ekIntegrand_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) (K : ℝ) (k : ℕ) (ξ : ℝ) :
    P.ekIntegrand F W d x K k ξ =
      (∑ ℓ ∈ lattice P.Enat (P.Hnat d) (d * k) (P.Xpar d x),
          P.integrand F W d x K (k / K) ℓ ξ) -
        (rho (P.m d) (d * k) : ℂ) / ((d : ℂ) * k) *
          ∫ t, P.integrand F W d x K (k / K) t ξ := by
  rw [hd.integral_integrand_t F W hx K _ ξ]
  simp only [integrand, ekIntegrand]
  rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  ring

theorem IsGood.integrable_ekIntegrand {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) (K : ℝ) (k : ℕ) :
    Integrable (P.ekIntegrand F W d x K k) := by
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  have hint1 : Integrable (fun ξ => ∑ ℓ ∈ lattice P.Enat (P.Hnat d) (d * k) (P.Xpar d x),
      P.integrand F W d x K (k / K) ℓ ξ) :=
    integrable_finsetSum _ (f := fun (ℓ : ℤ) (ξ : ℝ) => P.integrand F W d x K (k / K) ℓ ξ)
      (fun ℓ _ => hd.integrable_integrand F W hx0 K _ ℓ)
  have hint2 : Integrable (fun ξ => ∫ t, P.integrand F W d x K (k / K) t ξ) :=
    (hd.integrable_integrand_prod F W hx K _).integral_prod_right
  have := hint1.sub (hint2.const_mul ((rho (P.m d) (d * k) : ℂ) / ((d : ℂ) * k)))
  refine this.congr (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only [Pi.sub_apply]
  rw [hd.ekIntegrand_eq F W hx K k ξ]

/-- `ψ₀(k/K) e(k)` as an integral over `ξ`. -/
theorem IsGood.psi0_mul_ek_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) {K : ℝ} (hK : 0 < K) (k : ℕ) :
    ((Dyadic.psi0 (k / K) * P.ek F W d x k : ℝ) : ℂ) =
      ∫ ξ : ℝ, P.ekIntegrand F W d x K k ξ := by
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  set X := P.Xpar d x with hXdef
  set L := lattice P.Enat (P.Hnat d) (d * k) X with hL
  set y : ℝ := k / K with hy
  set c : ℂ := (rho (P.m d) (d * k) : ℂ) / ((d : ℂ) * k) with hc
  have hA : (∑ᶠ (ℓ : ℤ) (_ : ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), P.Phi F W d x k ℓ) =
      ∑ ℓ ∈ L, P.Phi F W d x k ℓ :=
    hd.finsum_eq_lattice hx k _
      (fun ℓ h => (Treal_mem_of_F_ne_zero F hx0 (left_ne_zero_of_mul h)).2)
  -- the lattice sum
  have ha : ((Dyadic.psi0 y * ∑ ℓ ∈ L, P.Phi F W d x k ℓ : ℝ) : ℂ) =
      ∫ ξ, ∑ ℓ ∈ L, P.integrand F W d x K y ℓ ξ := by
    rw [integral_finsetSum L (f := fun (ℓ : ℤ) (ξ : ℝ) => P.integrand F W d x K y ℓ ξ)
      (fun ℓ _ => hd.integrable_integrand F W hx0 K y ℓ)]
    rw [Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro ℓ _
    have := hd.psi0_mul_Phi_eq F W hx hK k ℓ
    push_cast at this
    rw [this]
    rfl
  -- the integral
  have hb : ((Dyadic.psi0 y * ∫ t, P.Phi F W d x k t : ℝ) : ℂ) =
      ∫ ξ, ∫ t, P.integrand F W d x K y t ξ := by
    rw [← integral_const_mul, ← integral_complex_ofReal]
    rw [← integral_integral_swap (hd.integrable_integrand_prod F W hx K y)]
    apply integral_congr_ae
    filter_upwards with t
    exact hd.psi0_mul_Phi_eq F W hx hK k t
  have hint1 : Integrable (fun ξ => ∑ ℓ ∈ L, P.integrand F W d x K y ℓ ξ) :=
    integrable_finsetSum L (f := fun (ℓ : ℤ) (ξ : ℝ) => P.integrand F W d x K y ℓ ξ)
      (fun ℓ _ => hd.integrable_integrand F W hx0 K y ℓ)
  have hint2 : Integrable (fun ξ => ∫ t, P.integrand F W d x K y t ξ) :=
    (hd.integrable_integrand_prod F W hx K y).integral_prod_right
  have hek : ((Dyadic.psi0 y * P.ek F W d x k : ℝ) : ℂ) =
      ((Dyadic.psi0 y * ∑ ℓ ∈ L, P.Phi F W d x k ℓ : ℝ) : ℂ) -
        c * ((Dyadic.psi0 y * ∫ t, P.Phi F W d x k t : ℝ) : ℂ) := by
    unfold ek
    rw [hA, hc]
    push_cast
    ring
  rw [hek, ha, hb, ← integral_const_mul, ← integral_sub hint1 (hint2.const_mul c)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hd.ekIntegrand_eq F W hx K k ξ]

/-- `ϱ(dk) = ϱ_{E,H}(dk)` for odd `k`. -/
theorem IsGood.rho_eq_rhoEH_mul {d : ℕ} (hd : P.IsGood d) {k : ℕ} (hk : k % 2 = 1) :
    rho (P.m d) (d * k) = rhoEH ((P.Enat : ℕ) : ℤ) ((P.Hnat d : ℕ) : ℤ) (d * k) := by
  rw [P.Enat_cast, hd.Hnat_cast, hd.m_eq]
  apply rho_eq_rhoEH P.two_pow_v_mul_E
  have hd4 := hd.emod_four
  have : d % 2 = 1 := by omega
  rw [Nat.mul_mod, this, hk]

/-- **The separation of variables**: the sum `ℰ(K, κ)` of the proof of Lemma 7.3 is
`∫ 𝓕f(ξ) Ξ_ξ dξ`, with `Ξ_ξ = Ξ(ψ_{1,ξ}, ψ_{2,ξ})` for moduli `μ ≡ κd (mod 4d)` of size `dK`. -/
theorem IsGood.sum_psi0_ek_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) {K : ℝ} (hK : 0 < K) {κ : ℕ} (hκ : κ = 1 ∨ κ = 3) :
    ((∑ k ∈ (Finset.Icc 1 ⌊2 * K⌋₊).filter (fun k => k % 4 = κ),
        Dyadic.psi0 (k / K) * P.ek F W d x k : ℝ) : ℂ) =
      ∫ ξ : ℝ, 𝓕 (P.fK W x K) ξ *
        Xi P.Enat (P.Hnat d) d κ (P.Xpar d x) (d * K) (psiOne ξ) (P.psiTwo F d x ξ) := by
  have hd0 : 0 < d := hd.prime.pos
  have hd0' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [Complex.ofReal_sum]
  rw [Finset.sum_congr rfl (fun k _ => hd.psi0_mul_ek_eq F W hx hK k)]
  rw [← integral_finsetSum _ (fun k _ => hd.integrable_ekIntegrand F W hx K k)]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold Xi
  rw [sum_moduli_eq hd0 (by omega) hK, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk4 : k % 4 = κ := (Finset.mem_filter.1 hk).2
  have hkodd : k % 2 = 1 := by omega
  rw [← hd.rho_eq_rhoEH_mul hkodd]
  unfold ekIntegrand
  have h1 : ((d * k : ℕ) : ℝ) / (d * K) = k / K := by
    push_cast; field_simp
  rw [h1]
  push_cast
  ring

end PatternData

end Triples
