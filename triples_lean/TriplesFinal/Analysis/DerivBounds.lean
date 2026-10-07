import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Bounds for iterated derivatives

General tools used for the derivative bounds in hypothesis (H) of §6:

* the Leibniz bound and the Faà di Bruno bound on open subsets of `ℝ`
  (`norm_iteratedDeriv_mul_le_of_isOpen`, `norm_iteratedDeriv_comp_le_of_isOpen`);
* the derivatives of `log` and of `u ↦ e^{cui}`;
* smooth functions with compact support have bounded derivatives;
* **the phase functions** `u ↦ g(u) e^{i c log u}` for `g` smooth and supported in `[a, b]`,
  `0 < a`: they are smooth and `‖D^n‖ ≤ C_n (1 + |c|)^n` uniformly in `c`
  (`exists_bound_phaseFn`).

These are used in the proof of Lemma 7.3 (`Asymptotic/ErrorTerm.lean`).
-/

namespace Triples

open scoped ContDiff Nat
open Complex

/-- **Leibniz bound** on an open set. -/
theorem norm_iteratedDeriv_mul_le_of_isOpen {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : ℝ} (hx : x ∈ U) (n : ℕ) :
    ‖iteratedDeriv n (fun y => f y * g y) x‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedDeriv i f x‖ * ‖iteratedDeriv (n - i) g x‖ := by
  have hs : UniqueDiffOn ℝ U := hU.uniqueDiffOn
  have key := norm_iteratedFDerivWithin_mul_le hf hg hs hx (n := n) (by exact_mod_cast le_top)
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen hU hx] at key
  refine key.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen hU hx, iteratedDerivWithin_of_isOpen hU hx]

/-- **Faà di Bruno bound** on open sets. -/
theorem norm_iteratedDeriv_comp_le_of_isOpen {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    {g : ℝ → ℂ} {f : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g V) (hf : ContDiffOn ℝ ∞ f U)
    (hfUV : Set.MapsTo f U V) {x : ℝ} (hx : x ∈ U) (n : ℕ) {C D : ℝ}
    (hC : ∀ i ≤ n, ‖iteratedDeriv i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedDeriv i f x‖ ≤ D ^ i) :
    ‖iteratedDeriv n (g ∘ f) x‖ ≤ n ! * C * D ^ n := by
  have key := norm_iteratedFDerivWithin_comp_le hg hf (n := n) (by exact_mod_cast le_top)
    hV.uniqueDiffOn hU.uniqueDiffOn hfUV hx (C := C) (D := D)
    (fun i hi => by
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen hV (hfUV hx)]
      exact hC i hi)
    (fun i hi hin => by
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen hU hx]
      exact hD i hi hin)
  rwa [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_of_isOpen hU hx] at key

/-- The derivatives of `log`: `log^(n+1)(x) = (-1)^n n! x^(-1-n)`. -/
theorem iteratedDeriv_succ_log (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) Real.log x = (-1) ^ n * n ! * x ^ (-1 - n : ℤ) := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]

theorem norm_iteratedDeriv_succ_log (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (n + 1) Real.log x‖ = n ! / x ^ (n + 1) := by
  rw [iteratedDeriv_succ_log, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, norm_zpow, Real.norm_of_nonneg hx.le]
  rw [show (-1 - n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    div_eq_mul_inv]

/-- The derivatives of `u ↦ e^{c u i}`. -/
theorem iteratedDeriv_cexp_mul_I (n : ℕ) (c : ℝ) :
    iteratedDeriv n (fun u : ℝ => Complex.exp (c * u * I)) =
      fun u : ℝ => (c * I) ^ n * Complex.exp (c * u * I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext u
    have h1 : HasDerivAt (fun u : ℝ => (c * u * I : ℂ)) (c * I) u := by
      have := ((hasDerivAt_id (u : ℝ)).ofReal_comp).const_mul (c : ℂ)
      have := this.mul_const I
      simpa using this
    have h2 := (h1.cexp).const_mul ((c * I) ^ n)
    rw [h2.deriv]
    ring

theorem norm_iteratedDeriv_cexp_mul_I (n : ℕ) (c u : ℝ) :
    ‖iteratedDeriv n (fun u : ℝ => Complex.exp (c * u * I)) u‖ = |c| ^ n := by
  rw [iteratedDeriv_cexp_mul_I, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  have : ‖Complex.exp (c * u * I)‖ = 1 := by
    rw [show (c * u * I : ℂ) = ((c * u : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, mul_one]

/-- Iterated derivatives vanish outside the topological support. -/
theorem iteratedDeriv_eq_zero_of_notMem_tsupport {f : ℝ → ℂ} {x : ℝ} (hx : x ∉ tsupport f)
    (n : ℕ) : iteratedDeriv n f x = 0 := by
  have h : f =ᶠ[nhds x] fun _ => 0 := by
    have := (notMem_tsupport_iff_eventuallyEq).1 hx
    exact this
  rw [Filter.EventuallyEq.iteratedDeriv_eq n h]
  simp

/-- A smooth function with compact support has bounded iterated derivatives. -/
theorem exists_bound_iteratedDeriv {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, ‖iteratedDeriv n h u‖ ≤ M := by
  have hcont : Continuous (iteratedDeriv n h) :=
    hh.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (iteratedDeriv n h) := by
    apply hc.mono'
    intro u hu
    by_contra hu'
    exact hu (iteratedDeriv_eq_zero_of_notMem_tsupport hu' n)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  exact ⟨max M 0, le_max_right _ _, fun u => (hM u).trans (le_max_left _ _)⟩

/-- A uniform bound for the first `n + 1` derivatives. -/
theorem exists_bound_iteratedDeriv_le {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ n, ∀ u, ‖iteratedDeriv i h u‖ ≤ M := by
  choose M hM0 hM using fun i => exists_bound_iteratedDeriv hh hc i
  refine ⟨∑ i ∈ Finset.range (n + 1), M i, Finset.sum_nonneg (fun i _ => hM0 i), ?_⟩
  intro i hi u
  calc ‖iteratedDeriv i h u‖ ≤ M i := hM i u
    _ ≤ ∑ i ∈ Finset.range (n + 1), M i :=
      Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))

/-- `u ↦ g(u) e^{i c log u}`. -/
noncomputable def phaseFn (g : ℝ → ℂ) (c : ℝ) (u : ℝ) : ℂ :=
  g u * Complex.exp (c * Real.log u * I)

theorem tsupport_subset_Icc_of_support {g : ℝ → ℂ} {a b : ℝ} (hsupp : ∀ u, g u ≠ 0 → a ≤ u ∧ u ≤ b) :
    tsupport g ⊆ Set.Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  exact hsupp u hu

theorem contDiffAt_cexp_log {c u : ℝ} (hu : u ≠ 0) :
    ContDiffAt ℝ ∞ (fun u : ℝ => Complex.exp (c * Real.log u * I)) u := by
  have h1 : ContDiffAt ℝ ∞ Real.log u := Real.contDiffAt_log.2 hu
  have h2 : ContDiffAt ℝ ∞ (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) u :=
    ofRealCLM.contDiff.contDiffAt.comp u h1
  have h3 : ContDiffAt ℝ ∞ (fun u : ℝ => (c : ℂ) * Real.log u * I) u :=
    (contDiffAt_const.mul h2).mul contDiffAt_const
  exact h3.cexp

theorem contDiff_phaseFn {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ u, g u ≠ 0 → a ≤ u ∧ u ≤ b) (c : ℝ) : ContDiff ℝ ∞ (phaseFn g c) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport g
  · have hu0 : 0 < u := lt_of_lt_of_le ha (tsupport_subset_Icc_of_support hsupp hu).1
    exact hg.contDiffAt.mul (contDiffAt_cexp_log hu0.ne')
  · have h : g =ᶠ[nhds u] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hu
    have h' : phaseFn g c =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [h] with y hy
      simp [phaseFn, hy]
    exact contDiffAt_const.congr_of_eventuallyEq h'

theorem tsupport_phaseFn_subset (g : ℝ → ℂ) (c : ℝ) : tsupport (phaseFn g c) ⊆ tsupport g := by
  apply closure_mono
  intro u hu
  simp only [Function.mem_support, phaseFn] at hu ⊢
  exact left_ne_zero_of_mul hu

/-- The derivatives of `u ↦ e^{i c log u}` for `u ≥ a > 0`. -/
theorem norm_iteratedDeriv_cexp_log_le {a : ℝ} (ha : 0 < a) (c : ℝ) {u : ℝ} (hu : a ≤ u)
    (j : ℕ) :
    ‖iteratedDeriv j (fun u : ℝ => Complex.exp (c * Real.log u * I)) u‖ ≤
      j ! * (1 + |c|) ^ j * ((j + 1) / a) ^ j := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hu
  have hcomp : (fun u : ℝ => Complex.exp (c * Real.log u * I)) =
      (fun y : ℝ => Complex.exp (c * y * I)) ∘ Real.log := rfl
  rw [hcomp]
  apply norm_iteratedDeriv_comp_le_of_isOpen (U := Set.Ioi 0) (V := Set.univ) isOpen_Ioi
    isOpen_univ _ _ (Set.mapsTo_univ _ _) hu0
  · intro i hi
    rw [norm_iteratedDeriv_cexp_mul_I]
    calc |c| ^ i ≤ (1 + |c|) ^ i := pow_le_pow_left₀ (abs_nonneg c) (by linarith) i
      _ ≤ (1 + |c|) ^ j := pow_le_pow_right₀ (by linarith [abs_nonneg c]) hi
  · intro i hi hij
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [norm_iteratedDeriv_succ_log k hu0, div_pow]
    have hk : (k ! : ℝ) ≤ (j + 1 : ℝ) ^ (k + 1) := by
      have h1 : (k ! : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
      have h2 : (k : ℝ) ^ k ≤ (j + 1 : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) (by norm_cast; omega) k
      have h3 : (j + 1 : ℝ) ^ k ≤ (j + 1 : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]) (by omega)
      linarith
    have hau : a ^ (k + 1) ≤ u ^ (k + 1) := pow_le_pow_left₀ ha.le hu _
    calc (k ! : ℝ) / u ^ (k + 1) ≤ (j + 1 : ℝ) ^ (k + 1) / a ^ (k + 1) := by
          apply div_le_div₀ (by positivity) hk (by positivity) hau
      _ = _ := rfl
  · have h1 : ContDiff ℝ ∞ (fun y : ℝ => (c : ℂ) * y * I) :=
      (contDiff_const.mul ofRealCLM.contDiff).mul contDiff_const
    exact h1.cexp.contDiffOn
  · intro y hy
    exact (Real.contDiffAt_log.2 (ne_of_gt hy)).contDiffWithinAt

theorem contDiffOn_cexp_log (c : ℝ) :
    ContDiffOn ℝ ∞ (fun u : ℝ => Complex.exp (c * Real.log u * I)) (Set.Ioi 0) :=
  fun _ hu => (contDiffAt_cexp_log (ne_of_gt hu)).contDiffWithinAt

theorem hasCompactSupport_of_support {g : ℝ → ℂ} {a b : ℝ}
    (hsupp : ∀ u, g u ≠ 0 → a ≤ u ∧ u ≤ b) : HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) (fun u hu => by
    by_contra h
    exact hu (hsupp u h))

/-- **Derivative bound** for `u ↦ g(u) e^{i c log u}`: `‖D^n‖ ≤ C (1 + |c|)^n`, uniformly in
`c`. -/
theorem exists_bound_phaseFn {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ u, g u ≠ 0 → a ≤ u ∧ u ≤ b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c u : ℝ, ‖iteratedDeriv n (phaseFn g c) u‖ ≤ C * (1 + |c|) ^ n := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedDeriv_le hg (hasCompactSupport_of_support hsupp) n
  set C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M *
    ((n - i) ! * ((((n - i : ℕ) : ℝ) + 1) / a) ^ (n - i)) with hC
  refine ⟨C, by positivity, ?_⟩
  intro c u
  have hc1 : 1 ≤ 1 + |c| := by linarith [abs_nonneg c]
  by_cases hu : u ∈ tsupport g
  · have hu' := tsupport_subset_Icc_of_support hsupp hu
    have hu0 : 0 < u := lt_of_lt_of_le ha hu'.1
    have hL := norm_iteratedDeriv_mul_le_of_isOpen isOpen_Ioi hg.contDiffOn
      (contDiffOn_cexp_log c) (Set.mem_Ioi.2 hu0) n
    calc ‖iteratedDeriv n (phaseFn g c) u‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedDeriv i g u‖ *
          ‖iteratedDeriv (n - i) (fun u : ℝ => Complex.exp (c * Real.log u * I)) u‖ := hL
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M *
          ((n - i) ! * ((((n - i : ℕ) : ℝ) + 1) / a) ^ (n - i) * (1 + |c|) ^ n) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 := hM i hi' u
          have h2 := norm_iteratedDeriv_cexp_log_le ha c hu'.1 (n - i)
          have h3 : (1 + |c|) ^ (n - i) ≤ (1 + |c|) ^ n := pow_le_pow_right₀ hc1 (by omega)
          have h4 : ((n - i) ! : ℝ) * (1 + |c|) ^ (n - i) * ((((n - i : ℕ) : ℝ) + 1) / a) ^ (n - i)
              ≤ (n - i) ! * ((((n - i : ℕ) : ℝ) + 1) / a) ^ (n - i) * (1 + |c|) ^ n := by
            have : 0 ≤ ((n - i) ! : ℝ) * ((((n - i : ℕ) : ℝ) + 1) / a) ^ (n - i) := by positivity
            nlinarith
          gcongr
          exact h2.trans h4
      _ = C * (1 + |c|) ^ n := by
          rw [hC, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
  · rw [iteratedDeriv_eq_zero_of_notMem_tsupport
      (fun h => hu (tsupport_phaseFn_subset g c h)) n, norm_zero]
    positivity

end Triples
