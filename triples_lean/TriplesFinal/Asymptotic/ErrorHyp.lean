import TriplesFinal.Asymptotic.Separation

/-!
# Hypothesis (H) for the sums `Ξ_ξ` (proof of Lemma 7.3)

The weights `ψ_{1,ξ}` and `ψ_{2,ξ}` of `Separation.lean` satisfy hypothesis (H) of §6 with
`Δ = 1 + |ξ|`, moduli of size `dK` (for `1/2 ≤ K ≤ k₊`) and constants `C_ν` that depend only on
`ψ₀` and `F`:

* `‖ψ_{1,ξ}^(ν)‖ ≤ C_ν (1 + |ξ|)^ν` (`exists_bound_psiOne`, from the phase bound);
* `ψ_{2,ξ} = G_ξ ∘ Q` with `Q(s) = αs² + (1 - α)`, `0 < α ≤ 1`, so that by Faà di Bruno
  `‖ψ_{2,ξ}^(ν)(s)‖ ≤ ν! C_ν (1 + |ξ|)^ν 2^ν` for `|s| ≤ 1`, and `ψ_{2,ξ}` vanishes near
  `|s| > 1` (`exists_bound_psiTwo`);
* `X ≥ N^(1/2)` and `1 ≤ dK ≤ dk₊ ≤ qX` (`IsGood.kplus_le_X`), and the arithmetic conditions on
  `E, H, d` from §4 (`IsGood.hypH`).

Paper: §7.3, proof of Lemma 7.3 ("The hypotheses (H) hold, with `K` replaced by `dK`").
-/

namespace Triples

open MeasureTheory Complex
open scoped ContDiff Nat

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- The derivatives of `s ↦ As² + B` for `|s| ≤ 1`, `0 ≤ A ≤ 1`. -/
theorem norm_iteratedDeriv_quadratic_le {A B : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) {s : ℝ}
    (hs : |s| ≤ 1) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedDeriv i (fun s : ℝ => A * s ^ 2 + B) s‖ ≤ 2 ^ i := by
  have hd1 : deriv (fun s : ℝ => A * s ^ 2 + B) = fun s => 2 * A * s := by
    ext s
    have : HasDerivAt (fun s : ℝ => A * s ^ 2 + B) (A * (2 * s)) s := by
      have := ((hasDerivAt_pow 2 s).const_mul A).add_const B
      simpa using this
    rw [this.deriv]; ring
  have hd2 : deriv (fun s : ℝ => 2 * A * s) = fun _ => 2 * A := by
    ext s
    have : HasDerivAt (fun s : ℝ => 2 * A * s) (2 * A * 1) s := (hasDerivAt_id s).const_mul _
    rw [this.deriv]; ring
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [iteratedDeriv_succ', hd1]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [iteratedDeriv_zero, Real.norm_eq_abs, zero_add, pow_one]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * A)]
    nlinarith [abs_nonneg s]
  · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
    rw [iteratedDeriv_succ', hd2, iteratedDeriv_const]
    have h2 : (2 : ℝ) ≤ 2 ^ (l + 1 + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (l + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
    · simp only [norm_zero]; positivity

theorem contDiff_psiOne (ξ : ℝ) : ContDiff ℝ ∞ (psiOne ξ) :=
  contDiff_phaseFn (ofRealCLM.contDiff.comp Dyadic.contDiff_psi0) (a := 1) (b := 2) one_pos
    (fun u h => Dyadic.psi0_support (fun h' => h (by simp [h']))) _

theorem contDiff_Gphase (F : Cutoff) (ξ : ℝ) : ContDiff ℝ ∞ (Gphase F ξ) :=
  contDiff_phaseFn (ofRealCLM.contDiff.comp F.smooth) (a := 1 / 2) (b := 1) (by norm_num)
    (fun u h => F.support u (fun h' => h (by simp [h']))) _

theorem psiOne_support {ξ t : ℝ} (h : psiOne ξ t ≠ 0) : 1 ≤ t ∧ t ≤ 2 := by
  apply Dyadic.psi0_support
  intro h'
  apply h
  simp [psiOne, phaseFn, h']

/-- `ψ_{2,ξ}(s) = G_ξ(αs² + (1 - α))`. -/
theorem IsGood.psiTwo_eq {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx : 33 * (d : ℝ) ≤ x) (ξ : ℝ) :
    P.psiTwo F d x ξ = fun s => Gphase F ξ
      ((2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x)) * s ^ 2 +
        (1 - 2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x))) := by
  ext s
  unfold psiTwo
  rw [hd.Treal_Xpar_mul hx s]

theorem IsGood.contDiff_psiTwo {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx : 33 * (d : ℝ) ≤ x) (ξ : ℝ) : ContDiff ℝ ∞ (P.psiTwo F d x ξ) := by
  rw [hd.psiTwo_eq F hx ξ]
  exact (contDiff_Gphase F ξ).comp ((contDiff_const.mul (contDiff_id.pow 2)).add contDiff_const)

theorem IsGood.psiTwo_support {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ}
    (hx : 33 * (d : ℝ) ≤ x) {ξ t : ℝ} (h : P.psiTwo F d x ξ t ≠ 0) : -1 ≤ t ∧ t ≤ 1 := by
  have hX0 := (hd.Xpar_spec hx).1
  have hx0 : 0 < x := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
    linarith
  have hF : F.F (P.Treal d (P.Xpar d x * t) / x) ≠ 0 := by
    intro h'
    apply h
    simp [psiTwo, Gphase, phaseFn, h']
  obtain ⟨-, hT⟩ := Treal_mem_of_F_ne_zero F hx0 hF
  have habs := hd.abs_le_Xpar hx hT
  rw [abs_mul, abs_of_pos hX0] at habs
  have : |t| ≤ 1 := by
    by_contra h'
    push Not at h'
    nlinarith
  exact abs_le.1 this

/-- The derivative bounds for `ψ_{1,ξ}`. -/
theorem exists_bound_psiOne (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ t : ℝ, ‖iteratedDeriv n (psiOne ξ) t‖ ≤ C * (1 + |ξ|) ^ n := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_phaseFn (ofRealCLM.contDiff.comp Dyadic.contDiff_psi0)
    (a := 1) (b := 2) one_pos (fun u h => Dyadic.psi0_support (fun h' => h (by simp [h']))) n
  refine ⟨C * (2 * Real.pi) ^ n, by positivity, fun ξ t => ?_⟩
  have h := hC (2 * Real.pi * ξ) t
  have h1 : 1 + |2 * Real.pi * ξ| ≤ 2 * Real.pi * (1 + |ξ|) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.two_le_pi, abs_nonneg ξ]
  calc ‖iteratedDeriv n (psiOne ξ) t‖ ≤ C * (1 + |2 * Real.pi * ξ|) ^ n := h
    _ ≤ C * (2 * Real.pi * (1 + |ξ|)) ^ n := by gcongr
    _ = C * (2 * Real.pi) ^ n * (1 + |ξ|) ^ n := by rw [mul_pow]; ring

/-- The derivative bounds for `G_ξ`. -/
theorem exists_bound_Gphase (F : Cutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ ξ u : ℝ, ‖iteratedDeriv i (Gphase F ξ) u‖ ≤
      C * (1 + |ξ|) ^ n := by
  choose C hC0 hC using fun i => exists_bound_phaseFn (ofRealCLM.contDiff.comp F.smooth)
    (a := 1 / 2) (b := 1) (by norm_num) (fun u h => F.support u (fun h' => h (by simp [h']))) i
  refine ⟨(∑ i ∈ Finset.range (n + 1), C i) * Real.pi ^ n,
    by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (n + 1)) => hC0 i); positivity,
    fun i hi ξ u => ?_⟩
  have h := hC i (-(Real.pi * ξ)) u
  have h1 : 1 + |-(Real.pi * ξ)| ≤ Real.pi * (1 + |ξ|) := by
    rw [abs_neg, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.two_le_pi, abs_nonneg ξ]
  have hCi : C i ≤ ∑ i ∈ Finset.range (n + 1), C i :=
    Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.2 (by omega))
  have hpow : (1 + |-(Real.pi * ξ)|) ^ i ≤ (Real.pi * (1 + |ξ|)) ^ n := by
    calc (1 + |-(Real.pi * ξ)|) ^ i ≤ (Real.pi * (1 + |ξ|)) ^ i := by
          gcongr
      _ ≤ (Real.pi * (1 + |ξ|)) ^ n := by
          apply pow_le_pow_right₀ _ hi
          nlinarith [Real.two_le_pi, abs_nonneg ξ]
  calc ‖iteratedDeriv i (Gphase F ξ) u‖ ≤ C i * (1 + |-(Real.pi * ξ)|) ^ i := h
    _ ≤ (∑ i ∈ Finset.range (n + 1), C i) * (Real.pi * (1 + |ξ|)) ^ n := by
        gcongr
        exact Finset.sum_nonneg (fun j _ => hC0 j)
    _ = (∑ i ∈ Finset.range (n + 1), C i) * Real.pi ^ n * (1 + |ξ|) ^ n := by
        rw [mul_pow]; ring

/-- The derivative bounds for `ψ_{2,ξ}`, uniformly in `d`, `x`, `ξ`. -/
theorem exists_bound_psiTwo (F : Cutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ), P.IsGood d → ∀ x : ℝ, 33 * (d : ℝ) ≤ x → ∀ ξ t : ℝ,
      ‖iteratedDeriv n (P.psiTwo F d x ξ) t‖ ≤ C * (1 + |ξ|) ^ n := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_Gphase F n
  refine ⟨n ! * C * 2 ^ n, by positivity, fun d hd x hx ξ t => ?_⟩
  by_cases ht : |t| ≤ 1
  · rw [hd.psiTwo_eq F hx ξ]
    obtain ⟨hα0, hα1⟩ := hd.alpha_mem hx
    set α := 2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x)
    have hcomp : (fun s => Gphase F ξ (α * s ^ 2 + (1 - α))) =
        Gphase F ξ ∘ (fun s : ℝ => α * s ^ 2 + (1 - α)) := rfl
    rw [hcomp]
    have hQ : ContDiff ℝ ∞ (fun s : ℝ => α * s ^ 2 + (1 - α)) := by fun_prop
    have key := norm_iteratedFDeriv_comp_le (contDiff_Gphase F ξ) hQ (n := n)
      (by exact_mod_cast le_top) t (C := C * (1 + |ξ|) ^ n) (D := 2)
      (fun i hi => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hC i hi ξ _)
      (fun i hi hin => by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_quadratic_le hα0.le hα1 ht hi)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at key
    calc _ ≤ n ! * (C * (1 + |ξ|) ^ n) * 2 ^ n := key
      _ = n ! * C * 2 ^ n * (1 + |ξ|) ^ n := by ring
  · rw [iteratedDeriv_eq_zero_of_notMem_tsupport, norm_zero]
    · positivity
    · intro h
      have := tsupport_subset_Icc_of_support (fun u h => hd.psiTwo_support F hx h) h
      exact ht (abs_le.2 this)

theorem two_rpow_v_sq (P : PatternData a b) :
    ((2 : ℝ) ^ (((P.v : ℝ) - 2) / 2)) ^ 2 = 2 ^ (P.v - 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1
  rw [Nat.cast_sub P.hv]
  push_cast
  ring

/-- `k₊ ≤ 4EX`, so that moduli of size `dK ≤ dk₊` are at most `qX`. -/
theorem IsGood.kplus_le_X {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) :
    P.kplus x ≤ 4 * P.E * P.Xpar d x := by
  obtain ⟨hX0, -, -, hXl, -⟩ := hd.Xpar_spec hx
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  have hx0 : 0 < x := by linarith
  have hE0 := P.E_real_pos
  have hE4 : (4 : ℝ) ≤ P.E := by rcases P.E_real_eq with h | h <;> linarith
  set c := (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) with hc
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = 2 ^ (P.v - 2) := P.two_rpow_v_sq
  have hc2pos : (0 : ℝ) < 2 ^ (P.v - 2) := by positivity
  unfold kplus
  rw [← hc, div_le_iff₀ hc0]
  have h1 : (2 * Real.sqrt x) ^ 2 ≤ (4 * P.E * P.Xpar d x * c) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx0.le, mul_pow, mul_pow, hc2]
    have h3 : (d : ℝ) * x / 2 ^ (P.v - 2) / (2 * P.E) * (2 ^ (P.v - 2) * P.E) = d * x / 2 := by
      field_simp
    have hEd : (4 : ℝ) ≤ P.E * d := by nlinarith
    have h7 : 4 * x ≤ 8 * P.E * d * x := by nlinarith
    have h5 : (d : ℝ) * x / 2 ^ (P.v - 2) / (2 * P.E) * (16 * P.E ^ 2 * 2 ^ (P.v - 2)) ≤
        P.Xpar d x ^ 2 * (16 * P.E ^ 2 * 2 ^ (P.v - 2)) := by gcongr
    have h6 : (d : ℝ) * x / 2 ^ (P.v - 2) / (2 * P.E) * (16 * P.E ^ 2 * 2 ^ (P.v - 2)) =
        8 * P.E * d * x := by field_simp; ring
    nlinarith
  have h2 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  linarith

/-- **Hypothesis (H)** for `Ξ_ξ`. -/
theorem IsGood.hypH {d : ℕ} (hd : P.IsGood d) (F : Cutoff) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x)
    {κ : ℕ} (hκ : κ = 1 ∨ κ = 3) {K : ℝ} (hK1 : 1 / 2 ≤ K) (hKk : K ≤ P.kplus x) (ξ : ℝ)
    (Cν : ℕ → ℝ) (hC1 : ∀ ν t, ‖iteratedDeriv ν (psiOne ξ) t‖ ≤ Cν ν * (1 + |ξ|) ^ ν)
    (hC2 : ∀ ν t, ‖iteratedDeriv ν (P.psiTwo F d x ξ) t‖ ≤ Cν ν * (1 + |ξ|) ^ ν) :
    HypH Cν P.Enat (P.Hnat d) d κ (1 + |ξ|) (P.Xpar d x) (d * K) (psiOne ξ)
      (P.psiTwo F d x ξ) := by
  have hHc := hd.Hnat_cast
  have hHpos := hd.H_pos
  have hd4 := hd.emod_four
  have hd2 := hd.prime.two_le
  obtain ⟨hX0, -, hEH, -, -⟩ := hd.Xpar_spec hx
  refine ⟨P.Enat_eq, ?_, ?_, hd.prime, ?_, ?_, ?_, ?_, hκ, ?_, ?_, ?_, ?_,
    contDiff_psiOne ξ, hd.contDiff_psiTwo F hx ξ, fun t h => psiOne_support h,
    fun t h => hd.psiTwo_support F hx h, hC1, hC2⟩
  · omega
  · have := hd.H_odd; omega
  · omega
  · intro h
    apply hd.not_dvd_H
    rw [← hHc]
    exact_mod_cast h
  · rintro ⟨s, hs⟩
    apply hd.N_not_sq
    refine ⟨s, ?_⟩
    unfold N
    rw [← P.Enat_cast, ← hHc]
    exact_mod_cast hs
  · rintro ⟨s, hs⟩
    apply hd.N_not_three_sq
    refine ⟨s, ?_⟩
    unfold N
    rw [← P.Enat_cast, ← hHc]
    exact_mod_cast hs
  · linarith [abs_nonneg ξ]
  · push_cast
    rw [P.Enat_real, hd.Hnat_real]
    calc Real.sqrt ((P.E : ℝ) * P.H d) ≤ Real.sqrt (P.Xpar d x ^ 2) := Real.sqrt_le_sqrt hEH
      _ = P.Xpar d x := Real.sqrt_sq hX0.le
  · have : (5 : ℝ) ≤ d := by
      have : 5 ≤ d := by omega
      exact_mod_cast this
    nlinarith
  · push_cast
    rw [P.Enat_real]
    have h1 := hd.kplus_le_X hx
    have hd0 : (0 : ℝ) ≤ d := d.cast_nonneg
    nlinarith

end PatternData

end Triples
