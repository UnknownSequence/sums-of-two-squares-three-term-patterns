import TriplesFinal.Asymptotic.ErrorHyp
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The error term from a Type I estimate (proof of Lemma 7.3)

* **The dyadic decomposition** (`IsGood.Ed_eq_sum_EK`): with `K_i = 2^(i/2)`, `-1 ≤ i ≤ ⌈log₂ x⌉ + 2`,
  `ℰ_d = 8 ∑_i (ℰ(K_i, 1) - ℰ(K_i, 3))`, where `ℰ(K, κ) = ∑_{k ≡ κ (4)} ψ₀(k/K) e(k)`. Every odd
  `k < k₊ ≤ 2√x` is covered by the partition of unity, and `e(k) = 0` for `k ≥ k₊`.
* `ℰ(K, κ) = 0` for `K ≥ k₊`.
* **Lemma 7.3 from a Type I estimate** (`abs_Ed_le_of_typeI`): if the sums `Ξ` satisfy
  `‖Ξ‖ ≤ C Δ^c G(E, H, d, X, K)` under (H), then `|ℰ_d| ≤ C' · #{i} · B` whenever
  `0 ≤ G(E, H_d, d, X, dK) ≤ B` for `1/2 ≤ K ≤ k₊`. For each `K`, by the separation of
  variables, `|ℰ(K, κ)| ≤ ∫ |𝓕f(ξ)| ‖Ξ_ξ‖ dξ ≤ C B ∫ A_n (1 + |ξ|)^(c - n) dξ` with
  `n = ⌈c⌉ + 2`.

Paper: §7.3, proof of Lemma 7.3.
-/

namespace Triples

open MeasureTheory Complex
open scoped FourierTransform

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- `K_i = 2^(i/2)`. -/
noncomputable def Kdy (i : ℤ) : ℝ := (2 : ℝ) ^ ((i : ℝ) / 2)

theorem Kdy_pos (i : ℤ) : 0 < Kdy i := by unfold Kdy; positivity

/-- The dyadic indices `-1 ≤ i ≤ ⌈log₂ x⌉ + 2`. -/
noncomputable def dyIdx (x : ℝ) : Finset ℤ := Finset.Icc (-1) (⌈Real.logb 2 x⌉ + 2)

variable (P) in
/-- `ℰ(K, κ) = ∑_{k ≡ κ (4), 1 ≤ k ≤ 2K} ψ₀(k/K) e(k)`. -/
noncomputable def EK (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x K : ℝ) (κ : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 ⌊2 * K⌋₊).filter (fun k => k % 4 = κ), Dyadic.psi0 (k / K) * P.ek F W d x k

/-- `ψ₀(t) ≠ 0` implies `1 < t < 2`. -/
theorem psi0_ne_zero {t : ℝ} (h : Dyadic.psi0 t ≠ 0) : 1 < t ∧ t < 2 := by
  constructor
  · by_contra h'; exact h (Dyadic.psi0_eq_zero_of_le (not_lt.1 h'))
  · by_contra h'; exact h (Dyadic.psi0_eq_zero_of_ge (not_lt.1 h'))

theorem Kdy_le_half {i : ℤ} (hi : i ≤ -2) : Kdy i ≤ 1 / 2 := by
  unfold Kdy
  calc (2 : ℝ) ^ ((i : ℝ) / 2) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (i : ℝ) ≤ -2 := by exact_mod_cast hi
        linarith
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem two_sqrt_lt_Kdy {x : ℝ} (hx : 0 < x) {i : ℤ} (hi : ⌈Real.logb 2 x⌉ + 3 ≤ i) :
    2 * Real.sqrt x < Kdy i := by
  unfold Kdy
  have h1 : Real.logb 2 x + 3 ≤ (i : ℝ) := by
    have := Int.le_ceil (Real.logb 2 x)
    have : ((⌈Real.logb 2 x⌉ + 3 : ℤ) : ℝ) ≤ i := by exact_mod_cast hi
    push_cast at this
    linarith
  have h2 : Real.sqrt x = (2 : ℝ) ^ (Real.logb 2 x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hx]
    rw [Real.logb_rpow (by norm_num) (by norm_num), ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [h2]
  calc 2 * (2 : ℝ) ^ (Real.logb 2 x / 2) = (2 : ℝ) ^ (Real.logb 2 x / 2 + 1) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
    _ < (2 : ℝ) ^ ((i : ℝ) / 2) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        linarith

/-- If `1 ≤ k < 2√x` and `ψ₀(k/K_i) ≠ 0`, then `i` is a dyadic index. -/
theorem mem_dyIdx {x : ℝ} (hx : 0 < x) {k : ℕ} (hk1 : 1 ≤ k) (hkx : (k : ℝ) < 2 * Real.sqrt x)
    {i : ℤ} (h : Dyadic.psi0 (k / Kdy i) ≠ 0) : i ∈ dyIdx x := by
  obtain ⟨h1, h2⟩ := psi0_ne_zero h
  have hK := Kdy_pos i
  rw [one_lt_div hK] at h1
  rw [div_lt_iff₀ hK] at h2
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  simp only [dyIdx, Finset.mem_Icc]
  constructor
  · by_contra hi
    have := Kdy_le_half (i := i) (by omega)
    linarith
  · by_contra hi
    have := two_sqrt_lt_Kdy hx (i := i) (by omega)
    linarith

/-- `∑_{i ∈ dyIdx x} ψ₀(k/K_i) = 1` for `1 ≤ k < 2√x`. -/
theorem sum_psi0_dyIdx {x : ℝ} (hx : 0 < x) {k : ℕ} (hk1 : 1 ≤ k)
    (hkx : (k : ℝ) < 2 * Real.sqrt x) : ∑ i ∈ dyIdx x, Dyadic.psi0 (k / Kdy i) = 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have h1 := Dyadic.hasSum_psi0 hk0
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ)
    (f := fun i : ℤ => Dyadic.psi0 (k / Kdy i)) (s := dyIdx x)
    (fun i hi => by
      by_contra h
      exact hi (mem_dyIdx hx hk1 hkx h))
  exact h2.unique h1

/-- On `kRange x` (odd `k`), the sum over `k ≡ κ (mod 4)` is `ℰ(K, κ)`. -/
theorem IsGood.sum_kRange_filter_eq_EK {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 0 < x) {K : ℝ} (hK : 0 < K) {κ : ℕ}
    (hκ : κ = 1 ∨ κ = 3) :
    ∑ k ∈ (kRange x).filter (fun k => k % 4 = κ), Dyadic.psi0 (k / K) * P.ek F W d x k =
      P.EK F W d x K κ := by
  set A := (kRange x).filter (fun k => k % 4 = κ)
  set B := (Finset.Icc 1 ⌊2 * K⌋₊).filter (fun k => k % 4 = κ)
  have hA : ∑ k ∈ A ∩ B, Dyadic.psi0 (k / K) * P.ek F W d x k =
      ∑ k ∈ A, Dyadic.psi0 (k / K) * P.ek F W d x k := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hkA hkAB
    have hkB : k ∉ B := fun h => hkAB (Finset.mem_inter.2 ⟨hkA, h⟩)
    simp only [A, kRange, Finset.mem_filter, Finset.mem_range] at hkA
    simp only [B, Finset.mem_filter, Finset.mem_Icc, not_and_or, not_le] at hkB
    have hk2 : ⌊2 * K⌋₊ < k := by
      rcases hkB with (h | h) | h
      · omega
      · exact h
      · exact absurd hkA.2 h
    have : 2 * K ≤ k := by
      have := Nat.lt_floor_add_one (2 * K)
      have h' : ((⌊2 * K⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk2
      push_cast at h'
      linarith
    rw [Dyadic.psi0_eq_zero_of_ge (by rw [le_div_iff₀ hK]; linarith), zero_mul]
  have hB : ∑ k ∈ A ∩ B, Dyadic.psi0 (k / K) * P.ek F W d x k =
      ∑ k ∈ B, Dyadic.psi0 (k / K) * P.ek F W d x k := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro k hkB hkAB
    have hkA : k ∉ A := fun h => hkAB (Finset.mem_inter.2 ⟨h, hkB⟩)
    simp only [B, Finset.mem_filter] at hkB
    have hkodd : k % 2 = 1 := by omega
    simp only [A, kRange, Finset.mem_filter, Finset.mem_range, not_and_or, not_lt] at hkA
    have hk : ⌈2 * Real.sqrt x⌉₊ + 1 ≤ k := by
      rcases hkA with h | h
      · rcases h with h | h
        · exact h
        · exact absurd hkodd h
      · exact absurd hkB.2 h
    have hkx : P.kplus x ≤ k := by
      have h1 := Nat.le_ceil (2 * Real.sqrt x)
      have h2 : ((⌈2 * Real.sqrt x⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2
      linarith [P.kplus_le x]
    rw [hd.ek_eq_zero_of_kplus_le F W hx hkx, mul_zero]
  rw [← hA, hB]
  rfl

/-- **The dyadic decomposition**: `ℰ_d = 8 ∑_i (ℰ(K_i, 1) - ℰ(K_i, 3))`. -/
theorem IsGood.Ed_eq_sum_EK {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 1 ≤ x) :
    P.Ed F W d x =
      8 * ∑ i ∈ dyIdx x, (P.EK F W d x (Kdy i) 1 - P.EK F W d x (Kdy i) 3) := by
  have hx0 : 0 < x := by linarith
  rw [hd.Ed_eq_sum_ek F W hx]
  congr 1
  have h1 : ∀ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) * P.ek F W d x k =
      ∑ i ∈ dyIdx x, (ZMod.χ₄ (k : ZMod 4) : ℝ) * (Dyadic.psi0 (k / Kdy i) * P.ek F W d x k) := by
    intro k hk
    have hkodd : k % 2 = 1 := (Finset.mem_filter.1 hk).2
    have hk1 : 1 ≤ k := by omega
    by_cases hkp : P.kplus x ≤ k
    · rw [hd.ek_eq_zero_of_kplus_le F W hx0 hkp]; simp
    · push Not at hkp
      have hkx : (k : ℝ) < 2 * Real.sqrt x := lt_of_lt_of_le hkp (P.kplus_le x)
      rw [← Finset.mul_sum, ← Finset.sum_mul, sum_psi0_dyIdx hx0 hk1 hkx, one_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hK := Kdy_pos i
  rw [← hd.sum_kRange_filter_eq_EK F W hx0 hK (Or.inl rfl),
    ← hd.sum_kRange_filter_eq_EK F W hx0 hK (Or.inr rfl)]
  rw [← Finset.sum_filter_add_sum_filter_not (kRange x) (fun k => k % 4 = 1)]
  have h3 : (kRange x).filter (fun k => ¬ k % 4 = 1) = (kRange x).filter (fun k => k % 4 = 3) := by
    ext k
    simp only [kRange, Finset.mem_filter, Finset.mem_range]
    omega
  rw [h3]
  have hc1 : ∀ k ∈ (kRange x).filter (fun k => k % 4 = 1),
      (ZMod.χ₄ (k : ZMod 4) : ℝ) * (Dyadic.psi0 (k / Kdy i) * P.ek F W d x k) =
        Dyadic.psi0 (k / Kdy i) * P.ek F W d x k := by
    intro k hk
    have h4 : k % 4 = 1 := (Finset.mem_filter.1 hk).2
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp [show k % 2 ≠ 0 by omega, h4]
  have hc3 : ∀ k ∈ (kRange x).filter (fun k => k % 4 = 3),
      (ZMod.χ₄ (k : ZMod 4) : ℝ) * (Dyadic.psi0 (k / Kdy i) * P.ek F W d x k) =
        -(Dyadic.psi0 (k / Kdy i) * P.ek F W d x k) := by
    intro k hk
    have h4 : k % 4 = 3 := (Finset.mem_filter.1 hk).2
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp [show k % 2 ≠ 0 by omega, h4]
  rw [Finset.sum_congr rfl hc1, Finset.sum_congr rfl hc3, Finset.sum_neg_distrib]
  ring

theorem half_le_Kdy {x : ℝ} {i : ℤ} (hi : i ∈ dyIdx x) : 1 / 2 ≤ Kdy i := by
  simp only [dyIdx, Finset.mem_Icc] at hi
  unfold Kdy
  calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
    _ ≤ (2 : ℝ) ^ ((i : ℝ) / 2) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (-1 : ℝ) ≤ i := by exact_mod_cast hi.1
        linarith

/-- `ℰ(K, κ) = 0` for `K ≥ k₊`. -/
theorem IsGood.EK_eq_zero {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 0 < x) {K : ℝ} (hK : P.kplus x ≤ K) (κ : ℕ) : P.EK F W d x K κ = 0 := by
  unfold EK
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : Dyadic.psi0 (k / K) = 0
  · rw [h, zero_mul]
  · have hK0 : 0 < K := by
      by_contra hK0
      push Not at hK0
      have h1 := (psi0_ne_zero h).1
      rcases eq_or_lt_of_le hK0 with h0 | h0
      · rw [h0, div_zero] at h1; linarith
      · have : (k : ℝ) / K ≤ 0 := div_nonpos_of_nonneg_of_nonpos k.cast_nonneg hK0
        linarith
    have h1 := (psi0_ne_zero h).1
    rw [one_lt_div hK0] at h1
    rw [hd.ek_eq_zero_of_kplus_le F W hx (by linarith), mul_zero]

variable (P) in
/-- **Lemma 7.3 from a Type I estimate.** If the sums `Ξ` satisfy a bound
`‖Ξ‖ ≤ C Δ^c G(E, H, d, X, K)` under (H), then `|ℰ_d| ≤ C' #(dyadic K) B`, where `B` bounds
`G(E, H_d, d, X, dK)` for `1/2 ≤ K ≤ k₊`. -/
theorem abs_Ed_le_of_typeI (F : Cutoff) (W : HyperbolaWeight) (G : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ)
    (hT : ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ → ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤ C * Δ ^ c * G E H d X K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ), P.IsGood d → ∀ x : ℝ, 33 * (d : ℝ) ≤ x → 1 ≤ x →
      ∀ B : ℝ, 0 ≤ B →
      (∀ K : ℝ, 1 / 2 ≤ K → K ≤ P.kplus x →
        0 ≤ G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ∧
          G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ≤ B) →
      |P.Ed F W d x| ≤ C * (dyIdx x).card * B := by
  obtain ⟨c, hc⟩ := hT
  choose C1 hC1_0 hC1 using exists_bound_psiOne
  choose C2 hC2_0 hC2 using fun n => exists_bound_psiTwo (P := P) F n
  obtain ⟨C, hC⟩ := hc (fun n => C1 n + C2 n)
  set n : ℕ := ⌈c⌉₊ + 2 with hn
  obtain ⟨A, hA0, hA⟩ := WeightFourier.exists_fourier_bound_fW' W n
  have hnc : 1 < (n : ℝ) - c := by
    have := Nat.le_ceil c
    rw [hn]; push_cast; linarith
  have hInt : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ (c - n)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (n : ℝ) - c) (by simpa using hnc)
    simpa [Real.norm_eq_abs, neg_sub] using this
  set I := ∫ ξ : ℝ, (1 + |ξ|) ^ (c - n) with hI
  have hI0 : 0 ≤ I := integral_nonneg (fun ξ => by positivity)
  set Cp := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  refine ⟨16 * A * Cp * I, by positivity, ?_⟩
  intro d hd x hx hx1 B hB0 hGB
  have hx0 : 0 < x := by linarith
  -- the bound for each dyadic `K`
  have hEK : ∀ i ∈ dyIdx x, ∀ κ : ℕ, (κ = 1 ∨ κ = 3) →
      |P.EK F W d x (Kdy i) κ| ≤ A * Cp * I * B := by
    intro i hi κ hκ
    have hK0 := Kdy_pos i
    by_cases hKk : Kdy i ≤ P.kplus x
    · have hK12 := half_le_Kdy hi
      have hsep := hd.sum_psi0_ek_eq F W hx hK0 hκ
      rw [← Real.norm_eq_abs, ← Complex.norm_real, EK, hsep]
      have hbound : ∀ ξ : ℝ, ‖𝓕 (P.fK W x (Kdy i)) ξ *
          Xi P.Enat (P.Hnat d) d κ (P.Xpar d x) (d * Kdy i) (psiOne ξ) (P.psiTwo F d x ξ)‖ ≤
          A * Cp * B * (1 + |ξ|) ^ (c - n) := by
        intro ξ
        have hyp := hd.hypH F hx hκ hK12 hKk ξ (fun n => C1 n + C2 n)
          (fun ν t => (hC1 ν ξ t).trans (by
            have := hC2_0 ν
            have : 0 ≤ (1 + |ξ|) ^ ν := by positivity
            nlinarith))
          (fun ν t => (hC2 ν d hd x hx ξ t).trans (by
            have := hC1_0 ν
            have : 0 ≤ (1 + |ξ|) ^ ν := by positivity
            nlinarith))
        have hX := hC _ _ _ _ _ _ _ _ _ hyp
        obtain ⟨hG0, hGB'⟩ := hGB (Kdy i) hK12 hKk
        have hΔ : 0 < 1 + |ξ| := by positivity
        have hΔc : 0 ≤ (1 + |ξ|) ^ c := by positivity
        have hX' : ‖Xi P.Enat (P.Hnat d) d κ (P.Xpar d x) (d * Kdy i) (psiOne ξ)
            (P.psiTwo F d x ξ)‖ ≤ Cp * (1 + |ξ|) ^ c * B := by
          refine hX.trans ?_
          calc C * (1 + |ξ|) ^ c * G P.Enat (P.Hnat d) d (P.Xpar d x) (d * Kdy i)
              ≤ Cp * (1 + |ξ|) ^ c * G P.Enat (P.Hnat d) d (P.Xpar d x) (d * Kdy i) := by
                gcongr
                exact le_max_left _ _
            _ ≤ Cp * (1 + |ξ|) ^ c * B := by gcongr
        have hF := hA (P.uzero x (Kdy i)) ξ
        rw [norm_mul]
        calc ‖𝓕 (P.fK W x (Kdy i)) ξ‖ * ‖Xi P.Enat (P.Hnat d) d κ (P.Xpar d x) (d * Kdy i)
              (psiOne ξ) (P.psiTwo F d x ξ)‖
            ≤ (A * (1 + |ξ|) ^ (-(n : ℝ))) * (Cp * (1 + |ξ|) ^ c * B) :=
              mul_le_mul hF hX' (norm_nonneg _) (by positivity)
          _ = A * Cp * B * ((1 + |ξ|) ^ (-(n : ℝ)) * (1 + |ξ|) ^ c) := by ring
          _ = A * Cp * B * (1 + |ξ|) ^ (c - n) := by
              rw [← Real.rpow_add hΔ]; ring_nf
      calc ‖∫ ξ : ℝ, 𝓕 (P.fK W x (Kdy i)) ξ *
            Xi P.Enat (P.Hnat d) d κ (P.Xpar d x) (d * Kdy i) (psiOne ξ) (P.psiTwo F d x ξ)‖
          ≤ ∫ ξ : ℝ, A * Cp * B * (1 + |ξ|) ^ (c - n) :=
            norm_integral_le_of_norm_le (hInt.const_mul _) (Filter.Eventually.of_forall hbound)
        _ = A * Cp * I * B := by rw [integral_const_mul]; ring
    · push Not at hKk
      rw [hd.EK_eq_zero F W hx0 hKk.le, abs_zero]
      positivity
  rw [hd.Ed_eq_sum_EK F W hx1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  calc 8 * |∑ i ∈ dyIdx x, (P.EK F W d x (Kdy i) 1 - P.EK F W d x (Kdy i) 3)|
      ≤ 8 * ∑ i ∈ dyIdx x, |P.EK F W d x (Kdy i) 1 - P.EK F W d x (Kdy i) 3| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 8 * ∑ i ∈ dyIdx x, (2 * (A * Cp * I * B)) := by
        gcongr with i hi
        calc |P.EK F W d x (Kdy i) 1 - P.EK F W d x (Kdy i) 3|
            ≤ |P.EK F W d x (Kdy i) 1| + |P.EK F W d x (Kdy i) 3| := abs_sub _ _
          _ ≤ A * Cp * I * B + A * Cp * I * B :=
              add_le_add (hEK i hi 1 (Or.inl rfl)) (hEK i hi 3 (Or.inr rfl))
          _ = 2 * (A * Cp * I * B) := by ring
    _ = 16 * A * Cp * I * (dyIdx x).card * B := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end PatternData

end Triples
