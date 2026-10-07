import TriplesFinal.Poisson.Poisson

/-!
# Lemma 9.1(c): the tail `|h| > h₀`

Assume (H), and let `k_η = ⌈4/η⌉ + 2`. Then `∑_{|h| > h₀} |W_h| ≪ Δ^(k_η) (qX)^(-1)`, with the
implied constant depending only on `η` and the `C_ν`.

Integrating by parts `k_η` times gives `|ψ̂₂(ξ)| ≤ 2C_{k_η} Δ^(k_η) (2π|ξ|)^(-k_η)`
(`norm_fourier_le`). For `|h| > h₀` and `μ ≤ 2K` we have `2π|h|X/μ ≥ (qX)^η`, and
`η(k_η - 2) ≥ 4`; with `|S(h; μ)| ≤ μ` and `K ≤ qX`, `X ≥ 1`, this gives
`|W_h| ≤ (4C₀C_{k_η}/π²) Δ^(k_η) (qX)^(-1) h^(-2)` (`norm_Wh_le`).

Paper: §9.1, Lemma 9.1(c).
-/

namespace Triples

open MeasureTheory Filter
open scoped ContDiff Real

/-- `|S(h; μ)| ≤ μ`. -/
theorem norm_weylSum_le (E H : ℕ) (h : ℤ) (μ : ℕ) : ‖weylSum E H h μ‖ ≤ μ := by
  rw [weylSum_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_eC, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (roots E H μ).card ≤ μ := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- The number of moduli is at most `2K`. -/
theorem card_moduli_le (d κ : ℕ) {K : ℝ} (hK : 0 ≤ K) : ((moduli d κ K).card : ℝ) ≤ 2 * K := by
  have h1 : (moduli d κ K).card ≤ ⌊2 * K⌋₊ :=
    (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (⌊2 * K⌋₊ : ℝ) ≤ 2 * K := Nat.floor_le (by positivity)
  exact (Nat.cast_le.2 h1).trans h2

theorem le_of_mem_moduli {d κ μ : ℕ} {K : ℝ} (hμ : μ ∈ moduli d κ K) : 1 ≤ μ ∧ (μ : ℝ) ≤ 2 * K := by
  simp only [moduli, Finset.mem_filter, Finset.mem_Icc] at hμ
  refine ⟨hμ.1.1, ?_⟩
  have h := hμ.1.2
  by_cases hK : 0 ≤ 2 * K
  · exact (Nat.cast_le.2 h).trans (Nat.floor_le hK)
  · push Not at hK
    rw [Nat.floor_of_nonpos hK.le] at h
    omega

/-- The bound for `W_h` with `|h| > h₀`: `|W_h| ≤ (4 C₀ C_k/π²) Δ^k (qX)^(-1) h^(-2)`. -/
theorem norm_Wh_le {η : ℝ} (hη : 0 < η) {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ}
    {ψ₁ ψ₂ : ℝ → ℂ} (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) {h : ℤ}
    (hh : h₀ E d X K η < |(h : ℝ)|) :
    ‖Wh E H d κ X K ψ₁ ψ₂ h‖ ≤ 4 * |Cν 0| * |Cν (⌈4 / η⌉₊ + 2)| / π ^ 2 *
      Δ ^ (⌈4 / η⌉₊ + 2) * (((4 * E * d : ℕ) : ℝ) * X)⁻¹ * |(h : ℝ)| ^ (-2 : ℝ) := by
  set k := ⌈4 / η⌉₊ + 2 with hk
  set Q : ℝ := ((4 * E * d : ℕ) : ℝ) * X with hQ
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hd0 : 0 < d := hH.hd.pos
  have hN : (0 : ℝ) < ((E * H : ℕ) : ℝ) := by have := hH.hH; positivity
  have hX1 : 1 ≤ X := by
    refine le_trans ?_ hH.hX
    rw [Real.one_le_sqrt]
    have : 1 ≤ E * H := Nat.one_le_iff_ne_zero.2 (by have := hH.hH; positivity)
    exact_mod_cast this
  have hX : 0 < X := by linarith
  have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    have : (1 : ℝ) ≤ ((4 * E * d : ℕ) : ℝ) := by
      have : 1 ≤ 4 * E * d := Nat.one_le_iff_ne_zero.2 (by positivity)
      exact_mod_cast this
    nlinarith
  have hKQ : K ≤ Q := hH.hKq
  have hΔ : 1 ≤ Δ := hH.hΔ
  have hh0 : h ≠ 0 := by
    rintro rfl
    have : 0 < h₀ E d X K η := by unfold h₀; positivity
    simp at hh; linarith
  have habs : 0 < |(h : ℝ)| := abs_pos.2 (by exact_mod_cast hh0)
  -- `|h| X / K > Q^η ≥ 1`
  have hhX : Q ^ η < |(h : ℝ)| * X / K := by
    have : h₀ E d X K η = Q ^ η * K / X := rfl
    rw [this, div_lt_iff₀ hX] at hh
    rw [lt_div_iff₀ hK]; linarith
  have hQη : 1 ≤ Q ^ η := Real.one_le_rpow hQ1 hη.le
  -- `Q^(η(k - 2)) ≥ Q⁴`
  have hηk : (4 : ℝ) ≤ η * ((k - 2 : ℕ) : ℝ) := by
    rw [hk, Nat.add_sub_cancel]
    have := Nat.le_ceil (4 / η)
    rw [div_le_iff₀ hη] at this
    linarith
  have hQk : Q ^ 4 ≤ (Q ^ η) ^ (k - 2) := by
    rw [← Real.rpow_natCast (Q ^ η), ← Real.rpow_mul (by linarith)]
    rw [show (Q : ℝ) ^ 4 = Q ^ (4 : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hηk
  set C₀ := |Cν 0|
  set Ck := |Cν k|
  have hψ₁ : ∀ t, ‖ψ₁ t‖ ≤ C₀ := fun t => by
    have := hH.deriv₁ 0 t
    simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
    exact this.trans (le_abs_self _)
  have hψ₂k : ∀ t, ‖iteratedDeriv k ψ₂ t‖ ≤ Ck * Δ ^ k := fun t =>
    (hH.deriv₂ k t).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  -- the bound for each modulus
  have hterm : ∀ μ ∈ moduli d κ K, ‖ψ₁ (μ / K) * ((X / μ : ℝ) : ℂ) * fourier ψ₂ (h * X / μ) *
      weylSum E H h μ‖ ≤ C₀ * Ck / (2 * π ^ 2) * Δ ^ k * (μ : ℝ) ^ 2 / ((h : ℝ) ^ 2 * X) *
        (Q ^ 4)⁻¹ := by
    intro μ hμ
    obtain ⟨hμ1, hμK⟩ := le_of_mem_moduli hμ
    have hμ0 : (0 : ℝ) < μ := by exact_mod_cast hμ1
    set u := 2 * π * |(h : ℝ) * X / μ| with hu
    have hu_eq : u = 2 * π * (|(h : ℝ)| * X / μ) := by
      rw [hu, abs_div, abs_mul, abs_of_pos hX, abs_of_pos hμ0]
    have hu1 : Q ^ η ≤ u := by
      rw [hu_eq]
      have h1 : |(h : ℝ)| * X / K ≤ |(h : ℝ)| * X / μ * 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hK hμ0]
        have : 0 < |(h : ℝ)| * X := by positivity
        nlinarith
      have h2 : 0 ≤ |(h : ℝ)| * X / μ := by positivity
      nlinarith [Real.two_le_pi]
    have hupos : 0 < u := by linarith
    have hF := norm_fourier_le hH.smooth₂ hH.supp₂ hψ₂k (h * X / μ)
    rw [← hu] at hF
    -- `u^k ≥ u² Q^4`
    have huk : u ^ 2 * Q ^ 4 ≤ u ^ k := by
      have h2 : k = 2 + (k - 2) := by omega
      rw [h2, pow_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc Q ^ 4 ≤ (Q ^ η) ^ (k - 2) := hQk
        _ ≤ u ^ (k - 2) := pow_le_pow_left₀ (by positivity) hu1 _
    have hF' : ‖fourier ψ₂ (h * X / μ)‖ ≤ 2 * (Ck * Δ ^ k) / (u ^ 2 * Q ^ 4) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖fourier ψ₂ (h * X / μ)‖ * (u ^ 2 * Q ^ 4) ≤ ‖fourier ψ₂ (h * X / μ)‖ * u ^ k :=
            mul_le_mul_of_nonneg_left huk (norm_nonneg _)
        _ ≤ 2 * (Ck * Δ ^ k) := by linarith
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hX hμ0)]
    have hS := norm_weylSum_le E H h μ
    calc ‖ψ₁ (μ / K)‖ * (X / μ) * ‖fourier ψ₂ (h * X / μ)‖ * ‖weylSum E H h μ‖
        ≤ C₀ * (X / μ) * (2 * (Ck * Δ ^ k) / (u ^ 2 * Q ^ 4)) * μ := by
          gcongr
          · exact hψ₁ _
      _ = C₀ * Ck / (2 * π ^ 2) * Δ ^ k * (μ : ℝ) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹ := by
          rw [hu_eq]
          field_simp
          rw [sq_abs]
  -- sum over the moduli
  set A : ℝ := C₀ * Ck / (2 * π ^ 2) * Δ ^ k with hA
  have hA0 : 0 ≤ A := by positivity
  have hh2 : (0 : ℝ) < (h : ℝ) ^ 2 := by positivity
  have hsum : ‖Wh E H d κ X K ψ₁ ψ₂ h‖ ≤ ∑ μ ∈ moduli d κ K,
      A * (μ : ℝ) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hsum2 : ∑ μ ∈ moduli d κ K, A * (μ : ℝ) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹ ≤
      (moduli d κ K).card • (A * (2 * K) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹) := by
    apply Finset.sum_le_card_nsmul
    intro μ hμ
    obtain ⟨hμ1, hμK⟩ := le_of_mem_moduli hμ
    have hμ0 : (0 : ℝ) ≤ μ := by positivity
    have : (μ : ℝ) ^ 2 ≤ (2 * K) ^ 2 := pow_le_pow_left₀ hμ0 hμK 2
    gcongr
  rw [nsmul_eq_mul] at hsum2
  have hcard := card_moduli_le d κ hK.le
  have hfin : ((moduli d κ K).card : ℝ) * (A * (2 * K) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹) ≤
      8 * A * Q⁻¹ * ((h : ℝ) ^ 2)⁻¹ := by
    calc ((moduli d κ K).card : ℝ) * (A * (2 * K) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹)
        ≤ (2 * K) * (A * (2 * K) ^ 2 / ((h : ℝ) ^ 2 * X) * (Q ^ 4)⁻¹) := by gcongr
      _ = 8 * A * K ^ 3 / X * (Q ^ 4)⁻¹ * ((h : ℝ) ^ 2)⁻¹ := by field_simp; ring
      _ ≤ 8 * A * Q ^ 3 / 1 * (Q ^ 4)⁻¹ * ((h : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 8 * A * Q⁻¹ * ((h : ℝ) ^ 2)⁻¹ := by
          have hQ0 : Q ≠ 0 := by positivity
          field_simp
  have hrpow : |(h : ℝ)| ^ (-2 : ℝ) = ((h : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  rw [hrpow]
  calc ‖Wh E H d κ X K ψ₁ ψ₂ h‖ ≤ 8 * A * Q⁻¹ * ((h : ℝ) ^ 2)⁻¹ :=
        hsum.trans (hsum2.trans hfin)
    _ = 4 * C₀ * Ck / π ^ 2 * Δ ^ k * Q⁻¹ * ((h : ℝ) ^ 2)⁻¹ := by
        rw [hA]; field_simp; ring

/-- **Lemma 9.1(c).** `∑_{|h| > h₀} |W_h| ≪ Δ^(k_η) (qX)^(-1)`, with the implied constant
depending only on `η` and the `C_ν`. -/
theorem poisson_c {η : ℝ} (hη : 0 < η) (Cν : ℕ → ℝ) :
    ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ∑' h : {h : ℤ // h₀ E d X K η < |(h : ℝ)|}, ‖Wh E H d κ X K ψ₁ ψ₂ h‖ ≤
        C * Δ ^ (⌈4 / η⌉₊ + 2) * (((4 * E * d : ℕ) : ℝ) * X)⁻¹ := by
  set S₂ := ∑' h : ℤ, |(h : ℝ)| ^ (-2 : ℝ) with hS₂
  refine ⟨4 * |Cν 0| * |Cν (⌈4 / η⌉₊ + 2)| / π ^ 2 * S₂, ?_⟩
  intro E H d κ Δ X K ψ₁ ψ₂ hH
  set B := 4 * |Cν 0| * |Cν (⌈4 / η⌉₊ + 2)| / π ^ 2 * Δ ^ (⌈4 / η⌉₊ + 2) *
    (((4 * E * d : ℕ) : ℝ) * X)⁻¹ with hB
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hH0 : 0 < H := hH.hH
  have hX : 0 < X := lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) hH.hX
  have hΔ : 0 ≤ Δ := le_trans zero_le_one hH.hΔ
  have hB0 : 0 ≤ B := by positivity
  have hsumm : Summable (fun h : ℤ => B * |(h : ℝ)| ^ (-2 : ℝ)) :=
    (Real.summable_abs_int_rpow one_lt_two).mul_left B
  have hle : ∀ h : {h : ℤ // h₀ E d X K η < |(h : ℝ)|},
      ‖Wh E H d κ X K ψ₁ ψ₂ h‖ ≤ B * |((h : ℤ) : ℝ)| ^ (-2 : ℝ) := fun h =>
    norm_Wh_le hη hH h.2
  have hsub : Summable (fun h : {h : ℤ // h₀ E d X K η < |(h : ℝ)|} =>
      B * |((h : ℤ) : ℝ)| ^ (-2 : ℝ)) :=
    hsumm.comp_injective Subtype.val_injective
  have hlhs : Summable (fun h : {h : ℤ // h₀ E d X K η < |(h : ℝ)|} =>
      ‖Wh E H d κ X K ψ₁ ψ₂ h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsub
  calc ∑' h : {h : ℤ // h₀ E d X K η < |(h : ℝ)|}, ‖Wh E H d κ X K ψ₁ ψ₂ h‖
      ≤ ∑' h : ℤ, B * |(h : ℝ)| ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
          (fun c _ => by positivity) hle hlhs hsumm
    _ = B * S₂ := tsum_mul_left
    _ = _ := by rw [hB]; ring

end Triples
