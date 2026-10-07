import TriplesFinal.TypeIProof.FinalBound
import TriplesFinal.Asymptotic.DyadicPartition

/-!
# The proof of Theorem 6.1

Fix `η > 0` and work with `η' = min(η, 1)/18`. By Lemma 9.1(d),
`Ξ = ∑_{M ∈ 𝓜} (Ξ_M(ψ₂) + Ξ_M(ψ₂⁻)) + O(Δ^(k_η') (qX)^(-1))` with `#𝓜 ≪ log(qX)`. For each
`M ∈ 𝓜` the set-up of §12 applies to `ψ₂` and to `ψ₂⁻`, and `Setup.XiM_bound_a`
(resp. `Setup.XiM_bound_b`) gives `|Ξ_M| ≤ K Δ⁹ Q^(17η') H^(1/4 + η'/2) X^(1/2) 𝒜^θ`, where
`𝒜 = 1 + X/(dH^(1/2))` (resp. `1 + K/(dH^(1/2))`) and `K` depends only on `η`, `θ` and the
constants `C_ν`. Summing over `M` with `log Q ≤ Q^η'/η'` and `Q^(18η') H^(η'/2) ≤ (QH)^η`
gives Theorem 6.1 with exponent `c = max(9, ⌈4/η'⌉ + 2)` of `Δ`.

Paper: §12.6.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups
open SymMat

/-- **The assembly**: the per-`M` bounds and Lemma 9.1(d) give the shape of Theorem 6.1. -/
theorem typeI_assemble (ψ₀ : DyadicPartition) {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ}
    {ψ₁ ψ₂ : ℝ → ℂ} (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) {η η' c Cpd Kf A : ℝ} (hη' : 0 < η')
    (hηη : 18 * η' ≤ η) (hc9 : 9 ≤ c) (hck : ((⌈4 / η'⌉₊ + 2 : ℕ) : ℝ) ≤ c) (hKf : 0 ≤ Kf)
    (hA : 1 ≤ A)
    (hpd1 : ‖Xi E H d κ X K ψ₁ ψ₂ - ∑ M ∈ dyadicSet (h₀ E d X K η'),
          (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M)‖ ≤
        Cpd * Δ ^ (⌈4 / η'⌉₊ + 2) * (((4 * E * d : ℕ) : ℝ) * X)⁻¹)
    (hpd2 : ((dyadicSet (h₀ E d X K η')).card : ℝ) ≤
      Cpd * Real.log (((4 * E * d : ℕ) : ℝ) * X))
    (hM : ∀ M ∈ dyadicSet (h₀ E d X K η'),
      ‖XiM ψ₀ E H d κ X K ψ₁ ψ₂ M‖ + ‖XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M‖ ≤
        2 * (Kf * Δ ^ 9 * ((((4 * E * d : ℕ) : ℝ) * X) ^ η') ^ 17 * (H : ℝ) ^ (1 / 4 : ℝ) *
          (H : ℝ) ^ (η' / 2) * Real.sqrt X * A)) :
    ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤
      (max Cpd 0 + max Cpd 0 / η' * 2 * Kf) * Δ ^ c *
        (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) * A := by
  set Q : ℝ := ((4 * E * d : ℕ) : ℝ) * X with hQ
  -- basic facts
  have hE4 : 4 ≤ E := by rcases hH.hE with h | h <;> omega
  have hq48 : (48 : ℝ) ≤ ((4 * E * d : ℕ) : ℝ) := by
    have : 48 ≤ 4 * E * d := by have := hH.hd3; nlinarith
    exact_mod_cast this
  have hX1 : 1 ≤ X := by
    refine le_trans ?_ hH.hX
    rw [Real.one_le_sqrt]
    have : 1 ≤ E * H := Nat.one_le_iff_ne_zero.2 (by have := hH.hH; positivity)
    exact_mod_cast this
  have hX0 : 0 < X := by linarith
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH.hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hΔ1 := hH.hΔ
  have hΔ0 : 0 < Δ := by linarith
  have hη0 : 0 < η := by linarith
  have hA0 : 0 ≤ A := by linarith
  -- the sum over `M`
  set B := Kf * Δ ^ 9 * (Q ^ η') ^ 17 * (H : ℝ) ^ (1 / 4 : ℝ) * (H : ℝ) ^ (η' / 2) *
    Real.sqrt X * A with hB
  have hB0 : 0 ≤ B := by positivity
  set 𝓜 := dyadicSet (h₀ E d X K η') with h𝓜
  have hsum : ‖∑ M ∈ 𝓜, (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M)‖ ≤
      (𝓜.card : ℝ) * (2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul 𝓜
      (fun M => ‖XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M‖) (2 * B)
      (fun M hM' => (norm_add_le _ _).trans (hM M hM'))
    rwa [nsmul_eq_mul] at this
  have hcard : (𝓜.card : ℝ) ≤ max Cpd 0 * (Q ^ η' / η') := by
    have hlog : Real.log Q ≤ Q ^ η' / η' := Real.log_le_rpow_div hQ0.le hη'
    have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
    calc (𝓜.card : ℝ) ≤ Cpd * Real.log Q := hpd2
      _ ≤ max Cpd 0 * Real.log Q := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
      _ ≤ max Cpd 0 * (Q ^ η' / η') := mul_le_mul_of_nonneg_left hlog (le_max_right _ _)
  -- the powers
  have hΔ9 : Δ ^ 9 ≤ Δ ^ c := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hΔ1 (by push_cast; linarith)
  have hΔk : Δ ^ (⌈4 / η'⌉₊ + 2) ≤ Δ ^ c := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hΔ1 hck
  have hx18 : (Q ^ η') ^ 18 ≤ Q ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by push_cast; linarith)
  have hHη : (H : ℝ) ^ (η' / 2) ≤ (H : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
  have hQH : (Q * H) ^ η = Q ^ η * (H : ℝ) ^ η := Real.mul_rpow hQ0.le hH0.le
  have hsX : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  -- the target factor is at least `1`
  set T := (Q * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) * A with hT
  have hT1 : 1 ≤ T := by
    have h1 : 1 ≤ (Q * H) ^ η := Real.one_le_rpow (by nlinarith) hη0.le
    have h2 : 1 ≤ X ^ (1 / 2 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
    have h3 : 1 ≤ (H : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hH1 (by norm_num)
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3) hA
  -- the error term
  have herr : Cpd * Δ ^ (⌈4 / η'⌉₊ + 2) * Q⁻¹ ≤ max Cpd 0 * Δ ^ c * T := by
    have hQi : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ1
    have hQi0 : 0 ≤ Q⁻¹ := by positivity
    calc Cpd * Δ ^ (⌈4 / η'⌉₊ + 2) * Q⁻¹ ≤ max Cpd 0 * Δ ^ (⌈4 / η'⌉₊ + 2) * Q⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hQi0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cpd 0 * Δ ^ c * 1 := by gcongr
      _ ≤ max Cpd 0 * Δ ^ c * T := by gcongr
  -- the main term
  have hmain : (𝓜.card : ℝ) * (2 * B) ≤ max Cpd 0 / η' * 2 * Kf * Δ ^ c * T := by
    calc (𝓜.card : ℝ) * (2 * B) ≤ max Cpd 0 * (Q ^ η' / η') * (2 * B) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = max Cpd 0 / η' * 2 * Kf * Δ ^ 9 * ((Q ^ η') ^ 18 * (H : ℝ) ^ (η' / 2)) *
            (Real.sqrt X * (H : ℝ) ^ (1 / 4 : ℝ) * A) := by
          rw [hB]; ring
      _ ≤ max Cpd 0 / η' * 2 * Kf * Δ ^ c * (Q ^ η * (H : ℝ) ^ η) *
            (Real.sqrt X * (H : ℝ) ^ (1 / 4 : ℝ) * A) := by
          gcongr
      _ = max Cpd 0 / η' * 2 * Kf * Δ ^ c * T := by
          rw [hT, hQH, hsX]; ring
  have htri := norm_sub_norm_le (Xi E H d κ X K ψ₁ ψ₂)
    (∑ M ∈ 𝓜, (XiM ψ₀ E H d κ X K ψ₁ ψ₂ M + XiM ψ₀ E H d κ X K ψ₁ (reflect ψ₂) M))
  calc ‖Xi E H d κ X K ψ₁ ψ₂‖
      ≤ max Cpd 0 * Δ ^ c * T + max Cpd 0 / η' * 2 * Kf * Δ ^ c * T := by
        linarith
    _ = (max Cpd 0 + max Cpd 0 / η' * 2 * Kf) * Δ ^ c * T := by ring
    _ = _ := by rw [hT]; ring

/-- The auxiliary exponent `η' = min(η, 1)/18`. -/
theorem eta_aux {η : ℝ} (hη : 0 < η) :
    0 < min η 1 / 18 ∧ min η 1 / 18 ≤ 1 ∧ 18 * (min η 1 / 18) ≤ η ∧
      1 ≤ min η 1 / 18 * (((⌈1 / (min η 1 / 18)⌉₊ + 3 : ℕ) : ℝ) - 3) := by
  have h0 : 0 < min η 1 / 18 := by positivity
  refine ⟨h0, ?_, ?_, ?_⟩
  · have := min_le_right η 1; linarith
  · have := min_le_left η 1; linarith
  · have h1 := Nat.le_ceil (1 / (min η 1 / 18))
    have h2 : min η 1 / 18 * (1 / (min η 1 / 18)) = 1 := by field_simp
    push_cast
    calc (1 : ℝ) = min η 1 / 18 * (1 / (min η 1 / 18)) := h2.symm
      _ ≤ min η 1 / 18 * (⌈1 / (min η 1 / 18)⌉₊ : ℝ) := mul_le_mul_of_nonneg_left h1 h0.le
      _ = _ := by ring

theorem HypH.q_pos {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) : 0 < 4 * E * d := by
  have hd := hH.hd.pos
  have hE : 0 < E := by rcases hH.hE with h | h <;> omega
  positivity

set_option maxHeartbeats 1000000 in
/-- **Theorem 6.1(a)**, proof. -/
theorem typeI_a_proof {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesis θ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤
        C * Δ ^ c * (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
          (1 + X / (d * Real.sqrt H)) ^ θ := by
  obtain ⟨Cls, hCls⟩ := hS
  obtain ⟨hη'0, hη'1, hηη, hkη⟩ := eta_aux hη
  set η' := min η 1 / 18 with hη'
  refine ⟨max 9 ((⌈4 / η'⌉₊ + 2 : ℕ) : ℝ), fun Cν => ?_⟩
  obtain ⟨Cpd, hCpd⟩ := poisson_d dyadicPartition hη'0 Cν
  obtain ⟨Cψ, hCψ0, hψ⟩ := DyadicPartition.exists_deriv_bound dyadicPartition
  obtain ⟨CG, hCG0, hCG⟩ := Setup.exists_bound_Gfun Cν dyadicPartition
  obtain ⟨Cd, hCd⟩ := Mh_deriv_bound' Cν hη'0
  obtain ⟨C6, hC6⟩ := Mh_bound Cν 6 hη'0
  obtain ⟨Ck, hCk⟩ := Mh_bound Cν (⌈1 / η'⌉₊ + 3) hη'0
  obtain ⟨CGt, hCGt⟩ := Gt_bound hB
  obtain ⟨CP, hCP⟩ := pair_count hη'0
  obtain ⟨C', hC'⟩ := SpectralData.discFam_ExcA hθ0 hθ Cls hη'0
  set Kf := 12 * Setup.KspecF Cν η' Cls (max C' 0 * CG ^ 2 * 2) Cψ (max Cd 0) (max C6 0) CGt
    (max Ck 0) * Real.sqrt (max CP 0) * 3 * 9 ^ 9 * 8 with hKf
  have hKf0 : 0 ≤ Kf := by
    have := Setup.KspecF_nonneg Cν η' Cls (max C' 0 * CG ^ 2 * 2) Cψ (max Cd 0) (max C6 0) CGt
      (max Ck 0)
    positivity
  refine ⟨max Cpd 0 + max Cpd 0 / η' * 2 * Kf, ?_⟩
  intro E H d κ Δ X K ψ₁ ψ₂ hH
  have hq0 := hH.q_pos
  obtain ⟨D, hPE, hPT, hDI2, -, hPas, hEB, hEC⟩ := hCls (4 * E * d) hq0
  have hM : ∀ ψ : ℝ → ℂ, HypH Cν E H d κ Δ X K ψ₁ ψ → ∀ M ∈ dyadicSet (h₀ E d X K η'),
      ‖XiM dyadicPartition E H d κ X K ψ₁ ψ M‖ ≤
        Kf * Δ ^ 9 * ((((4 * E * d : ℕ) : ℝ) * X) ^ η') ^ 17 * (H : ℝ) ^ (1 / 4 : ℝ) *
          (H : ℝ) ^ (η' / 2) * Real.sqrt X * (1 + X / (d * Real.sqrt H)) ^ θ := by
    intro ψ hψH M hMm
    obtain ⟨hM1, hM2⟩ := mem_dyadicSet_bounds hMm
    exact Setup.XiM_bound_a ⟨E, H, d, κ, Δ, X, K, ψ₁, ψ, hψH, η', hη'0, hη'1, M, hM1, hM2⟩
      dyadicPartition hθ0 hθ hB hSC D rfl hPE hPT hDI2 hEC (hC' _ D hq0 hDI2 hPas hEB) hCG0
      (hCG _) hCψ0 hψ hCd hC6 hCGt hkη hCk hCP
  obtain ⟨hpd1, hpd2⟩ := hCpd E H d κ Δ X K ψ₁ ψ₂ hH
  have hA : 1 ≤ (1 + X / (d * Real.sqrt H)) ^ θ := by
    have hX := hH.Xpos
    have : 0 ≤ X / (d * Real.sqrt H) := by positivity
    exact Real.one_le_rpow (by linarith) hθ0
  exact typeI_assemble dyadicPartition hH hη'0 hηη (le_max_left _ _) (le_max_right _ _) hKf0 hA
    hpd1 hpd2 (fun M hMm => by
      have h1 := hM ψ₂ hH M hMm
      have h2 := hM (reflect ψ₂) hH.reflect M hMm
      linarith)

set_option maxHeartbeats 1000000 in
/-- **Theorem 6.1(b)**, proof. -/
theorem typeI_b_proof {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesisDI θ) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
      ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤
        C * Δ ^ c * (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
          (1 + K / (d * Real.sqrt H)) ^ θ := by
  obtain ⟨Cls, hCls⟩ := hS
  obtain ⟨hη'0, hη'1, hηη, hkη⟩ := eta_aux hη
  set η' := min η 1 / 18 with hη'
  refine ⟨max 9 ((⌈4 / η'⌉₊ + 2 : ℕ) : ℝ), fun Cν => ?_⟩
  obtain ⟨Cpd, hCpd⟩ := poisson_d dyadicPartition hη'0 Cν
  obtain ⟨Cψ, hCψ0, hψ⟩ := DyadicPartition.exists_deriv_bound dyadicPartition
  obtain ⟨Cd, hCd⟩ := Mh_deriv_bound' Cν hη'0
  obtain ⟨C6, hC6⟩ := Mh_bound Cν 6 hη'0
  obtain ⟨Ck, hCk⟩ := Mh_bound Cν (⌈1 / η'⌉₊ + 3) hη'0
  obtain ⟨CGt, hCGt⟩ := Gt_bound hB
  obtain ⟨CP, hCP⟩ := pair_count hη'0
  set Kf := 12 * Setup.KspecF Cν η' Cls (16 * max (Cls η') 0 * |Cν 0| ^ 2) Cψ (max Cd 0)
    (max C6 0) CGt (max Ck 0) * Real.sqrt (max CP 0) * 3 * 9 ^ 9 * 8 with hKf
  have hKf0 : 0 ≤ Kf := by
    have := Setup.KspecF_nonneg Cν η' Cls (16 * max (Cls η') 0 * |Cν 0| ^ 2) Cψ (max Cd 0)
      (max C6 0) CGt (max Ck 0)
    positivity
  refine ⟨max Cpd 0 + max Cpd 0 / η' * 2 * Kf, ?_⟩
  intro E H d κ Δ X K ψ₁ ψ₂ hH
  have hq0 := hH.q_pos
  obtain ⟨D, hPE, hPT, hDI2, hDI5, hEB, hEC⟩ := hCls (4 * E * d) hq0
  have hM : ∀ ψ : ℝ → ℂ, HypH Cν E H d κ Δ X K ψ₁ ψ → ∀ M ∈ dyadicSet (h₀ E d X K η'),
      ‖XiM dyadicPartition E H d κ X K ψ₁ ψ M‖ ≤
        Kf * Δ ^ 9 * ((((4 * E * d : ℕ) : ℝ) * X) ^ η') ^ 17 * (H : ℝ) ^ (1 / 4 : ℝ) *
          (H : ℝ) ^ (η' / 2) * Real.sqrt X * (1 + K / (d * Real.sqrt H)) ^ θ := by
    intro ψ hψH M hMm
    obtain ⟨hM1, hM2⟩ := mem_dyadicSet_bounds hMm
    exact Setup.XiM_bound_b ⟨E, H, d, κ, Δ, X, K, ψ₁, ψ, hψH, η', hη'0, hη'1, M, hM1, hM2⟩
      dyadicPartition hθ0 hθ hB hSC D rfl hPE hPT hDI2 hDI5 hEB hEC hCψ0 hψ hCd hC6 hCGt hkη
      hCk hCP
  obtain ⟨hpd1, hpd2⟩ := hCpd E H d κ Δ X K ψ₁ ψ₂ hH
  have hA : 1 ≤ (1 + K / (d * Real.sqrt H)) ^ θ := by
    have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
    have : 0 ≤ K / (d * Real.sqrt H) := by positivity
    exact Real.one_le_rpow (by linarith) hθ0
  exact typeI_assemble dyadicPartition hH hη'0 hηη (le_max_left _ _) (le_max_right _ _) hKf0 hA
    hpd1 hpd2 (fun M hMm => by
      have h1 := hM ψ₂ hH M hMm
      have h2 := hM (reflect ψ₂) hH.reflect M hMm
      linarith)

end Triples
