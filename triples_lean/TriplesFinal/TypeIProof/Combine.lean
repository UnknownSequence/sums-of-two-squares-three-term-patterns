import TriplesFinal.TypeIProof.BlockTail

/-!
# Combining the blocks

The spectrum is cut into the blocks `‖t‖ ≤ 1`, `1 < ‖t‖ ≤ T₁` and
`2^m T₁ < ‖t‖ ≤ 2^(m+1) T₁` (`m ≥ 0`), and the Cauchy–Schwarz inequality is applied on each
block (`setIntegral_mul_le_tsum`). On the real spectrum `‖t‖ > 1`,
`|B|² ≤ 3(m_main(t) + m_main(-t) + mᴿ(t))` (`normSq_B_le_J1`).

Paper: §§12.2–12.6.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff Interval

section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Cauchy–Schwarz over a countable partition**: if `∫_{s n} f² ≤ a n` and
`∫_{s n} g² ≤ b n`, then `∫_{⋃ s n} f g ≤ ∑ √(a n) √(b n)`. -/
theorem setIntegral_mul_le_tsum {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Function.onFun Disjoint s)) {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : ∀ n, IntegrableOn (fun x => f x ^ 2) (s n) μ)
    (hg2 : ∀ n, IntegrableOn (fun x => g x ^ 2) (s n) μ) {a b : ℕ → ℝ}
    (ha : ∀ n, ∫ x in s n, f x ^ 2 ∂μ ≤ a n) (hb : ∀ n, ∫ x in s n, g x ^ 2 ∂μ ≤ b n)
    (hsum : Summable fun n => Real.sqrt (a n) * Real.sqrt (b n)) :
    IntegrableOn (fun x => f x * g x) (⋃ n, s n) μ ∧
      ∫ x in ⋃ n, s n, f x * g x ∂μ ≤ ∑' n, Real.sqrt (a n) * Real.sqrt (b n) :=
  setIntegral_iUnion_le hs hd (fun x => mul_nonneg (hf0 x) (hg0 x))
    (fun n => IntegrableOn.mul_of_sq hfm.restrict hgm.restrict (hf2 n) (hg2 n))
    (fun n => setIntegral_mul_le_of_sq hf0 hg0 hfm.restrict hgm.restrict (hf2 n) (hg2 n)
      (ha n) (hb n)) hsum

end

theorem sq_norm_add3_le (a b c : ℂ) : ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

/-- The blocks of the spectrum: lower and upper radii. -/
noncomputable def blockLo (T₁ : ℝ) : ℕ → ℝ
  | 0 => -1
  | 1 => 1
  | (m + 2) => 2 ^ m * T₁

noncomputable def blockHi (T₁ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => T₁
  | (m + 2) => 2 ^ (m + 1) * T₁

theorem blockHi_le_blockLo {T₁ : ℝ} (hT₁ : 1 ≤ T₁) {n n' : ℕ} (h : n < n') :
    blockHi T₁ n ≤ blockLo T₁ n' := by
  have hT0 : 0 ≤ T₁ := by linarith
  match n, n', h with
  | 0, 1, _ => simp [blockHi, blockLo]
  | 0, (m + 2), _ =>
      simp only [blockHi, blockLo]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 ^ m * T₁ := mul_le_mul (one_le_pow₀ (by norm_num)) hT₁ zero_le_one (by positivity)
  | 1, (m + 2), _ =>
      simp only [blockHi, blockLo]
      calc T₁ = 1 * T₁ := by ring
        _ ≤ 2 ^ m * T₁ := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) hT0
  | (m + 2), (m' + 2), h =>
      simp only [blockHi, blockLo]
      apply mul_le_mul_of_nonneg_right _ hT0
      exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem one_le_blockHi {T₁ : ℝ} (hT₁ : 1 ≤ T₁) (n : ℕ) : 1 ≤ blockHi T₁ n := by
  match n with
  | 0 => simp [blockHi]
  | 1 => simpa [blockHi] using hT₁
  | (m + 2) =>
      simp only [blockHi]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 ^ (m + 1) * T₁ := mul_le_mul (one_le_pow₀ (by norm_num)) hT₁ zero_le_one
            (by positivity)

namespace SpecFam

variable (F : SpecFam)

/-- The blocks `blockLo < ‖t‖ ≤ blockHi`. -/
def block (T₁ : ℝ) (n : ℕ) : Set F.Ω := F.annulus (blockLo T₁ n) (blockHi T₁ n)

theorem measurableSet_block (T₁ : ℝ) (n : ℕ) : MeasurableSet (F.block T₁ n) :=
  F.measurableSet_annulus _ _

theorem block_subset_ball (T₁ : ℝ) (n : ℕ) : F.block T₁ n ⊆ F.ball (blockHi T₁ n) :=
  F.annulus_subset_ball _ _

theorem block_zero (T₁ : ℝ) : F.block T₁ 0 = F.ball 1 := by
  ext x
  simp only [block, annulus, ball, blockLo, blockHi, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by linarith [norm_nonneg (F.t x)], h⟩

theorem block_disjoint {T₁ : ℝ} (hT₁ : 1 ≤ T₁) :
    Pairwise (Function.onFun Disjoint (F.block T₁)) := by
  intro n n' hne
  rcases lt_or_gt_of_ne hne with h | h
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    have := blockHi_le_blockLo hT₁ h
    linarith [hx.2, hx'.1]
  · refine Set.disjoint_left.2 fun x hx hx' => ?_
    have := blockHi_le_blockLo hT₁ h
    linarith [hx.1, hx'.2]

theorem iUnion_block {T₁ : ℝ} (hT₁ : 1 ≤ T₁) : ⋃ n, F.block T₁ n = univ := by
  classical
  refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
  by_cases h1 : ‖F.t x‖ ≤ 1
  · refine ⟨0, ?_, h1⟩
    show (-1 : ℝ) < ‖F.t x‖
    linarith [norm_nonneg (F.t x)]
  push Not at h1
  by_cases h2 : ‖F.t x‖ ≤ T₁
  · exact ⟨1, h1, h2⟩
  push Not at h2
  have hT0 : 0 < T₁ := by linarith
  have hex : ∃ m : ℕ, ‖F.t x‖ ≤ 2 ^ (m + 1) * T₁ := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (‖F.t x‖ / T₁) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ hT0] at hm
    have : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  set m₀ := Nat.find hex with hm₀
  have hspec : ‖F.t x‖ ≤ 2 ^ (m₀ + 1) * T₁ := Nat.find_spec hex
  refine ⟨m₀ + 2, ?_, hspec⟩
  show 2 ^ m₀ * T₁ < ‖F.t x‖
  rcases Nat.eq_zero_or_pos m₀ with h0 | hpos
  · rw [h0, pow_zero, one_mul]; exact h2
  · have hlt : m₀ - 1 < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    push Not at hmin
    have e : m₀ - 1 + 1 = m₀ := by omega
    rw [e] at hmin
    exact hmin

end SpecFam

namespace Setup

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition) (F : SpecFam)

/-- **The pointwise bound on the real spectrum `|t| ≥ 1`**:
`|B(ρ, t)|² ≤ 3(m_main(t) + m_main(-t) + mᴿ(t))`. -/
theorem normSq_B_le_J1 (hB : BesselAssumptions) {C6 : ℝ} (hC6 : 0 ≤ C6)
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    (ρ : ℕ → ℂ) {τ : ℝ} (hτ : 1 ≤ |τ|) :
    ‖S.B ψ₀ ρ τ‖ ^ 2 ≤ 3 * (S.mMain ψ₀ ρ τ + S.mMain ψ₀ ρ (-τ) + S.mRem ψ₀ ρ τ) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h, abs_zero] at hτ; linarith
  rw [S.B_eq_J1 ψ₀ hB ρ hτ0]
  refine (sq_norm_add3_le _ _ _).trans ?_
  have h1 := S.normSq_Bmain_le ψ₀ ρ hτ
  have h2 := S.normSq_Bmain_le ψ₀ ρ (τ := -τ) (by rwa [abs_neg])
  have hG : ∀ ξ : ℝ, ‖Gt τ (-3 / 2 + I * ξ)‖ ≤ |CGt| := by
    intro ξ
    refine (hGt τ ξ).trans ?_
    have e1 : Real.exp (-Real.pi * |τ| / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, abs_nonneg τ])
    have e2 : (1 + |ξ + τ|) ^ (-(5 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (ξ + τ)]) (by norm_num)
    have e3 : (1 + |ξ - τ|) ^ (-(5 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (ξ - τ)]) (by norm_num)
    have e1' : 0 ≤ Real.exp (-Real.pi * |τ| / 2) := (Real.exp_pos _).le
    have e2' : 0 ≤ (1 + |ξ + τ|) ^ (-(5 : ℝ) / 4) := by positivity
    have e3' : 0 ≤ (1 + |ξ - τ|) ^ (-(5 : ℝ) / 4) := by positivity
    calc CGt * Real.exp (-Real.pi * |τ| / 2) * (1 + |ξ + τ|) ^ (-(5 : ℝ) / 4) *
          (1 + |ξ - τ|) ^ (-(5 : ℝ) / 4)
        ≤ |CGt| * Real.exp (-Real.pi * |τ| / 2) * (1 + |ξ + τ|) ^ (-(5 : ℝ) / 4) *
            (1 + |ξ - τ|) ^ (-(5 : ℝ) / 4) := by
          gcongr; exact le_abs_self _
      _ ≤ |CGt| * 1 * 1 * 1 := by gcongr
      _ = |CGt| := by ring
  have h3 := S.normSq_Brem_le ψ₀ hC6 hM6 hG ρ
  linarith

end Setup

end Triples
