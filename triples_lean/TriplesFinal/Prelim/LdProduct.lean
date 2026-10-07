import TriplesFinal.Prelim.SingularSeriesValue
import TriplesFinal.Prelim.LValue
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues

/-!
# Lemma 5.3(c): the product formula `𝔏_d = L(1, χ) L(1, ψ) 𝒫_d`

For real `s > 1`, `∑ χf(n) n^(-s) = L(s, χ) L(s, ψ) ∑ β(n) n^(-s)`, since `χ f = χ ∗ ψ ∗ β`
(`IsGood.LSeries_gR`). As `s → 1⁺`:

* the left side tends to `𝔏_d` (Abelian theorem, using Lemma 5.3(b));
* `L(s, χ₄) → π/4` (Abelian theorem and Leibniz's series, `tsum_abelTerm_chiR`);
* `L(s, ψ) → L(1, ψ)` (continuity of the `L`-function of the non-principal character `ψ`);
* `∑ β(n) n^(-s) → 𝒫_d = ∑ β(n)/n` (dominated convergence).

Hence `𝔏_d = (π/4) L(1, ψ) 𝒫_d` (`IsGood.Ld_eq_product`). The lower bound
`𝒫_d ≥ (6/π²) φ(dm)/(dm)` comes from the Euler product of `𝒫_d` (`IsGood.Pd_ge`).

Paper: §5.3, proof of Lemma 5.3(c).
-/

namespace Triples

open ZMod Filter Topology ArithmeticFunction
open scoped LSeries.notation

/-- For a real sequence and real `s ≠ 0`, the terms of the `L`-series are real. -/
theorem LSeries_term_ofReal (a : ℕ → ℝ) {s : ℝ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun n ↦ (a n : ℂ)) s n = ((a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero' (by exact_mod_cast hs)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (neg_ne_zero.2 hs), hs]
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [Real.rpow_neg hn0, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow hn0, div_eq_mul_inv]
    push_cast
    rfl

theorem LSeries_ofReal (a : ℕ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    LSeries (fun n ↦ (a n : ℂ)) s = ((∑' n : ℕ, a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  congr 1
  ext n
  exact LSeries_term_ofReal a hs n

theorem summable_of_LSeriesSummable_ofReal (a : ℕ → ℝ) {s : ℝ} (hs : s ≠ 0)
    (h : LSeriesSummable (fun n ↦ (a n : ℂ)) s) :
    Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-s)) := by
  rw [LSeriesSummable] at h
  have heq : LSeries.term (fun n ↦ (a n : ℂ)) s = fun n ↦ ((a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) :=
    funext (LSeries_term_ofReal a hs)
  rw [heq] at h
  exact Complex.summable_ofReal.1 h

/-! ### `L(1, χ₄) = π/4` -/

/-- `χ₄` as a real sequence. -/
noncomputable def chiR (k : ℕ) : ℝ := (chiAF k : ℝ)

theorem chiR_zero : chiR 0 = 0 := by simp [chiR]

theorem abs_psum_chiR_le (N : ℕ) (_ : 1 ≤ N) : |psum chiR N| ≤ 1 * (N : ℝ) ^ (0 : ℝ) := by
  rw [Real.rpow_zero, one_mul]
  have : psum chiR N = ∑ j ∈ Finset.Icc 1 N, (chiAF j : ℝ) := by
    rw [psum]
    rw [← Finset.sum_subset (s₁ := Finset.Icc 1 N) (s₂ := Finset.range (N + 1))]
    · rfl
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
    · intro k hk1 hk
      rw [Finset.mem_range] at hk1
      simp only [Finset.mem_Icc, not_and, not_le] at hk
      have : k = 0 := by
        by_contra h0
        have := hk (by omega)
        omega
      subst this
      exact chiR_zero
  rw [this]
  exact abs_sum_Icc_chiAF_le N

/-- The partial sums of the Leibniz series. -/
theorem sum_range_two_mul_chiR (K : ℕ) :
    ∑ k ∈ Finset.range (2 * K), chiR k / k = ∑ i ∈ Finset.range K, (-1 : ℝ) ^ i / (2 * i + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h0 : chiR (2 * K) = 0 := by
      rw [chiR, chiAF_apply, χ₄_nat_eq_if_mod_four]
      simp [Nat.mul_mod_right]
    have h1 : chiR (2 * K + 1) = (-1) ^ K := by
      rw [chiR, chiAF_apply, χ₄_eq_neg_one_pow (by omega)]
      rw [show (2 * K + 1) / 2 = K by omega]
      push_cast; rfl
    rw [h0, h1]
    push_cast
    ring

/-- **`L(1, χ₄) = π/4`**, in the form `S_χ = π/4` for the Abel sum of `χ₄`. -/
theorem tsum_abelTerm_chiR : ∑' k, abelTerm chiR 1 k = Real.pi / 4 := by
  have h := tendsto_sum_div chiR_zero (by norm_num : (0 : ℝ) < 1) abs_psum_chiR_le
  have h2 : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range (2 * K), chiR k / k) atTop
      (𝓝 (∑' k, abelTerm chiR 1 k)) :=
    h.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have h3 : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range (2 * K), chiR k / k) atTop
      (𝓝 (Real.pi / 4)) := by
    simp_rw [sum_range_two_mul_chiR]
    exact Real.tendsto_sum_pi_div_four
  exact tendsto_nhds_unique h2 h3

theorem summable_chiR {s : ℝ} (hs : 1 < s) : Summable (fun k : ℕ => chiR k * (k : ℝ) ^ (-s)) := by
  refine Summable.of_norm_bounded (Real.summable_nat_rpow.2 (by linarith : -s < -1)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
  have : |chiR k| ≤ 1 := abs_chiAF_le k
  calc |chiR k| * (k : ℝ) ^ (-s) ≤ 1 * (k : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ = (k : ℝ) ^ (-s) := one_mul _

/-- `∑ χ₄(k) k^(-s) → π/4` as `s → 1⁺`. -/
theorem tendsto_tsum_chiR :
    Tendsto (fun s : ℝ => ∑' k : ℕ, chiR k * (k : ℝ) ^ (-s)) (𝓝[>] 1) (𝓝 (Real.pi / 4)) := by
  rw [← tsum_abelTerm_chiR]
  exact tendsto_tsum_rpow chiR_zero (by norm_num : (0 : ℝ) < 1) abs_psum_chiR_le
    (fun s hs _ => summable_chiR hs)

theorem LSeriesSummable_ofReal_iff (a : ℕ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    LSeriesSummable (fun n ↦ (a n : ℂ)) s ↔ Summable (fun n : ℕ ↦ a n * (n : ℝ) ^ (-s)) := by
  rw [LSeriesSummable]
  have heq : LSeries.term (fun n ↦ (a n : ℂ)) s = fun n ↦ ((a n * (n : ℝ) ^ (-s) : ℝ) : ℂ) :=
    funext (LSeries_term_ofReal a hs)
  rw [heq]
  exact Complex.summable_ofReal

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- `β` as a real sequence. -/
noncomputable def betaR (P : PatternData a b) (d k : ℕ) : ℝ := (P.betaAF d k : ℝ)

theorem betaWeight_zero (d : ℕ) (σ : ℝ) : P.betaWeight d σ 0 = 0 := by
  simp [betaWeight]

theorem IsGood.summable_betaWeight_one {d : ℕ} (hd : P.IsGood d) :
    Summable (P.betaWeight d 1) := by
  obtain ⟨C, _, hC⟩ := P.betaWeight_sum_le (ε := 1 / 2) (by norm_num)
  apply summable_of_sum_range_le (fun n => P.betaWeight_nonneg d 1 n) (c := C * (d : ℝ) ^ (1 / 2 : ℝ))
  intro N
  have h := hC d hd (N - 1)
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num] at h
  calc ∑ n ∈ Finset.range N, P.betaWeight d 1 n = ∑ n ∈ Finset.Icc 1 (N - 1), P.betaWeight d 1 n := by
        symm
        apply Finset.sum_subset
        · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
        · intro k hk1 hk
          rw [Finset.mem_range] at hk1
          simp only [Finset.mem_Icc, not_and, not_le] at hk
          have : k = 0 := by
            by_contra h0
            have := hk (by omega)
            omega
          subst this
          exact betaWeight_zero d 1
    _ ≤ C * (d : ℝ) ^ (1 / 2 : ℝ) := h

theorem abs_betaR_mul_le {d : ℕ} {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    |P.betaR d n * (n : ℝ) ^ (-s)| ≤ P.betaWeight d 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [betaR, betaWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), betaWeight, betaR]
  gcongr

theorem IsGood.summable_betaR {d : ℕ} (hd : P.IsGood d) {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℕ ↦ P.betaR d n * (n : ℝ) ^ (-s)) :=
  Summable.of_norm_bounded hd.summable_betaWeight_one
    (fun n => by rw [Real.norm_eq_abs]; exact abs_betaR_mul_le hs n)

/-- `∑ β(n) n^(-s) → ∑ β(n)/n = 𝒫_d` as `s → 1⁺`. -/
theorem IsGood.tendsto_tsum_betaR {d : ℕ} (hd : P.IsGood d) :
    Tendsto (fun s : ℝ => ∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-s)) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-(1 : ℝ)))) := by
  apply tendsto_tsum_of_dominated_convergence hd.summable_betaWeight_one
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [betaR, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul]
      exact tendsto_const_nhds
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.const_mul
    exact ((Real.continuousAt_const_rpow hn0).comp continuous_neg.continuousAt).tendsto
  · filter_upwards [self_mem_nhdsWithin] with s hs n
    rw [Real.norm_eq_abs]
    exact abs_betaR_mul_le (le_of_lt hs) n

/-- The `L`-series identity `∑ χf(n) n^(-s) = L(s, χ) L(s, ψ) ∑ β(n) n^(-s)` for `s > 1`,
together with the absolute convergence of the left side. -/
theorem IsGood.LSeries_gR {d : ℕ} (hd : P.IsGood d) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n ↦ (P.gR d n : ℂ)) s ∧
    LSeries (fun n ↦ (P.gR d n : ℂ)) s =
      LSeries (fun n ↦ (chiR n : ℂ)) s * LSeries (fun n ↦ (psi (P.m d) n : ℂ)) s *
        LSeries (fun n ↦ (P.betaR d n : ℂ)) s := by
  have hs0 : s ≠ 0 := by linarith
  have hχ : LSeriesSummable ↗(chiAF : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_real (m := 1) _ hs
    intro n _
    rw [intCoe_apply, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact abs_chiAF_le n
  have hψ : LSeriesSummable ↗(psiAF (P.m d) : ArithmeticFunction ℂ) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_real (m := 1) _ hs
    intro n _
    rw [intCoe_apply, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, psiAF_apply]
    exact abs_psi_le _ n
  have hβ : LSeriesSummable ↗(P.betaAF d : ArithmeticFunction ℂ) s := by
    have := (LSeriesSummable_ofReal_iff (P.betaR d) hs0).2 (hd.summable_betaR hs.le)
    refine (LSeriesSummable_congr s (fun {n} _ => ?_)).1 this
    rw [intCoe_apply, betaR, Complex.ofReal_intCast]
  have hfun : (fun n ↦ (P.gR d n : ℂ)) =
      ↗((chiAF : ArithmeticFunction ℂ) * (psiAF (P.m d) : ArithmeticFunction ℂ) *
        (P.betaAF d : ArithmeticFunction ℂ)) := by
    ext n
    rw [← intCoe_mul, ← intCoe_mul, ← P.gAF_eq, intCoe_apply, gR, Complex.ofReal_intCast]
  rw [hfun]
  refine ⟨LSeriesSummable_mul (LSeriesSummable_mul hχ hψ) hβ, ?_⟩
  rw [LSeries_mul' (LSeriesSummable_mul hχ hψ) hβ, LSeries_mul' hχ hψ]
  congr 2

/-- **The product formula** `𝔏_d = (π/4) L(1, ψ) 𝒫_d` with `𝒫_d = ∑ β(n)/n` (proof of
Lemma 5.3(c)): both sides are limits of `∑ χf(n) n^(-s) = L(s, χ) L(s, ψ) ∑ β(n) n^(-s)` as
`s → 1⁺`. -/
theorem IsGood.Ld_eq_product (hPV : PolyaVinogradov) {d : ℕ} (hd : P.IsGood d)
    [NeZero (8 * (P.m d).natAbs)] (ψ' : DirichletCharacter ℂ (8 * (P.m d).natAbs))
    (hne : ψ' ≠ 1) (hval : ∀ n : ℕ, ψ' n = (psi (P.m d) n : ℂ)) :
    (P.Ld d : ℂ) = (Real.pi / 4 : ℂ) * DirichletCharacter.LFunction ψ' 1 *
      ((∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ) := by
  set F := fun s : ℝ => ∑' k : ℕ, P.gR d k * (k : ℝ) ^ (-s) with hFdef
  obtain ⟨C, -, hC⟩ := P.abs_psum_gR_le hPV (ε := 1 / 4) (by norm_num)
  have hθ : (1 / 2 + 1 / 4 : ℝ) < 1 := by norm_num
  have hF : Tendsto F (𝓝[>] 1) (𝓝 (P.Ld d)) := by
    rw [(hd.Ld_eq_and_tendsto hPV).1]
    apply tendsto_tsum_rpow (gR_zero d) hθ (hC d hd)
    intro s hs _
    exact (LSeriesSummable_ofReal_iff (P.gR d) (by linarith)).1 (hd.LSeries_gR hs).1
  have hψ : Tendsto (fun s : ℝ => DirichletCharacter.LFunction ψ' (s : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction ψ' 1)) := by
    have hc : Tendsto (fun s : ℝ => DirichletCharacter.LFunction ψ' (s : ℂ)) (𝓝 1)
        (𝓝 (DirichletCharacter.LFunction ψ' ((1 : ℝ) : ℂ))) :=
      ((DirichletCharacter.differentiable_LFunction hne).continuous.comp
        Complex.continuous_ofReal).tendsto 1
    rw [Complex.ofReal_one] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun s : ℝ => ((∑' k : ℕ, chiR k * (k : ℝ) ^ (-s) : ℝ) : ℂ) *
      DirichletCharacter.LFunction ψ' s * ((∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-s) : ℝ) : ℂ))
      (𝓝[>] 1) (𝓝 (((Real.pi / 4 : ℝ) : ℂ) * DirichletCharacter.LFunction ψ' 1 *
        ((∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-(1 : ℝ)) : ℝ) : ℂ))) :=
    (((Complex.continuous_ofReal.tendsto _).comp tendsto_tsum_chiR).mul hψ).mul
      ((Complex.continuous_ofReal.tendsto _).comp hd.tendsto_tsum_betaR)
  have hFc : Tendsto (fun s : ℝ => ((F s : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((P.Ld d : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hF
  have heq : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ((∑' k : ℕ, chiR k * (k : ℝ) ^ (-s) : ℝ) : ℂ) *
      DirichletCharacter.LFunction ψ' s * ((∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-s) : ℝ) : ℂ) =
        ((F s : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : (1 : ℝ) < s := hs
    have h := (hd.LSeries_gR hs1).2
    rw [LSeries_ofReal _ (by linarith), LSeries_ofReal _ (by linarith),
      LSeries_ofReal _ (by linarith)] at h
    have hψs : LSeries (fun n ↦ (psi (P.m d) n : ℂ)) s = DirichletCharacter.LFunction ψ' s := by
      rw [DirichletCharacter.LFunction_eq_LSeries ψ' (by simpa using hs1)]
      congr 1; ext n; rw [hval n]
    rw [hψs] at h
    exact h.symm
  have := tendsto_nhds_unique hFc (hprod.congr' heq)
  rw [this]
  push_cast
  ring

end PatternData

/-! ### The Euler product of `𝒫_d` -/

/-- `ϱ(nk) ≤ k ϱ(n)`: every root modulo `nk` reduces to a root modulo `n`, and each root
modulo `n` has at most `k` lifts. -/
theorem rho_mul_le (m : ℤ) {n : ℕ} (hn : 0 < n) (k : ℕ) : rho m (n * k) ≤ k * rho m n := by
  classical
  unfold rho
  set S := (Finset.range (n * k)).filter (fun ν : ℕ => ((n * k : ℕ) : ℤ) ∣ (ν : ℤ) ^ 2 + m)
  set R := (Finset.range n).filter (fun ν : ℕ => (n : ℤ) ∣ (ν : ℤ) ^ 2 + m)
  have himage : S.image (fun ν => ν % n) ⊆ R := by
    intro μ hμ
    rw [Finset.mem_image] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    rw [Finset.mem_filter] at hν ⊢
    refine ⟨Finset.mem_range.2 (Nat.mod_lt _ hn), ?_⟩
    have h1 : (n : ℤ) ∣ (ν : ℤ) ^ 2 + m :=
      dvd_trans (by push_cast; exact Dvd.intro _ rfl) hν.2
    have h2 : (n : ℤ) ∣ (ν : ℤ) - ((ν % n : ℕ) : ℤ) := by
      have : ((ν % n : ℕ) : ℤ) = (ν : ℤ) % (n : ℤ) := by push_cast; rfl
      rw [this]
      exact ⟨(ν : ℤ) / (n : ℤ), by rw [Int.emod_def]; ring⟩
    have h3 : (n : ℤ) ∣ ((ν : ℤ) ^ 2 + m) - (((ν % n : ℕ) : ℤ) ^ 2 + m) := by
      have : ((ν : ℤ) ^ 2 + m) - (((ν % n : ℕ) : ℤ) ^ 2 + m) =
          ((ν : ℤ) - ((ν % n : ℕ) : ℤ)) * ((ν : ℤ) + ((ν % n : ℕ) : ℤ)) := by ring
      rw [this]
      exact Dvd.dvd.mul_right h2 _
    have := dvd_sub h1 h3
    rwa [sub_sub_cancel] at this
  calc S.card ≤ k * (S.image (fun ν => ν % n)).card := by
        apply Finset.card_le_mul_card_image
        intro μ _
        calc (S.filter (fun ν => ν % n = μ)).card ≤ (Finset.range k).card := by
              apply Finset.card_le_card_of_injOn (fun ν => ν / n)
              · intro ν hν
                rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hν
                rw [Finset.coe_range, Set.mem_Iio]
                exact Nat.div_lt_of_lt_mul hν.1.1
              · intro ν₁ h₁ ν₂ h₂ heq
                rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
                rw [← Nat.mod_add_div ν₁ n, ← Nat.mod_add_div ν₂ n, h₁.2, h₂.2]
                simp only at heq
                rw [heq]
          _ = k := Finset.card_range k
    _ ≤ k * R.card := by gcongr

/-- `ϱ(p) = 1` for an odd prime `p ∣ m`. -/
theorem rho_prime_of_dvd {m : ℤ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : (p : ℤ) ∣ m) :
    rho m p = 1 := by
  have := Fact.mk hp
  have h := rho_prime (m := m) hp2
  have h0 : legendreSym p (-m) = 0 := by
    rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (dvd_neg).2 hpm
  rw [h0, add_zero] at h
  exact_mod_cast h

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- `β(n)/n`. -/
noncomputable def fP (P : PatternData a b) (d n : ℕ) : ℝ := P.betaR d n * (n : ℝ) ^ (-(1 : ℝ))

theorem fP_zero (d : ℕ) : P.fP d 0 = 0 := by simp [fP, betaR]

theorem fP_one (d : ℕ) : P.fP d 1 = 1 := by simp [fP, betaR, P.betaAF_one d]

theorem fP_mul (d : ℕ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    P.fP d (m * n) = P.fP d m * P.fP d n := by
  simp only [fP, betaR, (P.betaAF_isMultiplicative d).map_mul_of_coprime hmn, Int.cast_mul,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem fP_prime_pow (d p e : ℕ) : P.fP d (p ^ e) = (P.betaAF d (p ^ e) : ℝ) / (p : ℝ) ^ e := by
  rw [fP, betaR, Real.rpow_neg_one, Nat.cast_pow, div_eq_mul_inv]

theorem IsGood.summable_norm_fP {d : ℕ} (hd : P.IsGood d) : Summable (fun n ↦ ‖P.fP d n‖) := by
  refine Summable.of_norm_bounded hd.summable_betaWeight_one (fun n => ?_)
  rw [norm_norm, Real.norm_eq_abs]
  exact abs_betaR_mul_le le_rfl n

theorem IsGood.summable_fP_prime_pow {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) :
    Summable (fun e : ℕ ↦ P.fP d (p ^ e)) :=
  (hd.summable_norm_fP.of_norm).comp_injective (Nat.pow_right_injective hp.two_le)

/-- The Euler factor at `2` is `1`. -/
theorem tsum_fP_two (d : ℕ) : ∑' e : ℕ, P.fP d (2 ^ e) = 1 := by
  rw [tsum_eq_single 0]
  · simp [P.fP_one d]
  · intro e he
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    rw [fP_prime_pow, P.betaAF_two_pow]; simp

/-- The Euler factor at `d` is `1 - 1/d`. -/
theorem IsGood.tsum_fP_d {d : ℕ} (hd : P.IsGood d) : ∑' e : ℕ, P.fP d (d ^ e) = 1 - 1 / d := by
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, fP_prime_pow, P.betaAF_one d, hd.betaAF_d]
    ring
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 2 := ⟨e - 2, by omega⟩
    rw [fP_prime_pow, hd.betaAF_d_pow]; simp

/-- The Euler factor at an odd prime `p ∤ dm` is `1 - 1/p²`. -/
theorem IsGood.tsum_fP_of_not_dvd {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d) (hpm : ¬ (p : ℤ) ∣ P.m d) :
    ∑' e : ℕ, P.fP d (p ^ e) = 1 - 1 / (p : ℝ) ^ 2 := by
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, fP_prime_pow, P.betaAF_one d,
      hd.betaAF_prime_of_not_dvd hp hp2 hpd hpm, hd.betaAF_prime_sq_of_not_dvd hp hp2 hpd hpm]
    ring
  · intro e he
    simp only [Finset.mem_range, not_lt] at he
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 3 := ⟨e - 3, by omega⟩
    rw [fP_prime_pow, hd.betaAF_prime_pow_of_not_dvd hp hp2 hpd hpm]; simp

/-- The Euler factor at an odd prime `p ∣ m` is at least `1 - 1/p`: it equals
`(1 - χ(p)/p) ∑_e χ(p)^e ϱ(p^e)/p^e`, and the alternating series has decreasing terms. -/
theorem IsGood.tsum_fP_of_dvd_ge {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : (p : ℤ) ∣ P.m d) : 1 - 1 / (p : ℝ) ≤ ∑' e : ℕ, P.fP d (p ^ e) := by
  set c : ℝ := (chiAF p : ℝ) with hc
  set r : ℕ → ℝ := fun e => (rho (P.m d) (p ^ e) : ℝ) / (p : ℝ) ^ e with hr
  set u : ℕ → ℝ := fun e => c ^ e * r e with hu
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hc2 : c ^ 2 = 1 := by
    have := chiAF_sq_of_odd (Nat.odd_iff.1 (hp.odd_of_ne_two hp2))
    rw [hc]; exact_mod_cast this
  have hcabs : |c| = 1 := by
    have h := sq_abs c
    rw [hc2] at h
    have h0 := abs_nonneg c
    nlinarith
  have hr0 : r 0 = 1 := by simp [hr, rho_one]
  have hr1 : r 1 = 1 / p := by simp [hr, rho_prime_of_dvd hp hp2 hpm]
  have hr_nonneg : ∀ e, 0 ≤ r e := fun e => by positivity
  have hr_anti : ∀ e, r (e + 1) ≤ r e := by
    intro e
    have h := rho_mul_le (P.m d) (pow_pos hp.pos e) p
    rw [← pow_succ] at h
    have h' : (rho (P.m d) (p ^ (e + 1)) : ℝ) ≤ p * rho (P.m d) (p ^ e) := by exact_mod_cast h
    simp only [hr]
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ (p : ℝ) e]
    have := pow_pos hp0 e
    nlinarith
  have hm0 : P.m d ≠ 0 := (P.m_pos hd.d₁_lt).ne'
  have hr_le : ∀ e, r e ≤ 2 * (p : ℝ) ^ (padicValInt p (P.m d)) * (1 / (p : ℝ)) ^ e := by
    intro e
    have h := rho_prime_pow_le_nat hm0 hp hp2 e
    have h' : (rho (P.m d) (p ^ e) : ℝ) ≤ 2 * (p : ℝ) ^ (padicValInt p (P.m d)) := by
      have : rho (P.m d) (p ^ e) ≤ 2 * p ^ (padicValInt p (P.m d)) :=
        h.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hp.pos (by omega)))
      exact_mod_cast this
    simp only [hr]
    rw [one_div_pow, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right h' (by positivity)
  have hr_summ : Summable r := by
    refine Summable.of_nonneg_of_le hr_nonneg hr_le ?_
    exact (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one hp0]; exact hp1)).mul_left _
  have hu_summ : Summable u := by
    refine Summable.of_norm_bounded hr_summ (fun e => ?_)
    simp only [hu, norm_mul, norm_pow, Real.norm_eq_abs, hcabs, one_pow, one_mul,
      abs_of_nonneg (hr_nonneg e)]
    exact le_rfl
  have hfP : ∀ e, P.fP d (p ^ (e + 1)) = u (e + 1) - (c / p) * u e := by
    intro e
    rw [fP_prime_pow, hd.betaAF_prime_pow_of_dvd hp hp2 hpm e]
    simp only [hu, hr]
    push_cast
    rw [← hc]
    field_simp
    ring
  have hu0 : u 0 = 1 := by simp [hu, hr0]
  have hu_summ1 : Summable (fun e => u (e + 1)) := (summable_nat_add_iff 1).2 hu_summ
  have hE : ∑' e : ℕ, P.fP d (p ^ e) = (1 - c / p) * ∑' e, u e := by
    rw [(hd.summable_fP_prime_pow hp).tsum_eq_zero_add, hu_summ.tsum_eq_zero_add, pow_zero,
      P.fP_one d, tsum_congr hfP, hu_summ1.tsum_sub (hu_summ.mul_left _), tsum_mul_left,
      hu_summ.tsum_eq_zero_add, hu0]
    ring
  rw [hE]
  have hcases : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hcases with h1 | h1
  · -- `χ(p) = 1`: all terms are non-negative
    have hU : 1 ≤ ∑' e, u e := by
      have huu : u = r := by ext e; simp [hu, h1]
      rw [huu, ← hr0]
      exact hr_summ.le_tsum 0 (fun j _ => hr_nonneg j)
    rw [h1]
    have : 0 ≤ 1 - 1 / (p : ℝ) := by
      rw [sub_nonneg, div_le_one hp0]; exact hp1.le
    nlinarith
  · -- `χ(p) = -1`: an alternating series with decreasing terms
    have hue : ∀ k, u (2 * k) = r (2 * k) := by
      intro k; simp [hu, h1, pow_mul]
    have huo : ∀ k, u (2 * k + 1) = -r (2 * k + 1) := by
      intro k; simp [hu, h1, pow_succ, pow_mul]
    have hre : Summable (fun k => r (2 * k)) :=
      hr_summ.comp_injective (fun a b h => by simpa using h)
    have hro : Summable (fun k => r (2 * k + 1)) :=
      hr_summ.comp_injective (fun a b h => by simpa using h)
    have hU : ∑' e, u e = ∑' k, (r (2 * k) - r (2 * k + 1)) := by
      rw [← tsum_even_add_odd (f := u) (by simpa [hue] using hre) (by simpa [huo] using hro.neg)]
      simp only [hue, huo]
      rw [hre.tsum_sub hro, tsum_neg]
      ring
    have hU1 : 1 - 1 / (p : ℝ) ≤ ∑' e, u e := by
      rw [hU]
      have h := (hre.sub hro).le_tsum 0 (fun j _ => by
        have := hr_anti (2 * j); linarith)
      simp only [mul_zero, zero_add] at h
      rw [hr0, hr1] at h
      exact h
    rw [h1]
    have hpinv : 0 ≤ 1 / (p : ℝ) := by positivity
    have hpinv1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1.le
    have : (1 - -1 / (p : ℝ)) = 1 + 1 / p := by ring
    rw [this]
    nlinarith

end PatternData

/-- `∏_{p < N} (1 - p^(-2)) ≥ 6/π²`, from `∏_{p < N} (1 - p^(-2))⁻¹ = ∑_{n N-smooth} n^(-2) ≤ ζ(2)`. -/
theorem prod_primesBelow_one_sub_inv_sq_ge (N : ℕ) :
    6 / Real.pi ^ 2 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => 1 / (n : ℝ) ^ 2
      map_one' := by simp
      map_mul' := by intro x y; push_cast; rw [mul_pow, one_div_mul_one_div] }
  have hsum : Summable f := hasSum_zeta_two.summable
  have h := EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum N
  have hle : ∑' m : N.smoothNumbers, f m ≤ Real.pi ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]
    exact hsum.tsum_subtype_le _ _ (fun n => by show (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2; positivity)
  have hpos : ∀ p ∈ N.primesBelow, 0 < 1 - 1 / (p : ℝ) ^ 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have : 1 / (p : ℝ) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hprod_pos : 0 < ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2) := Finset.prod_pos hpos
  have h2 : (∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2))⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← Finset.prod_inv_distrib]
    calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ = ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := rfl
      _ = ∑' m : N.smoothNumbers, f m := h
      _ ≤ Real.pi ^ 2 / 6 := hle
  have hπ : 0 < Real.pi ^ 2 / 6 := by positivity
  calc 6 / Real.pi ^ 2 = (Real.pi ^ 2 / 6)⁻¹ := by rw [inv_div]
    _ ≤ ((∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hprod_pos) h2
    _ = ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2) := inv_inv _

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- Each Euler factor of `𝒫_d` is at least `(1 - p^(-2)) (1 - 1/p)^[p ∣ dm]`. -/
theorem IsGood.tsum_fP_ge {d : ℕ} (hd : P.IsGood d) {p : ℕ} (hp : p.Prime) :
    (1 - 1 / (p : ℝ) ^ 2) * (if p ∣ d * (P.m d).natAbs then 1 - (p : ℝ)⁻¹ else 1) ≤
      ∑' e : ℕ, P.fP d (p ^ e) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hsq : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
  have hsq1 : 1 / (p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hite0 : 0 ≤ (if p ∣ d * (P.m d).natAbs then 1 - (p : ℝ)⁻¹ else 1) := by
    split_ifs <;> linarith
  have hite1 : (if p ∣ d * (P.m d).natAbs then 1 - (p : ℝ)⁻¹ else 1) ≤ 1 := by
    split_ifs <;> linarith
  by_cases h2 : p = 2
  · subst h2
    rw [tsum_fP_two]
    nlinarith
  by_cases hpd : p = d
  · subst hpd
    rw [hd.tsum_fP_d, ite_eq_left (Dvd.intro _ rfl), one_div (p : ℝ)]
    nlinarith [mul_nonneg hsq (sub_nonneg.2 hinv)]
  by_cases hpm : (p : ℤ) ∣ P.m d
  · have hpD : p ∣ d * (P.m d).natAbs := Dvd.dvd.mul_left (Int.natCast_dvd.1 hpm) _
    rw [ite_eq_left hpD]
    have hE := hd.tsum_fP_of_dvd_ge hp h2 hpm
    rw [one_div (p : ℝ)] at hE
    nlinarith [mul_nonneg hsq (sub_nonneg.2 hinv)]
  · have hpD : ¬ p ∣ d * (P.m d).natAbs := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · exact hpd ((Nat.prime_dvd_prime_iff_eq hp hd.prime).1 h')
      · exact hpm (Int.natCast_dvd.2 h')
    rw [ite_eq_right hpD, mul_one, hd.tsum_fP_of_not_dvd hp h2 hpd hpm]

/-- **The lower bound for `𝒫_d`**: `𝒫_d ≥ (6/π²) φ(dm)/(dm)`. -/
theorem IsGood.Pd_ge {d : ℕ} (hd : P.IsGood d) :
    6 / Real.pi ^ 2 * ((d * (P.m d).natAbs).totient : ℝ) / (d * (P.m d).natAbs) ≤
      ∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-(1 : ℝ)) := by
  set D := d * (P.m d).natAbs with hD
  have hM0 : (P.m d).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (P.m_pos hd.d₁_lt).ne'
  have hD0 : D ≠ 0 := Nat.mul_ne_zero hd.prime.ne_zero hM0
  have hlim := EulerProduct.eulerProduct (P.fP_one d) (fun h => P.fP_mul d h)
    hd.summable_norm_fP (P.fP_zero d)
  have hPd : ∑' n : ℕ, P.betaR d n * (n : ℝ) ^ (-(1 : ℝ)) = ∑' n : ℕ, P.fP d n := rfl
  rw [hPd]
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop D] with N hN
  have hnn : ∀ p ∈ N.primesBelow,
      0 ≤ (1 - 1 / (p : ℝ) ^ 2) * (if p ∣ D then 1 - (p : ℝ)⁻¹ else 1) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have h1 : 0 ≤ 1 - 1 / (p : ℝ) ^ 2 := by
      have : 1 / (p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
      linarith
    have h2 : 0 ≤ (if p ∣ D then 1 - (p : ℝ)⁻¹ else 1) := by
      split_ifs
      · have := inv_le_one_of_one_le₀ hp1.le; linarith
      · norm_num
    exact mul_nonneg h1 h2
  have hfilter : N.primesBelow.filter (· ∣ D) = D.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, hpD⟩; exact ⟨hp, hpD, hD0⟩
    · rintro ⟨hp, hpD, _⟩
      exact ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hpD) hN, hp⟩, hpD⟩
  have hsecond : ∏ p ∈ N.primesBelow, (if p ∣ D then 1 - (p : ℝ)⁻¹ else 1) =
      (D.totient : ℝ) / D := by
    rw [← Finset.prod_filter, hfilter, totient_div_eq_prod D hD0]
  have hsecond0 : 0 ≤ (D.totient : ℝ) / D := by positivity
  calc 6 / Real.pi ^ 2 * ((d * (P.m d).natAbs).totient : ℝ) / (d * (P.m d).natAbs)
      = 6 / Real.pi ^ 2 * ((D.totient : ℝ) / D) := by rw [hD]; push_cast; ring
    _ ≤ (∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)) *
          ∏ p ∈ N.primesBelow, (if p ∣ D then 1 - (p : ℝ)⁻¹ else 1) := by
        rw [hsecond]
        exact mul_le_mul_of_nonneg_right (prod_primesBelow_one_sub_inv_sq_ge N) hsecond0
    _ = ∏ p ∈ N.primesBelow, ((1 - 1 / (p : ℝ) ^ 2) * (if p ∣ D then 1 - (p : ℝ)⁻¹ else 1)) :=
        (Finset.prod_mul_distrib).symm
    _ ≤ ∏ p ∈ N.primesBelow, ∑' e : ℕ, P.fP d (p ^ e) :=
        Finset.prod_le_prod₀ hnn (fun p hp => hd.tsum_fP_ge (Nat.prime_of_mem_primesBelow hp))

end PatternData

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- **Lemma 5.3(c)**, the product formula: `𝔏_d = L(1, χ) L(1, ψ) 𝒫_d` with
`L(1, χ) = π/4` and `𝒫_d ≥ (6/π²) φ(dm)/(dm)` (`Pd` below). -/
theorem Ld_product (hPV : PolyaVinogradov) {d : ℕ} (hd : P.IsGood d)
    [NeZero (8 * (P.m d).natAbs)] :
    ∃ ψ' : DirichletCharacter ℂ (8 * (P.m d).natAbs), (∀ n : ℕ, ψ' n = (psi (P.m d) n : ℂ)) ∧
      ∃ Pd : ℝ, 6 / Real.pi ^ 2 * ((d * (P.m d).natAbs).totient : ℝ) / (d * (P.m d).natAbs) ≤ Pd ∧
        (P.Ld d : ℂ) = (Real.pi / 4 : ℂ) * DirichletCharacter.LFunction ψ' 1 * Pd := by
  obtain ⟨ψ', hne, -, hval⟩ := hd.psi_character
  exact ⟨ψ', hval, _, hd.Pd_ge, hd.Ld_eq_product hPV ψ' hne hval⟩

end PatternData

end Triples
