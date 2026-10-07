import TriplesFinal.GoodPrimes.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The primes that are not good

The primes `d ≤ y` with `d ≡ d₀ (mod 2^J)` that are not good are: the `O(1)` primes `d ≤ d₁`;
the `O(1)` primes with `m_d = s²`, because `(d + c)² - s² = -4A(B - A) ≠ 0` has finitely many
solutions; and the primes with `m_d = 3s²`. The paper bounds the number of the latter by
`O(log y)` (the solutions of `(d + c)² - 3s² = -4A(B - A)` form finitely many orbits under the
units of `ℤ[√3]`). Since the deduction only uses primes in a dyadic range `(y/2, y]`, we prove
the simpler bound `O(1)` for such a range (`pell_dyadic`): the ratios `s/D` of the solutions with
`D ∈ (Z, 4Z]` lie within `|k|/Z²` of `1/√3` and are pairwise at least `1/(16Z²)` apart.

Paper: §4, deduction of Theorems 1.1 and 1.3, second paragraph.
-/

namespace Triples

/-- **Dyadic Pell count.** For `Z ≥ 1`, the number of `D ∈ (Z, 4Z]` such that
`D² - 3s² = k` for some `s ∈ ℤ` is at most `32|k| + 1`. -/
theorem pell_dyadic (k : ℤ) (Z : ℝ) (hZ : 1 ≤ Z) :
    {D : ℤ | Z < D ∧ (D : ℝ) ≤ 4 * Z ∧ ∃ s : ℤ, D ^ 2 - 3 * s ^ 2 = k}.ncard ≤
      32 * k.natAbs + 1 := by
  classical
  set S := {D : ℤ | Z < D ∧ (D : ℝ) ≤ 4 * Z ∧ ∃ s : ℤ, D ^ 2 - 3 * s ^ 2 = k} with hS
  have hZpos : 0 < Z := by linarith
  have hSfin : S.Finite := by
    apply (Set.finite_Icc (0 : ℤ) ⌈4 * Z⌉).subset
    intro D hD
    obtain ⟨h1, h2, -⟩ := hD
    constructor
    · have : (0 : ℝ) < D := by linarith
      exact_mod_cast this.le
    · exact Int.cast_le.1 (h2.trans (Int.le_ceil _))
  -- the non-negative `s` attached to `D`
  have hs : ∀ D ∈ S, ∃ s : ℤ, 0 ≤ s ∧ D ^ 2 - 3 * s ^ 2 = k := by
    rintro D ⟨-, -, s, hs⟩
    exact ⟨|s|, abs_nonneg s, by rw [sq_abs]; exact hs⟩
  choose! σ hσ0 hσ using hs
  set r : ℤ → ℝ := fun D => (σ D : ℝ) / D with hr
  set c₀ : ℝ := Real.sqrt 3 / 3 with hc₀
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsq3 : 1 ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- `|r(D) - 1/√3| ≤ |k|/Z²`
  have hclose : ∀ D ∈ S, |r D - c₀| ≤ |(k : ℝ)| / Z ^ 2 := by
    intro D hD
    have hZD : Z < D := hD.1
    have hDpos : (0 : ℝ) < D := by linarith
    have hs0 : (0 : ℝ) ≤ σ D := by exact_mod_cast hσ0 D hD
    have hk : (D : ℝ) ^ 2 - 3 * (σ D : ℝ) ^ 2 = k := by exact_mod_cast hσ D hD
    have hprod : ((D : ℝ) - Real.sqrt 3 * σ D) * ((D : ℝ) + Real.sqrt 3 * σ D) = k := by
      rw [← hk]; linear_combination (-(σ D : ℝ) ^ 2) * h3
    have hpos : (D : ℝ) ≤ (D : ℝ) + Real.sqrt 3 * σ D := by
      have : 0 ≤ Real.sqrt 3 * σ D := by positivity
      linarith
    have habs : |(D : ℝ) - Real.sqrt 3 * σ D| ≤ |(k : ℝ)| / D := by
      rw [le_div_iff₀ hDpos, ← hprod, abs_mul]
      have : |(D : ℝ) + Real.sqrt 3 * σ D| = (D : ℝ) + Real.sqrt 3 * σ D := abs_of_pos (by linarith)
      rw [this]
      exact mul_le_mul_of_nonneg_left hpos (abs_nonneg _)
    have e : r D - c₀ = -((D : ℝ) - Real.sqrt 3 * σ D) / (Real.sqrt 3 * D) := by
      simp only [hr, hc₀]
      field_simp
      linear_combination (-(D : ℝ)) * h3
    rw [e, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 3),
      abs_of_pos hDpos, div_le_div_iff₀ (by positivity) (by positivity)]
    have hZD2 : Z ^ 2 ≤ (D : ℝ) * D := by nlinarith
    calc |(D : ℝ) - Real.sqrt 3 * σ D| * Z ^ 2 ≤ |(k : ℝ)| / D * ((D : ℝ) * D) := by
          apply mul_le_mul habs hZD2 (by positivity) (by positivity)
      _ = |(k : ℝ)| * D := by field_simp
      _ ≤ |(k : ℝ)| * (Real.sqrt 3 * D) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          nlinarith
  -- distinct `D` have ratios at least `1/(16 Z²)` apart
  have hsep : ∀ D ∈ S, ∀ D' ∈ S, D ≠ D' → 1 / (16 * Z ^ 2) ≤ |r D - r D'| := by
    intro D hD D' hD' hne
    have hZD : Z < D := hD.1
    have hD4 : (D : ℝ) ≤ 4 * Z := hD.2.1
    have hZD' : Z < D' := hD'.1
    have hD4' : (D' : ℝ) ≤ 4 * Z := hD'.2.1
    have hDpos : (0 : ℝ) < D := by linarith
    have hDpos' : (0 : ℝ) < D' := by linarith
    have hk := hσ D hD
    have hk' := hσ D' hD'
    -- the integer `σ(D) D' - σ(D') D` is non-zero
    have hY : σ D * D' - σ D' * D ≠ 0 := by
      intro h0
      have hDZ : (0 : ℤ) < D := by exact_mod_cast hDpos
      have hDZ' : (0 : ℤ) < D' := by exact_mod_cast hDpos'
      -- then `k D'² = k D²`
      have e1 : k * D' ^ 2 = k * D ^ 2 := by
        have : σ D * D' = σ D' * D := by linarith
        linear_combination (-(D' ^ 2)) * hk + D ^ 2 * hk' - 3 * (σ D * D' + σ D' * D) * this
      by_cases hk0 : k = 0
      · -- `D² = 3σ²` is impossible for `D ≠ 0`: compare the `3`-adic valuations
        exfalso
        have hD2 : D ^ 2 = 3 * σ D ^ 2 := by linarith
        have hσpos : (0 : ℤ) < σ D := by
          rcases (hσ0 D hD).lt_or_eq with h | h
          · exact h
          · rw [← h] at hD2; nlinarith
        have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hnat : D.natAbs ^ 2 = 3 * (σ D).natAbs ^ 2 := by
          have := congrArg Int.natAbs hD2
          simpa [Int.natAbs_mul, Int.natAbs_pow] using this
        have hb0 : (σ D).natAbs ≠ 0 := by omega
        have hv := congrArg (padicValNat 3) hnat
        rw [padicValNat.pow, padicValNat.mul (by norm_num) (pow_ne_zero 2 hb0), padicValNat.pow,
          padicValNat.self (by norm_num)] at hv
        omega
      · have hsq : D' ^ 2 = D ^ 2 := mul_left_cancel₀ hk0 e1
        have hmul : (D' - D) * (D' + D) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 hmul with h | h
        · exact hne (by linarith)
        · linarith
    have hY1 : (1 : ℝ) ≤ |((σ D * D' - σ D' * D : ℤ) : ℝ)| := by
      have := Int.one_le_abs hY
      exact_mod_cast this
    have e : r D - r D' = ((σ D * D' - σ D' * D : ℤ) : ℝ) / ((D : ℝ) * D') := by
      simp only [hr]; push_cast; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (D : ℝ) * D'),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : (D : ℝ) * D' ≤ 16 * Z ^ 2 := by nlinarith
    nlinarith
  -- injection into `range (32|k| + 1)`
  set N : ℕ := 32 * k.natAbs + 1 with hN
  set f : ℤ → ℕ := fun D => ⌊(r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2)⌋₊ with hf
  have hmaps : ∀ D ∈ hSfin.toFinset, f D ∈ Finset.range N := by
    intro D hD
    rw [Set.Finite.mem_toFinset] at hD
    rw [Finset.mem_range]
    have h1 := abs_le.1 (hclose D hD)
    have hle : (r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) ≤ 32 * |(k : ℝ)| := by
      have hZ2 : 0 < Z ^ 2 := by positivity
      have : r D - c₀ + |(k : ℝ)| / Z ^ 2 ≤ 2 * (|(k : ℝ)| / Z ^ 2) := by linarith
      calc (r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2)
          ≤ 2 * (|(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) := by gcongr
        _ = 32 * |(k : ℝ)| := by field_simp; ring
    have hfl : f D ≤ 32 * k.natAbs := by
      simp only [hf]
      apply Nat.floor_le_of_le
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hle
    omega
  have hinj : Set.InjOn f (hSfin.toFinset : Set ℤ) := by
    intro D hD D' hD' hfeq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hD hD'
    by_contra hne
    have hsep' := hsep D hD D' hD' hne
    have h0 : ∀ E ∈ S, 0 ≤ (r E - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) := by
      intro E hE
      have := (abs_le.1 (hclose E hE)).1
      have : 0 ≤ r E - c₀ + |(k : ℝ)| / Z ^ 2 := by linarith
      positivity
    have hlt : |(r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) -
        (r D' - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2)| < 1 := by
      have ha := Nat.floor_le (h0 D hD)
      have hb := Nat.floor_le (h0 D' hD')
      have ha' := Nat.lt_floor_add_one ((r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2))
      have hb' := Nat.lt_floor_add_one ((r D' - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2))
      simp only [hf] at hfeq
      rw [hfeq] at ha ha'
      rw [abs_lt]; constructor <;> linarith
    have e : (r D - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) -
        (r D' - c₀ + |(k : ℝ)| / Z ^ 2) * (16 * Z ^ 2) = (r D - r D') * (16 * Z ^ 2) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 16 * Z ^ 2)] at hlt
    have : 1 / (16 * Z ^ 2) * (16 * Z ^ 2) ≤ |r D - r D'| * (16 * Z ^ 2) :=
      mul_le_mul_of_nonneg_right hsep' (by positivity)
    rw [one_div_mul_cancel (by positivity)] at this
    linarith
  rw [Set.ncard_eq_toFinset_card S hSfin]
  calc hSfin.toFinset.card ≤ (Finset.range N).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = N := Finset.card_range N

/-- For `k ≠ 0`, `D² - s² = k` has only finitely many solutions `D`: `|D| ≤ |k|`. -/
theorem sq_sub_sq_finite (k : ℤ) (hk : k ≠ 0) :
    {D : ℤ | ∃ s : ℤ, D ^ 2 - s ^ 2 = k}.Finite := by
  apply (Set.finite_Icc (-|k|) |k|).subset
  rintro D ⟨s, hs⟩
  have h1 : (D - s) * (D + s) = k := by rw [← hs]; ring
  have hne1 : D - s ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact hk h1.symm
  have hne2 : D + s ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact hk h1.symm
  have ha1 : 1 ≤ |D - s| := Int.one_le_abs hne1
  have ha2 : 1 ≤ |D + s| := Int.one_le_abs hne2
  have habs : |D - s| * |D + s| = |k| := by rw [← abs_mul, h1]
  have hb1 : |D - s| ≤ |k| := by nlinarith
  have hb2 : |D + s| ≤ |k| := by nlinarith
  have h2D : |2 * D| ≤ 2 * |k| := by
    have e : 2 * D = (D - s) + (D + s) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  rw [abs_mul, abs_two] at h2D
  have hD : |D| ≤ |k| := by linarith
  exact abs_le.1 hD

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

theorem k_ne_zero : -4 * P.A * (P.B - P.A) ≠ 0 := by
  have hA := P.adm.2.2.1
  have hAB := P.adm.2.2.2.1
  have : P.B - P.A ≠ 0 := sub_ne_zero.2 (Ne.symm hAB)
  have h4 : (-4 : ℤ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero h4 hA) this

theorem m_eq_shift (d : ℤ) : P.m d = (d + P.c) ^ 2 + 4 * P.A * (P.B - P.A) := by
  unfold m c; rw [mVal_eq]

/-- Only finitely many `d` have `m_d` a perfect square. -/
theorem sq_set_finite : {d : ℕ | ∃ s : ℤ, P.m d = s ^ 2}.Finite := by
  have hfin := sq_sub_sq_finite _ P.k_ne_zero
  have : {d : ℕ | ∃ s : ℤ, P.m d = s ^ 2} ⊆
      (fun D : ℤ => (D - P.c).toNat) '' {D : ℤ | ∃ s : ℤ, D ^ 2 - s ^ 2 = -4 * P.A * (P.B - P.A)} := by
    rintro d ⟨s, hs⟩
    refine ⟨(d : ℤ) + P.c, ⟨s, ?_⟩, ?_⟩
    · rw [P.m_eq_shift] at hs; linarith
    · simp
  exact (hfin.image _).subset this

/-- **The bad primes in a dyadic range.** For `y ≥ y₀`, the number of primes `d ∈ (y/2, y]` with
`d ≡ d₀ (mod 2^J)` that are not good is at most a constant `C`. -/
theorem bad_primes_dyadic :
    ∃ C : ℕ, ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      {d : ℕ | y / 2 < d ∧ (d : ℝ) ≤ y ∧ d.Prime ∧ (d : ℤ) ≡ P.d₀ [ZMOD 2 ^ P.J] ∧
        ¬ P.IsGood d}.ncard ≤ C := by
  set S₂ : Set ℕ := {d : ℕ | ∃ s : ℤ, P.m d = s ^ 2} with hS₂
  have hS₂fin : S₂.Finite := P.sq_set_finite
  set k := -4 * P.A * (P.B - P.A) with hk
  refine ⟨S₂.ncard + (32 * k.natAbs + 1), max (2 * P.d₁ + 2) (8 * |P.c| + 8), fun y hy => ?_⟩
  have hy1 : (2 * P.d₁ + 2 : ℝ) ≤ y := le_trans (by exact_mod_cast le_max_left _ _) hy
  have hy2 : (8 * |P.c| + 8 : ℝ) ≤ y := le_trans (by exact_mod_cast le_max_right _ _) hy
  set S₃ : Set ℕ := {d : ℕ | y / 2 < d ∧ (d : ℝ) ≤ y ∧ ∃ s : ℤ, ((d : ℤ) + P.c) ^ 2 - 3 * s ^ 2 = k}
    with hS₃
  set T₃ : Set ℤ := {D : ℤ | 3 * y / 8 < D ∧ (D : ℝ) ≤ 4 * (3 * y / 8) ∧
    ∃ s : ℤ, D ^ 2 - 3 * s ^ 2 = k} with hT₃
  have hcabs : |(P.c : ℝ)| ≤ y / 8 - 1 := by
    have : ((|P.c| : ℤ) : ℝ) = |(P.c : ℝ)| := Int.cast_abs
    push_cast at hy2
    linarith
  have hS₃card : S₃.ncard ≤ T₃.ncard := by
    have hT₃fin : T₃.Finite := by
      apply (Set.finite_Icc (0 : ℤ) ⌈2 * y⌉).subset
      rintro D ⟨h1, h2, -⟩
      have hy0 : (0 : ℝ) ≤ y := by
        have := abs_nonneg (P.c : ℝ); linarith
      constructor
      · have : (0 : ℝ) < D := by linarith
        exact_mod_cast this.le
      · exact_mod_cast (show (D : ℝ) ≤ (⌈2 * y⌉ : ℝ) by linarith [Int.le_ceil (2 * y)])
    apply Set.ncard_le_ncard_of_injOn (fun d : ℕ => (d : ℤ) + P.c) _ _ hT₃fin
    · rintro d ⟨h1, h2, s, hs⟩
      have hc1 := neg_abs_le (P.c : ℝ)
      have hc2 := le_abs_self (P.c : ℝ)
      refine ⟨?_, ?_, s, hs⟩
      · push_cast; linarith
      · push_cast; linarith
    · intro d _ d' _ h
      simp only [add_left_inj, Nat.cast_inj] at h
      exact h
  have hT₃card : T₃.ncard ≤ 32 * k.natAbs + 1 := by
    apply pell_dyadic k (3 * y / 8)
    have := abs_nonneg (P.c : ℝ); linarith
  have hsub : {d : ℕ | y / 2 < d ∧ (d : ℝ) ≤ y ∧ d.Prime ∧ (d : ℤ) ≡ P.d₀ [ZMOD 2 ^ P.J] ∧
      ¬ P.IsGood d} ⊆ S₂ ∪ S₃ := by
    rintro d ⟨hlo, hhi, hdp, hdc, hng⟩
    unfold IsGood at hng
    simp only [hS₂, hS₃, Set.mem_union, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨h2, h3⟩ := hcon
    apply hng
    refine ⟨hdp, hdc, ?_, fun ⟨s, hs⟩ => h2 s hs, ?_⟩
    · have : (P.d₁ : ℝ) < d := by linarith
      exact_mod_cast this
    · rintro ⟨s, hs⟩
      apply h3 hlo hhi s
      rw [P.m_eq_shift] at hs
      linarith
  have hS₃fin : S₃.Finite :=
    (Set.finite_Iic ⌊y⌋₊).subset (fun d hd => Set.mem_Iic.2 (Nat.le_floor hd.2.1))
  calc _ ≤ (S₂ ∪ S₃).ncard := Set.ncard_le_ncard hsub (hS₂fin.union hS₃fin)
    _ ≤ S₂.ncard + S₃.ncard := Set.ncard_union_le _ _
    _ ≤ S₂.ncard + (32 * k.natAbs + 1) := by omega

end PatternData

end Triples
