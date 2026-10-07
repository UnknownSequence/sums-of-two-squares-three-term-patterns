import TriplesFinal.Asymptotic.MainTerm

/-!
# Set-up for the error term (§7.3)

* `X` with `T(X) = x` (`Xpar`), and its basic properties for `x ≥ 33d` (`IsGood.Xpar_spec`):
  `EX² + H = dx/2^(v-2)`, `EH ≤ X²`, `dx/(2^(v-1) E) ≤ X² ≤ dx`;
* `T(t) ≤ x ↔ |t| ≤ X`, and `T(Xs)/x = αs² + (1 - α)` with `0 < α ≤ 1`;
* `k₊ = 2√x/2^((v-2)/2)`: `Φ_k = 0` for `k ≥ k₊`;
* `e(k) = ∑_{dk ∣ Eℓ² + H} Φ_k(ℓ) - ϱ(dk)/(dk) ∫ Φ_k`, so that `ℰ_d = 8 ∑_k χ(k) e(k)`;
* the `ℓ`-sum is a sum over `lattice E H (dk) X`.

Paper: §7.1 and the proof of Lemma 7.3.
-/

namespace Triples

open MeasureTheory

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `X = √((dx/2^(v-2) - H)/E)`, so that `T(X) = x` (§7.1). -/
noncomputable def Xpar (d : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (((d : ℝ) * x / 2 ^ (P.v - 2) - P.H d) / P.E)

/-- `k₊ = 2√x / 2^((v-2)/2)`: for `k ≥ k₊` we have `Φ_k = 0`. -/
noncomputable def kplus (x : ℝ) : ℝ := 2 * Real.sqrt x / (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2)

/-- `e(k) = ∑_{ℓ : dk ∣ Eℓ² + H} Φ_k(ℓ) - ϱ(dk)/(dk) ∫ Φ_k`. -/
noncomputable def ek (F : Cutoff) (W : HyperbolaWeight) (d : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (∑ᶠ (ℓ : ℤ) (_ : ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), P.Phi F W d x k ℓ) -
    (rho (P.m d) (d * k) : ℝ) / (d * k) * ∫ t : ℝ, P.Phi F W d x k t

/-- `E` as a natural number. -/
def Enat : ℕ := P.E.toNat

/-- `H_d` as a natural number. -/
def Hnat (d : ℕ) : ℕ := (P.H d).toNat

theorem E_pos : 0 < P.E := by rcases P.E_eq with h | h <;> rw [h] <;> norm_num

theorem Enat_cast : ((P.Enat : ℕ) : ℤ) = P.E := Int.toNat_of_nonneg P.E_pos.le

theorem Enat_eq : P.Enat = 4 ∨ P.Enat = 8 := by
  rcases P.E_eq with h | h
  · left; unfold Enat; rw [h]; rfl
  · right; unfold Enat; rw [h]; rfl

theorem E_real_eq : (P.E : ℝ) = 4 ∨ (P.E : ℝ) = 8 := by
  rcases P.E_eq with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

theorem E_real_pos : (0 : ℝ) < P.E := by exact_mod_cast P.E_pos

theorem Enat_real : ((P.Enat : ℕ) : ℝ) = P.E := by
  rw [← P.Enat_cast]; norm_cast

variable {P}

theorem IsGood.Hnat_cast {d : ℕ} (hd : P.IsGood d) : ((P.Hnat d : ℕ) : ℤ) = P.H d :=
  Int.toNat_of_nonneg hd.H_pos.le

theorem IsGood.Hnat_real {d : ℕ} (hd : P.IsGood d) : ((P.Hnat d : ℕ) : ℝ) = P.H d := by
  rw [← hd.Hnat_cast]; norm_cast

/-- `d²/2^(v+1) ≤ H_d ≤ 2d²/2^v`. -/
theorem IsGood.H_bounds {d : ℕ} (hd : P.IsGood d) :
    (d : ℝ) ^ 2 / 2 ^ (P.v + 1) ≤ P.H d ∧ (P.H d : ℝ) ≤ 2 * (d : ℝ) ^ 2 / 2 ^ P.v := by
  have hm := P.m_bounds hd.d₁_lt
  have hmeq := hd.m_eq
  have h1 : ((d : ℤ) : ℝ) ^ 2 ≤ 2 * (P.m d : ℝ) := by exact_mod_cast hm.1
  have h2 : (P.m d : ℝ) ≤ 2 * ((d : ℤ) : ℝ) ^ 2 := by exact_mod_cast hm.2
  have h3 : (P.m d : ℝ) = 2 ^ P.v * P.H d := by exact_mod_cast hmeq
  push_cast at h1 h2
  have h2v : (0 : ℝ) < 2 ^ P.v := by positivity
  constructor
  · rw [div_le_iff₀ (by positivity), show (2 : ℝ) ^ (P.v + 1) = 2 ^ P.v * 2 from pow_succ 2 P.v]
    nlinarith
  · rw [le_div_iff₀ h2v]
    nlinarith

theorem two_pow_v_sub_two (P : PatternData a b) : (2 : ℝ) ^ P.v = 4 * 2 ^ (P.v - 2) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; have := P.hv; omega

/-- The basic facts about `X` for `33 d ≤ x`. -/
theorem IsGood.Xpar_spec {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) :
    0 < P.Xpar d x ∧
      (P.E : ℝ) * P.Xpar d x ^ 2 + P.H d = d * x / 2 ^ (P.v - 2) ∧
      (P.E : ℝ) * P.H d ≤ P.Xpar d x ^ 2 ∧
      (d : ℝ) * x / 2 ^ (P.v - 2) / (2 * P.E) ≤ P.Xpar d x ^ 2 ∧
      P.Xpar d x ^ 2 ≤ d * x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hx0 : 0 < x := by linarith
  have hE := P.E_real_eq
  have hE0 := P.E_real_pos
  obtain ⟨hH1, hH2⟩ := hd.H_bounds
  have hHpos : (0 : ℝ) < P.H d := by exact_mod_cast hd.H_pos
  have hc2 : (0 : ℝ) < 2 ^ (P.v - 2) := by positivity
  have hc21 : (1 : ℝ) ≤ 2 ^ (P.v - 2) := one_le_pow₀ (by norm_num)
  have h2v := P.two_pow_v_sub_two
  set c2 : ℝ := 2 ^ (P.v - 2) with hc2def
  set D : ℝ := d * x / c2 with hD
  have hD0 : 0 < D := by positivity
  -- `H ≤ d²/(2 c2)`
  have hH' : (P.H d : ℝ) ≤ (d : ℝ) ^ 2 / (2 * c2) := by
    rw [h2v] at hH2
    calc (P.H d : ℝ) ≤ 2 * (d : ℝ) ^ 2 / (4 * c2) := hH2
      _ = (d : ℝ) ^ 2 / (2 * c2) := by field_simp; ring
  -- `65 H ≤ D`
  have hdd : (d : ℝ) ^ 2 ≤ d * x / 33 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have h65 : 65 * (P.H d : ℝ) ≤ D := by
    have h1 : (P.H d : ℝ) ≤ (d * x / 33) / (2 * c2) :=
      hH'.trans (div_le_div_of_nonneg_right hdd (by positivity))
    have h2 : 65 * ((d * x / 33) / (2 * c2)) = (65 / 66) * D := by
      rw [hD]; field_simp; ring
    nlinarith
  have hDH : 0 < D - P.H d := by linarith
  have hX2 : P.Xpar d x ^ 2 = (D - P.H d) / P.E := by
    unfold Xpar
    rw [Real.sq_sqrt (div_nonneg hDH.le hE0.le)]
  refine ⟨Real.sqrt_pos.2 (div_pos hDH hE0), ?_, ?_, ?_, ?_⟩
  · rw [hX2]; field_simp; ring
  · rw [hX2, le_div_iff₀ hE0]
    rcases hE with h | h <;> rw [h] <;> nlinarith
  · rw [hX2, div_le_div_iff₀ (by positivity) hE0]
    nlinarith
  · rw [hX2, div_le_iff₀ hE0]
    have hDle : D ≤ d * x := by
      rw [hD, div_le_iff₀ hc2]; nlinarith
    rcases hE with h | h <;> rw [h] <;> nlinarith

/-- `T(t) = 2^(v-2)(Et² + H)/d`. -/
theorem Treal_def (d : ℕ) (t : ℝ) :
    P.Treal d t = 2 ^ (P.v - 2) * (P.E * t ^ 2 + P.H d) / d := rfl

/-- `T(t) ≤ x ↔ t² ≤ X²`. -/
theorem IsGood.Treal_le_iff {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x)
    (t : ℝ) : P.Treal d t ≤ x ↔ t ^ 2 ≤ P.Xpar d x ^ 2 := by
  obtain ⟨-, hX, -⟩ := hd.Xpar_spec hx
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hc2 : (0 : ℝ) < 2 ^ (P.v - 2) := by positivity
  have hE0 := P.E_real_pos
  have hxeq : x = 2 ^ (P.v - 2) * (P.E * P.Xpar d x ^ 2 + P.H d) / d := by
    rw [hX]; field_simp
  rw [Treal_def]
  conv_lhs => rw [hxeq]
  rw [div_le_div_iff_of_pos_right hd0, mul_le_mul_iff_right₀ hc2, add_le_add_iff_right,
    mul_le_mul_iff_right₀ hE0]

/-- `T(t) ≤ x → |t| ≤ X`. -/
theorem IsGood.abs_le_Xpar {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) {t : ℝ}
    (ht : P.Treal d t ≤ x) : |t| ≤ P.Xpar d x := by
  have h := (hd.Treal_le_iff hx t).1 ht
  have hX := (hd.Xpar_spec hx).1
  exact abs_le_of_sq_le_sq' h hX.le |> fun h => abs_le.2 h

/-- `T(Xs)/x = α s² + (1 - α)` with `α = 2^(v-2) E X²/(dx) ∈ (0, 1)`. -/
theorem IsGood.Treal_Xpar_mul {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x)
    (s : ℝ) :
    P.Treal d (P.Xpar d x * s) / x =
      (2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x)) * s ^ 2 +
        (1 - 2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x)) := by
  obtain ⟨-, hX, -⟩ := hd.Xpar_spec hx
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hc2 : (0 : ℝ) < 2 ^ (P.v - 2) := by positivity
  have hH : (P.H d : ℝ) = d * x / 2 ^ (P.v - 2) - P.E * P.Xpar d x ^ 2 := by linarith
  rw [Treal_def, hH]
  field_simp

theorem IsGood.alpha_mem {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) :
    0 < 2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x) ∧
      2 ^ (P.v - 2) * P.E * P.Xpar d x ^ 2 / (d * x) ≤ 1 := by
  obtain ⟨hX0, hX, -⟩ := hd.Xpar_spec hx
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.prime.pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hc2 : (0 : ℝ) < 2 ^ (P.v - 2) := by positivity
  have hE0 := P.E_real_pos
  have hH : (0 : ℝ) < P.H d := by exact_mod_cast hd.H_pos
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have : (P.E : ℝ) * P.Xpar d x ^ 2 ≤ d * x / 2 ^ (P.v - 2) := by linarith
    rw [le_div_iff₀ hc2] at this
    linarith

/-- `2^((v-2)/2) ≥ 1`. -/
theorem one_le_two_rpow_v (P : PatternData a b) : (1 : ℝ) ≤ (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2) := by
  apply Real.one_le_rpow (by norm_num)
  have : (2 : ℝ) ≤ P.v := by exact_mod_cast P.hv
  linarith

theorem kplus_le (P : PatternData a b) (x : ℝ) : P.kplus x ≤ 2 * Real.sqrt x := by
  unfold kplus
  have h1 := P.one_le_two_rpow_v
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.sqrt_nonneg x]

/-- `Φ_k = 0` for `k ≥ k₊`. -/
theorem IsGood.Phi_eq_zero_of_kplus_le {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 0 < x) {k : ℝ} (hk : P.kplus x ≤ k) (t : ℝ) :
    P.Phi F W d x k t = 0 := by
  unfold Phi
  by_cases hF : F.F (P.Treal d t / x) = 0
  · rw [hF, zero_mul]
  · obtain ⟨-, hTx⟩ := Treal_mem_of_F_ne_zero F hx hF
    have hT0 := hd.Treal_pos t
    rw [W.eq_zero, mul_zero]
    have hc := P.one_le_two_rpow_v
    set c := (2 : ℝ) ^ (((P.v : ℝ) - 2) / 2)
    have hsq : Real.sqrt (P.Treal d t) ≤ Real.sqrt x := Real.sqrt_le_sqrt hTx
    have hsq0 : 0 < Real.sqrt (P.Treal d t) := Real.sqrt_pos.2 hT0
    have hk' : 2 * Real.sqrt x ≤ c * k := by
      unfold kplus at hk
      rw [div_le_iff₀ (by linarith)] at hk
      linarith
    rw [le_div_iff₀ hsq0]
    nlinarith

theorem IsGood.ek_eq_zero_of_kplus_le {d : ℕ} (hd : P.IsGood d) (F : Cutoff)
    (W : HyperbolaWeight) {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : P.kplus x ≤ k) :
    P.ek F W d x k = 0 := by
  unfold ek
  have h0 : ∀ t, P.Phi F W d x k t = 0 := fun t => hd.Phi_eq_zero_of_kplus_le F W hx hk t
  simp [h0]

/-- `ℰ_d = 8 ∑_{k} χ(k) e(k)`. -/
theorem IsGood.Ed_eq_sum_ek {d : ℕ} (hd : P.IsGood d) (F : Cutoff) (W : HyperbolaWeight)
    {x : ℝ} (hx : 1 ≤ x) :
    P.Ed F W d x = 8 * ∑ k ∈ kRange x, (ZMod.χ₄ (k : ZMod 4) : ℝ) * P.ek F W d x k := by
  rw [Ed, hd.Sigma_expand F W hx, Md, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold ek
  push_cast
  ring

/-- The `ℓ`-sum of `e(k)` is a sum over `lattice E H (dk) X`. -/
theorem IsGood.finsum_eq_lattice {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x)
    (k : ℕ) (g : ℤ → ℝ)
    (hg : ∀ ℓ : ℤ, g ℓ ≠ 0 → P.Treal d ℓ ≤ x) :
    (∑ᶠ (ℓ : ℤ) (_ : ((d * k : ℕ) : ℤ) ∣ P.E * ℓ ^ 2 + P.H d), g ℓ) =
      ∑ ℓ ∈ lattice P.Enat (P.Hnat d) (d * k) (P.Xpar d x), g ℓ := by
  classical
  simp only [finsum_eq_if]
  rw [lattice, Finset.sum_filter, P.Enat_cast, hd.Hnat_cast]
  apply finsum_eq_sum_of_support_subset
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  split_ifs at hℓ with h
  · have hT := hg ℓ hℓ
    have habs := hd.abs_le_Xpar hx hT
    rw [Finset.coe_Icc, Set.mem_Icc]
    have h1 : (ℓ : ℝ) ≤ P.Xpar d x := (le_abs_self _).trans habs
    have h2 : -(P.Xpar d x) ≤ (ℓ : ℝ) := by
      have := neg_abs_le (ℓ : ℝ); linarith
    constructor
    · have : -(ℓ : ℝ) ≤ P.Xpar d x := by linarith
      have h3 : -ℓ ≤ ⌊P.Xpar d x⌋ := Int.le_floor.2 (by push_cast; exact this)
      omega
    · exact Int.le_floor.2 h1
  · exact absurd rfl hℓ

end PatternData

end Triples
