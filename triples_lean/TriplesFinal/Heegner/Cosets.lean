import TriplesFinal.Heegner.Qkappa
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Lemma 8.3: the number of cosets

Let `𝒬 ⊆ {𝔤 ∈ Q_N : d ∣ 𝔠}`. Then for every `𝔤 ∈ Q_N`,
`#{τ ∈ 𝒯_q : τ ⋄ 𝔤 ∈ 𝒬} ≤ 12E ≤ 96`.

The proof maps `τ` to the point `(τ₃ : τ₄) ∈ ℙ¹(ℤ/qℤ)` given by its bottom row (an injection),
uses `ℙ¹(ℤ/qℤ) = ℙ¹(ℤ/4Eℤ) × ℙ¹(𝔽_d)`, `#ℙ¹(ℤ/2^r ℤ) = 3 · 2^(r-1)`, and the fact that the form
`φ_𝔤` is not identically zero modulo `d` (since `d² ∤ N`), so it has at most two zeros in
`ℙ¹(𝔽_d)`.

In the formalization the point `(τ₃ : τ₄)` is recorded by its normal forms in `ℙ¹(ℤ/4Eℤ)`
(`p1Two`, at most `6E` values) and in `ℙ¹(𝔽_d)` (`p1Prime`, at most two values on the zeros of
`φ_𝔤`), and two coset representatives with the same normal forms coincide (`eq_of_dvd_cross`).

Paper: §8.3, Lemma 8.3.
-/

namespace Triples

open scoped MatrixGroups
open CongruenceSubgroup

namespace SymMat

/-- Two coset representatives whose bottom rows are proportional modulo `q` coincide. -/
theorem eq_of_dvd_cross {q : ℕ} {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {τ τ' : SL(2, ℤ)}
    (hτ : τ ∈ T) (hτ' : τ' ∈ T) (h : (q : ℤ) ∣ τ' 1 0 * τ 1 1 - τ' 1 1 * τ 1 0) : τ = τ' := by
  have hδ : τ' * τ⁻¹ ∈ Gamma0 q := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : ((τ' * τ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        τ' 1 0 * τ 1 1 - τ' 1 1 * τ 1 0 := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring
    rw [this]; exact h
  obtain ⟨τ₀, -, huniq⟩ := hT τ'
  have e1 := huniq τ' ⟨hτ', 1, one_mem _, (one_mul _).symm⟩
  have e2 := huniq τ ⟨hτ, τ' * τ⁻¹, hδ, (inv_mul_cancel_right τ' τ).symm⟩
  rw [e1, e2]

/-- At most two roots of a quadratic polynomial over a field. -/
theorem card_le_two_of_quadratic {F : Type*} [Field F] {a b c : F} (ha : a ≠ 0) (S : Finset F)
    (hS : ∀ x ∈ S, a * x ^ 2 + b * x + c = 0) : S.card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 h
  have e1 : (x - y) * (a * (x + y) + b) = 0 := by linear_combination hS x hx - hS y hy
  have e2 : (x - z) * (a * (x + z) + b) = 0 := by linear_combination hS x hx - hS z hz
  have f1 := (mul_eq_zero.1 e1).resolve_left (sub_ne_zero.2 hxy)
  have f2 := (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hxz)
  have : a * (y - z) = 0 := by linear_combination f1 - f2
  exact hyz (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ha))

/-- At most one root of a non-zero polynomial of degree at most `1` over a field. -/
theorem card_le_one_of_linear {F : Type*} [Field F] {b c : F} (hbc : b ≠ 0 ∨ c ≠ 0)
    (S : Finset F) (hS : ∀ x ∈ S, b * x + c = 0) : S.card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
  have e : b * (x - y) = 0 := by linear_combination hS x hx - hS y hy
  have hb : b = 0 := (mul_eq_zero.1 e).resolve_right (sub_ne_zero.2 hxy)
  have hc : c = 0 := by have := hS x hx; rw [hb] at this; simpa using this
  rcases hbc with h | h <;> contradiction

/-- `M ∣ 1 - t A` for the Bézout coefficient `A` of `t` and `M` when `gcd(t, M) = 1`. -/
theorem dvd_one_sub_mul_gcdA {t M : ℤ} (h : Int.gcd t M = 1) : M ∣ 1 - t * Int.gcdA t M := by
  have := Int.gcd_eq_gcd_ab t M
  rw [h] at this
  exact ⟨Int.gcdB t M, by push_cast at this; linarith⟩

/-- Normal form of the point `(s : t)` of `ℙ¹(ℤ/Mℤ)` (`M` a power of `2`, `s` or `t` odd):
`(0, s/t)` if `t` is odd and `(1, t/s)` otherwise. -/
def p1Two (M s t : ℤ) : ℕ × ℤ :=
  if t % 2 = 1 then (0, s * Int.gcdA t M % M) else (1, t * Int.gcdA s M % M)

/-- Normal form of the point `(s : t)` of `ℙ¹(𝔽_d)`: `none` if `d ∣ t`, else `s/t`. -/
def p1Prime (d s t : ℤ) : Option ℤ :=
  if d ∣ t then none else some (s * Int.gcdA t d % d)

theorem gcd_two_pow_of_odd {t : ℤ} (ht : t % 2 = 1) (r : ℕ) : Int.gcd t (2 ^ r) = 1 := by
  have h1 : Odd t.natAbs := Int.natAbs_odd.2 (Int.odd_iff.2 ht)
  have h2 : Nat.Coprime t.natAbs 2 := Nat.coprime_two_right.2 h1
  have h3 := Nat.Coprime.pow_right r h2
  show Nat.gcd t.natAbs ((2 : ℤ) ^ r).natAbs = 1
  simpa [Int.natAbs_pow] using h3

/-- Equal normal forms in `ℙ¹(ℤ/2^rℤ)` give proportional rows. -/
theorem p1Two_cross {r : ℕ} {s t s' t' : ℤ} (hst : s % 2 = 1 ∨ t % 2 = 1)
    (hst' : s' % 2 = 1 ∨ t' % 2 = 1) (heq : p1Two (2 ^ r) s t = p1Two (2 ^ r) s' t') :
    (2 : ℤ) ^ r ∣ s * t' - s' * t := by
  unfold p1Two at heq
  split_ifs at heq with h1 h2 h2
  · simp only [Prod.mk.injEq, true_and] at heq
    obtain ⟨k1, hk1⟩ := (Int.ModEq.dvd heq)
    obtain ⟨k2, hk2⟩ := dvd_one_sub_mul_gcdA (gcd_two_pow_of_odd h1 r)
    obtain ⟨k3, hk3⟩ := dvd_one_sub_mul_gcdA (gcd_two_pow_of_odd h2 r)
    refine ⟨-(t * t') * k1 + s * t' * k2 - s' * t * k3, ?_⟩
    linear_combination (-(t * t')) * hk1 + s * t' * hk2 - s' * t * hk3
  · simp at heq
  · simp at heq
  · simp only [Prod.mk.injEq, true_and] at heq
    have hs : s % 2 = 1 := hst.resolve_right h1
    have hs' : s' % 2 = 1 := hst'.resolve_right h2
    obtain ⟨k1, hk1⟩ := (Int.ModEq.dvd heq)
    obtain ⟨k2, hk2⟩ := dvd_one_sub_mul_gcdA (gcd_two_pow_of_odd hs r)
    obtain ⟨k3, hk3⟩ := dvd_one_sub_mul_gcdA (gcd_two_pow_of_odd hs' r)
    refine ⟨s * s' * k1 + s * t' * k3 - s' * t * k2, ?_⟩
    linear_combination s * s' * hk1 + s * t' * hk3 - s' * t * hk2

/-- The normal forms of `ℙ¹(ℤ/Mℤ)`. -/
def p1TwoSet (M : ℤ) : Finset (ℕ × ℤ) :=
  ({0} ×ˢ Finset.Ico 0 M) ∪ ({1} ×ˢ (Finset.Ico 0 (M / 2)).image (2 * ·))

theorem p1Two_mem {r : ℕ} (hr : 1 ≤ r) {s t : ℤ} :
    p1Two (2 ^ r) s t ∈ p1TwoSet (2 ^ r) := by
  have hM : (0 : ℤ) < 2 ^ r := by positivity
  have hM2 : (2 : ℤ) ∣ 2 ^ r := dvd_pow_self 2 (by omega)
  unfold p1Two p1TwoSet
  split_ifs with h
  · apply Finset.mem_union_left
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico, true_and]
    exact ⟨Int.emod_nonneg _ hM.ne', Int.emod_lt_of_pos _ hM⟩
  · apply Finset.mem_union_right
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_image, Finset.mem_Ico,
      true_and]
    set x := t * Int.gcdA s (2 ^ r) % 2 ^ r with hx
    have h0 : 0 ≤ x := Int.emod_nonneg _ hM.ne'
    have h1 : x < 2 ^ r := Int.emod_lt_of_pos _ hM
    have h2 : x % 2 = 0 := by
      rw [hx, Int.emod_emod_of_dvd _ hM2]
      have : t % 2 = 0 := by omega
      rw [Int.mul_emod, this, zero_mul, Int.zero_emod]
    obtain ⟨k, hk⟩ := hM2
    rw [hk] at h1 ⊢
    refine ⟨x / 2, ⟨by omega, ?_⟩, by omega⟩
    rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    omega

theorem card_p1TwoSet {r : ℕ} (hr : 1 ≤ r) :
    ((p1TwoSet (2 ^ r)).card : ℤ) = 2 ^ r + 2 ^ (r - 1) := by
  unfold p1TwoSet
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_product, Finset.card_product, Finset.card_image_of_injective _
      (fun x y h => by simpa using h)]
    simp only [Finset.card_singleton, one_mul, Int.card_Ico, sub_zero]
    have h1 : (2 : ℤ) ^ r / 2 = 2 ^ (r - 1) := by
      rw [show r = (r - 1) + 1 by omega, pow_succ, Int.mul_ediv_cancel _ two_ne_zero]
      simp
    rw [h1]
    push_cast
    rw [Int.toNat_of_nonneg (by positivity), Int.toNat_of_nonneg (by positivity)]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_product, Finset.mem_singleton] at hx1 hx2
    omega

theorem gcd_eq_one_of_not_dvd {d t : ℤ} (hd : Prime d) (ht : ¬ d ∣ t) : Int.gcd t d = 1 :=
  Int.isCoprime_iff_gcd_eq_one.1 ((Prime.coprime_iff_not_dvd hd).2 ht).symm

/-- Equal normal forms in `ℙ¹(𝔽_d)` give proportional rows. -/
theorem p1Prime_cross {d s t s' t' : ℤ} (hd : Prime d)
    (heq : p1Prime d s t = p1Prime d s' t') : d ∣ s * t' - s' * t := by
  unfold p1Prime at heq
  by_cases h1 : d ∣ t <;> by_cases h2 : d ∣ t' <;> simp only [h1, h2, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq] at heq
  · exact dvd_sub (dvd_mul_of_dvd_right h2 s) (dvd_mul_of_dvd_right h1 s')
  · obtain ⟨k1, hk1⟩ := (Int.ModEq.dvd heq)
    obtain ⟨k2, hk2⟩ := dvd_one_sub_mul_gcdA (gcd_eq_one_of_not_dvd hd h1)
    obtain ⟨k3, hk3⟩ := dvd_one_sub_mul_gcdA (gcd_eq_one_of_not_dvd hd h2)
    refine ⟨-(t * t') * k1 + s * t' * k2 - s' * t * k3, ?_⟩
    linear_combination (-(t * t')) * hk1 + s * t' * hk2 - s' * t * hk3

/-- The normal forms of the zeros of `φ(s, t) = a s² + 2b s t + c t²` in `ℙ¹(𝔽_d)`. -/
def p1Zeros (d a b c : ℤ) : Finset (Option ℤ) :=
  (if d ∣ a then {none} else ∅) ∪
    ((Finset.Ico 0 d).filter (fun x => d ∣ a * x ^ 2 + 2 * b * x + c)).image some

/-- `s/t` is a root of `a x² + 2b x + c` modulo `d` when `d ∣ φ(s, t)` and `d ∤ t`. -/
theorem root_of_dvd_form {d a b c s t : ℤ} (hd : Prime d) (ht : ¬ d ∣ t)
    (hφ : d ∣ a * s ^ 2 + 2 * b * s * t + c * t ^ 2) :
    d ∣ a * (s * Int.gcdA t d % d) ^ 2 + 2 * b * (s * Int.gcdA t d % d) + c := by
  set A := Int.gcdA t d
  set x := s * A % d with hx
  obtain ⟨k1, hk1⟩ := dvd_one_sub_mul_gcdA (gcd_eq_one_of_not_dvd hd ht)
  have hx' : x = s * A - d * (s * A / d) := Int.emod_def _ _
  have htx : d ∣ t * x - s := by
    refine ⟨-(t * (s * A / d)) - s * k1, ?_⟩
    rw [hx']
    linear_combination (-s) * hk1
  have hmain : d ∣ t ^ 2 * (a * x ^ 2 + 2 * b * x + c) := by
    have e : t ^ 2 * (a * x ^ 2 + 2 * b * x + c) =
        (t * x - s) * (a * (t * x + s) + 2 * b * t) + (a * s ^ 2 + 2 * b * s * t + c * t ^ 2) := by
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left htx _) hφ
  rcases hd.dvd_or_dvd hmain with h | h
  · exact absurd (hd.dvd_of_dvd_pow h) ht
  · exact h

theorem p1Prime_mem {d a b c s t : ℤ} (hd : Prime d) (hd0 : 0 < d) (hst : ¬ (d ∣ s ∧ d ∣ t))
    (hφ : d ∣ a * s ^ 2 + 2 * b * s * t + c * t ^ 2) : p1Prime d s t ∈ p1Zeros d a b c := by
  unfold p1Prime p1Zeros
  by_cases ht : d ∣ t
  · rw [ite_eq_left ht]
    have hs : ¬ d ∣ s := fun h => hst ⟨h, ht⟩
    have ha : d ∣ a := by
      have h1 : d ∣ a * s ^ 2 := by
        obtain ⟨k, hk⟩ := ht
        have h2 : d ∣ 2 * b * s * t + c * t ^ 2 :=
          ⟨2 * b * s * k + c * k * t, by rw [hk]; ring⟩
        have := dvd_sub hφ h2
        simpa using this
      rcases hd.dvd_or_dvd h1 with h | h
      · exact h
      · exact absurd (hd.dvd_of_dvd_pow h) hs
    rw [ite_eq_left ha]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  · rw [ite_eq_right ht]
    apply Finset.mem_union_right
    apply Finset.mem_image_of_mem
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Int.emod_nonneg _ hd0.ne', Int.emod_lt_of_pos _ hd0⟩, root_of_dvd_form hd ht hφ⟩

/-- A non-degenerate binary quadratic form has at most two zeros in `ℙ¹(𝔽_d)`. -/
theorem card_p1Zeros {d a b c : ℤ} (hd : Prime d) (hd0 : 0 < d) (hd2 : d ≠ 2)
    (hN : ¬ d ∣ a * c - b ^ 2) : (p1Zeros d a b c).card ≤ 2 := by
  classical
  obtain ⟨p, hpd⟩ : ∃ p : ℕ, (p : ℤ) = d := ⟨d.natAbs, Int.natAbs_of_nonneg hd0.le⟩
  have hpp : p.Prime := by
    have := Int.prime_iff_natAbs_prime.1 hd
    rwa [← hpd, Int.natAbs_natCast] at this
  have : Fact p.Prime := ⟨hpp⟩
  set R := (Finset.Ico 0 d).filter (fun x => d ∣ a * x ^ 2 + 2 * b * x + c) with hR
  -- reduction modulo `d` is injective on `[0, d)`
  have hinj : Set.InjOn (fun x : ℤ => (x : ZMod p)) R := by
    intro x hx y hy hxy
    simp only [hR, Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hx hy
    have := (ZMod.intCast_eq_intCast_iff' x y p).1 hxy
    rw [hpd, Int.emod_eq_of_lt hx.1.1 hx.1.2, Int.emod_eq_of_lt hy.1.1 hy.1.2] at this
    exact this
  have hcardR : R.card = (R.image (fun x : ℤ => (x : ZMod p))).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hroots : ∀ y ∈ R.image (fun x : ℤ => (x : ZMod p)),
      (a : ZMod p) * y ^ 2 + (2 * b : ℤ) * y + c = 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have h := (Finset.mem_filter.1 hx).2
    rw [← hpd] at h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    push_cast at this ⊢
    linear_combination this
  have hunion := Finset.card_union_le (if d ∣ a then ({none} : Finset (Option ℤ)) else ∅)
    (R.image some)
  have himg : (R.image some).card = R.card := Finset.card_image_of_injective _ (Option.some_injective _)
  unfold p1Zeros
  rw [← hR]
  by_cases ha : d ∣ a
  · rw [ite_eq_left ha] at hunion ⊢
    rw [Finset.card_singleton, himg] at hunion
    have h0 : (a : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (hpd ▸ ha)
    have hbc : ((2 * b : ℤ) : ZMod p) ≠ 0 ∨ (c : ZMod p) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h2b : d ∣ 2 * b := hpd ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hcon.1
      have hc : d ∣ c := hpd ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hcon.2
      have hb : d ∣ b := by
        rcases hd.dvd_or_dvd h2b with h | h
        · exfalso
          have hle := Int.le_of_dvd (by norm_num) h
          have : d = 1 ∨ d = 2 := by omega
          rcases this with h1 | h1
          · exact hd.not_isUnit (h1 ▸ isUnit_one)
          · exact hd2 h1
        · exact h
      apply hN
      exact dvd_sub (dvd_mul_of_dvd_left ha c) (dvd_pow hb two_ne_zero)
    have hlin := card_le_one_of_linear hbc (R.image (fun x : ℤ => (x : ZMod p)))
      (fun y hy => by have := hroots y hy; rw [h0] at this; simpa using this)
    omega
  · rw [ite_eq_right ha] at hunion ⊢
    rw [Finset.card_empty, himg] at hunion
    have h0 : (a : ZMod p) ≠ 0 := fun h => ha (hpd ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h)
    have hq := card_le_two_of_quadratic h0 (R.image (fun x : ℤ => (x : ZMod p))) hroots
    omega

/-- The determinant of `τ ∈ SL₂(ℤ)` in coordinates. -/
theorem det_SL2 (τ : SL(2, ℤ)) : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
  have := τ.2
  rw [Matrix.det_fin_two] at this
  exact this

/-- No prime divides both entries of the bottom row of `τ ∈ SL₂(ℤ)`. -/
theorem not_dvd_bottom_row {p : ℤ} (hp : ¬ IsUnit p) (τ : SL(2, ℤ)) :
    ¬ (p ∣ τ 1 0 ∧ p ∣ τ 1 1) := by
  rintro ⟨h1, h2⟩
  apply hp
  have h : p ∣ τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 :=
    dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  rw [det_SL2] at h
  exact isUnit_of_dvd_one h

/-- Lemma 8.3 together with the finiteness of the set of cosets. -/
theorem coset_count_aux {E H d : ℤ} (hE : E = 4 ∨ E = 8) (hd : Prime d) (hd0 : 0 < d)
    (hd2 : d ≠ 2) (hdH : ¬ d ∣ H) {q : ℕ} (hq : (q : ℤ) = 4 * E * d) {T : Set SL(2, ℤ)}
    (hT : IsCosetReps q T) {Q : Set SymMat} (hQ : Q ⊆ {g | g ∈ QN (E * H) ∧ d ∣ g.c})
    {g : SymMat} (hg : g ∈ QN (E * H)) :
    {τ | τ ∈ T ∧ act τ g ∈ Q}.Finite ∧ ({τ | τ ∈ T ∧ act τ g ∈ Q}.ncard : ℤ) ≤ 12 * E := by
  classical
  -- `4E = 2^r`
  obtain ⟨r, hr1, hr, hr'⟩ : ∃ r : ℕ, 1 ≤ r ∧ (2 : ℤ) ^ r = 4 * E ∧ (2 : ℤ) ^ (r - 1) = 2 * E := by
    rcases hE with rfl | rfl
    · exact ⟨4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  -- `d ∤ N`
  have hdE : ¬ d ∣ E := by
    intro h
    have h' : d ∣ 2 ^ r := by rw [hr]; exact dvd_mul_of_dvd_right h 4
    have h2 : d ∣ 2 := hd.dvd_of_dvd_pow h'
    have hle := Int.le_of_dvd (by norm_num) h2
    have : d = 1 ∨ d = 2 := by omega
    rcases this with h1 | h1
    · exact hd.not_isUnit (h1 ▸ isUnit_one)
    · exact hd2 h1
  have hN : ¬ d ∣ g.a * g.c - g.b ^ 2 := by
    have : g.a * g.c - g.b ^ 2 = E * H := hg.2.2
    rw [this]
    intro h
    rcases hd.dvd_or_dvd h with h | h
    · exact hdE h
    · exact hdH h
  -- the map to normal forms
  set F : SL(2, ℤ) → (ℕ × ℤ) × Option ℤ :=
    fun τ => (p1Two (2 ^ r) (τ 1 0) (τ 1 1), p1Prime d (τ 1 0) (τ 1 1)) with hF
  set S := p1TwoSet (2 ^ r) ×ˢ p1Zeros d g.a g.b g.c with hS
  have h2unit : ¬ IsUnit (2 : ℤ) := by decide
  have hodd : ∀ τ : SL(2, ℤ), τ 1 0 % 2 = 1 ∨ τ 1 1 % 2 = 1 := by
    intro τ
    by_contra h
    push Not at h
    exact not_dvd_bottom_row h2unit τ
      ⟨Int.dvd_of_emod_eq_zero (by omega), Int.dvd_of_emod_eq_zero (by omega)⟩
  have hmaps : ∀ τ ∈ {τ | τ ∈ T ∧ act τ g ∈ Q}, F τ ∈ (S : Set ((ℕ × ℤ) × Option ℤ)) := by
    rintro τ ⟨-, hτQ⟩
    have hc : d ∣ (act τ g).c := (hQ hτQ).2
    rw [act_c] at hc
    simp only [hF, hS, Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    refine ⟨p1Two_mem hr1, p1Prime_mem hd hd0 (not_dvd_bottom_row hd.not_isUnit τ) ?_⟩
    simpa [form] using hc
  have hinj : Set.InjOn F {τ | τ ∈ T ∧ act τ g ∈ Q} := by
    rintro τ ⟨hτ, -⟩ τ' ⟨hτ', -⟩ heq
    simp only [hF, Prod.mk.injEq] at heq
    have h2 := p1Two_cross (hodd τ) (hodd τ') heq.1
    have hd' := p1Prime_cross hd heq.2
    have hnd2 : ¬ d ∣ 2 := fun h => by
      have hle := Int.le_of_dvd (by norm_num) h
      have : d = 1 ∨ d = 2 := by omega
      rcases this with h1 | h1
      · exact hd.not_isUnit (h1 ▸ isUnit_one)
      · exact hd2 h1
    have hcop : IsCoprime ((2 : ℤ) ^ r) d :=
      ((Prime.coprime_iff_not_dvd hd).2 hnd2).symm.pow_left
    have hqd : (q : ℤ) ∣ τ 1 0 * τ' 1 1 - τ' 1 0 * τ 1 1 := by
      rw [hq, ← hr]
      exact hcop.mul_dvd h2 hd'
    apply eq_of_dvd_cross hT hτ hτ'
    have : τ' 1 0 * τ 1 1 - τ' 1 1 * τ 1 0 = -(τ 1 0 * τ' 1 1 - τ' 1 0 * τ 1 1) := by ring
    rw [this]
    exact dvd_neg.2 hqd
  refine ⟨Set.Finite.of_injOn hmaps hinj S.finite_toSet, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn F hmaps hinj (S.finite_toSet)
  rw [Set.ncard_coe_finset, hS, Finset.card_product] at hle
  have h1 := card_p1TwoSet hr1
  have h2 := card_p1Zeros hd hd0 hd2 hN
  have hle' : ({τ | τ ∈ T ∧ act τ g ∈ Q}.ncard : ℤ) ≤
      ((p1TwoSet (2 ^ r)).card : ℤ) * ((p1Zeros d g.a g.b g.c).card : ℤ) := by
    exact_mod_cast hle
  rw [h1, hr, hr'] at hle'
  have h2' : ((p1Zeros d g.a g.b g.c).card : ℤ) ≤ 2 := by exact_mod_cast h2
  have hE0 : 0 ≤ 4 * E + 2 * E := by rcases hE with rfl | rfl <;> norm_num
  nlinarith

/-- **Lemma 8.3.** -/
theorem coset_count {E H d : ℤ} (hE : E = 4 ∨ E = 8) (_hH : 0 < H) (hd : Prime d) (hd0 : 0 < d)
    (hd2 : d ≠ 2) (hdH : ¬ d ∣ H) {q : ℕ} (hq : (q : ℤ) = 4 * E * d) {T : Set SL(2, ℤ)}
    (hT : IsCosetReps q T) {Q : Set SymMat} (hQ : Q ⊆ {g | g ∈ QN (E * H) ∧ d ∣ g.c})
    {g : SymMat} (hg : g ∈ QN (E * H)) :
    ({τ | τ ∈ T ∧ act τ g ∈ Q}.ncard : ℤ) ≤ 12 * E :=
  (coset_count_aux hE hd hd0 hd2 hdH hq hT hQ hg).2

/-- The set of cosets in Lemma 8.3 is finite. -/
theorem coset_finite {E H d : ℤ} (hE : E = 4 ∨ E = 8) (hd : Prime d) (hd0 : 0 < d)
    (hd2 : d ≠ 2) (hdH : ¬ d ∣ H) {q : ℕ} (hq : (q : ℤ) = 4 * E * d) {T : Set SL(2, ℤ)}
    (hT : IsCosetReps q T) {Q : Set SymMat} (hQ : Q ⊆ {g | g ∈ QN (E * H) ∧ d ∣ g.c})
    {g : SymMat} (hg : g ∈ QN (E * H)) : {τ | τ ∈ T ∧ act τ g ∈ Q}.Finite :=
  (coset_count_aux hE hd hd0 hd2 hdH hq hT hQ hg).1

end SymMat

end Triples
