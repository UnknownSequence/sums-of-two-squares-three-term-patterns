import TriplesFinal.TwoAdic.Defs

/-!
# Lemma 3.1: the auxiliary element `n_*`

For an admissible pair `(B, A)` there is `n_* ∈ ℤ` such that
(i) `Q_* = 2n_* + B ≡ 1 (mod 4)`;
(ii) `n_*(n_* + B)` is a non-zero square in `ℚ₂` (we record `n_*(n_*+B) = 4^s w`, `s ≥ 1`,
     `w ≡ 1 (mod 8)`);
(iii) `T_* = n_* + A ∈ 𝒩`.
Paper: §3, Lemma 3.1. The proof follows the paper: `n = 4^s o` (if `B ≡ 1 (mod 4)`) or
`n = 4^s o - B` (if `B ≡ 3 (mod 4)`), with explicit choices of `s` and of the odd number `o`.
-/

namespace Triples

/-- The residue class `c_s` of the paper: `5β` for `s = 1` and `β` for `s ≥ 2`. -/
def cS (β : ℤ) (s : ℕ) : ℤ := if s = 1 then 5 * β else β

theorem cS_emod_four {β : ℤ} (hβ : β % 4 = 1) (s : ℕ) : cS β s % 4 = 1 := by
  unfold cS; split_ifs <;> omega

/-- If `o ≡ c_s (mod 8)` (with `β` odd and `s ≥ 1`) then `o(4^s o + β) ≡ 1 (mod 8)`. -/
theorem w_emod_eight {β o : ℤ} {s : ℕ} (hβ : β % 2 = 1) (hs : 1 ≤ s)
    (ho : o % 8 = cS β s % 8) : (o * (4 ^ s * o + β)) % 8 = 1 := by
  have hβ2 := sq_emod_eight_of_odd hβ
  unfold cS at ho
  split_ifs at ho with h1
  · subst h1
    obtain ⟨k, rfl⟩ : ∃ k, o = 5 * β + 8 * k := ⟨(o - 5 * β) / 8, by omega⟩
    have h : (5 * β + 8 * k) * (4 ^ 1 * (5 * β + 8 * k) + β) =
        105 * β ^ 2 + 8 * (41 * k * β + 32 * k ^ 2) := by ring
    rw [h]
    generalize β ^ 2 = S at hβ2 ⊢
    generalize 41 * k * β + 32 * k ^ 2 = X
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, o = β + 8 * k := ⟨(o - β) / 8, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 2 := ⟨s - 2, by omega⟩
    have h : (β + 8 * k) * (4 ^ (r + 2) * (β + 8 * k) + β) =
        β ^ 2 + 8 * (2 * 4 ^ r * (β + 8 * k) ^ 2 + k * β) := by ring
    rw [h]
    generalize β ^ 2 = S at hβ2 ⊢
    generalize 2 * 4 ^ r * (β + 8 * k) ^ 2 + k * β = X
    omega

theorem four_pow_eq_two_pow (s : ℕ) : (4 : ℤ) ^ s = 2 ^ (2 * s) := by
  rw [pow_mul]; norm_num

/-- The core of the construction: given `β ≡ 1 (mod 4)` and `C ≠ 0` with `C ≡ 1 (mod 4)` whenever
`C` is odd, there are `s ≥ 1` and an odd `o` with `o(4^s o + β) ≡ 1 (mod 8)` and
`4^s o + C ∈ 𝒩`. -/
theorem nstar_core {β C : ℤ} (hβ : β % 4 = 1) (hC : C ≠ 0) (hCodd : C % 2 = 1 → C % 4 = 1) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ o : ℤ, o % 2 = 1 ∧ (o * (4 ^ s * o + β)) % 8 = 1 ∧
      InN (4 ^ s * o + C) := by
  have hβ2 : β % 2 = 1 := by omega
  by_cases hCo : C % 2 = 1
  · -- `C` odd: `s = 2`, `o = β`
    have hC4 := hCodd hCo
    refine ⟨2, by norm_num, β, hβ2, w_emod_eight hβ2 (by norm_num) (by simp [cS]),
      0, 4 ^ 2 * β + C, by ring, ?_⟩
    have : (4 : ℤ) ^ 2 * β + C = 4 * (4 * β) + C := by ring
    rw [this]; omega
  · obtain ⟨t, w₀, hCt, hw₀⟩ := exists_two_pow_mul_odd hC
    have ht : 1 ≤ t := by
      by_contra h0
      have : t = 0 := by omega
      subst this
      simp at hCt
      omega
    by_cases hw1 : w₀ % 4 = 1
    · -- `w₀ ≡ 1 (mod 4)`: `s = max(2, ⌈(t+2)/2⌉)`, `o = β`
      refine ⟨max 2 ((t + 3) / 2), by omega, β, hβ2,
        w_emod_eight hβ2 (by omega) (by simp only [cS]; split_ifs <;> omega),
        t, 2 ^ (2 * max 2 ((t + 3) / 2) - t) * β + w₀, ?_, ?_⟩
      · rw [hCt, four_pow_eq_two_pow]
        have h2 : (2 : ℤ) ^ (2 * max 2 ((t + 3) / 2)) =
            2 ^ t * 2 ^ (2 * max 2 ((t + 3) / 2) - t) := by
          rw [← pow_add]; congr 1; omega
        rw [h2]; ring
      · obtain ⟨e, he⟩ : ∃ e, 2 * max 2 ((t + 3) / 2) - t = e + 2 :=
          ⟨2 * max 2 ((t + 3) / 2) - t - 2, by omega⟩
        rw [he, pow_add]
        have : (2 : ℤ) ^ e * 2 ^ 2 * β + w₀ = 4 * (2 ^ e * β) + w₀ := by ring
        rw [this]; omega
    · have hw3 : w₀ % 4 = 3 := by omega
      rcases Nat.even_or_odd t with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- `t = 2m` even, `s = m`: `4^m o + 2^t w₀ = 2^t (o + w₀)`
        have hm1 : 1 ≤ m := by omega
        have hc4 := cS_emod_four hβ m
        have h48 : (cS β m + w₀) % 8 = 4 ∨ (cS β m + w₀) % 8 = 0 := by omega
        rcases h48 with h4 | h0
        · refine ⟨m, hm1, 4 - w₀, by omega, w_emod_eight hβ2 hm1 (by omega), t + 2, 1, ?_,
            by norm_num⟩
          rw [hCt, hm, four_pow_eq_two_pow, two_mul]; ring
        · refine ⟨m, hm1, 8 - w₀, by omega, w_emod_eight hβ2 hm1 (by omega), t + 3, 1, ?_,
            by norm_num⟩
          rw [hCt, hm, four_pow_eq_two_pow, two_mul]; ring
      · -- `t = 2m + 1` odd, `s = m + 1`, `o = c_s`: `4^s o + 2^t w₀ = 2^t (2o + w₀)`
        have hco : cS β (m + 1) % 2 = 1 := by
          have := cS_emod_four hβ (m + 1); omega
        refine ⟨m + 1, by omega, cS β (m + 1), hco, w_emod_eight hβ2 (by omega) rfl,
          t, 2 * cS β (m + 1) + w₀, ?_, by omega⟩
        rw [hCt, hm, four_pow_eq_two_pow]; ring

/-- **Lemma 3.1.** For an admissible pair `(B, A)` there is `n_* ∈ ℤ` with
`2n_* + B ≡ 1 (mod 4)`, `n_*(n_* + B) = 4^s w` with `s ≥ 1` and `w ≡ 1 (mod 8)` (so it is a
non-zero square in `ℚ₂` with positive valuation), and `n_* + A ∈ 𝒩`. -/
theorem nstar_exists {B A : ℤ} (h : Admissible B A) :
    ∃ n : ℤ, (2 * n + B) % 4 = 1 ∧
      (∃ s : ℕ, 1 ≤ s ∧ ∃ w : ℤ, n * (n + B) = 4 ^ s * w ∧ w % 8 = 1) ∧ InN (n + A) := by
  obtain ⟨hB, hBodd, hA0, hAB, h13, h32⟩ := h
  by_cases hB1 : B % 4 = 1
  · -- `σ = 1`: `n = 4^s o`, `β = B`, `C = A`
    obtain ⟨s, hs, o, -, hw, hN⟩ := nstar_core (β := B) (C := A) hB1 hA0 (fun hA => by omega)
    refine ⟨4 ^ s * o, ?_, ⟨s, hs, o * (4 ^ s * o + B), by ring, hw⟩, hN⟩
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
    have : 2 * (4 ^ (r + 1) * o) + B = 4 * (2 * 4 ^ r * o) + B := by ring
    rw [this]; omega
  · -- `σ = -1`: `n = 4^s o - B`, `β = -B`, `C = A - B`
    have hB3 : B % 4 = 3 := by omega
    obtain ⟨s, hs, o, -, hw, hN⟩ :=
      nstar_core (β := -B) (C := A - B) (by omega) (by omega) (fun hC => by omega)
    refine ⟨4 ^ s * o - B, ?_, ⟨s, hs, o * (4 ^ s * o + -B), by ring, hw⟩, ?_⟩
    · obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
      have : 2 * (4 ^ (r + 1) * o - B) + B = 4 * (2 * 4 ^ r * o) - B := by ring
      rw [this]; omega
    · have : 4 ^ s * o - B + A = 4 ^ s * o + (A - B) := by ring
      rw [this]; exact hN

end Triples
