import TriplesFinal.Families.Identity
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Lemma 2.5: the automatic pair consists of sums of two squares

If `4dT = u² + m_d` with `d` a prime `≡ 1 (mod 4)` and `P = T - A ≥ 1`, then `P` and `P + B`
are sums of two squares.
Paper: §2, Lemma 2.5.
-/

namespace Triples

/-- A prime `ℓ ≡ 3 (mod 4)` dividing `u² + d²` divides `d`
(because `-1` is not a square modulo `ℓ`). -/
theorem dvd_of_dvd_sq_add_sq_of_three_mod_four {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ % 4 = 3)
    {u d : ℤ} (h : (ℓ : ℤ) ∣ u ^ 2 + d ^ 2) : (ℓ : ℤ) ∣ d := by
  have := Fact.mk hℓ
  by_contra hd
  have hd' : (d : ZMod ℓ) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h' : (u : ZMod ℓ) ^ 2 + (d : ZMod ℓ) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).2 h
    push_cast at this
    exact this
  have hsq : IsSquare (-1 : ZMod ℓ) := by
    refine ⟨(u : ZMod ℓ) * (d : ZMod ℓ)⁻¹, ?_⟩
    have hu : (u : ZMod ℓ) ^ 2 = -((d : ZMod ℓ) ^ 2) := by linear_combination h'
    calc (-1 : ZMod ℓ) = -(((d : ZMod ℓ) * (d : ZMod ℓ)⁻¹) ^ 2) := by
          rw [mul_inv_cancel₀ hd']; ring
      _ = (u : ZMod ℓ) ^ 2 * ((d : ZMod ℓ)⁻¹) ^ 2 := by rw [hu]; ring
      _ = (u : ZMod ℓ) * (d : ZMod ℓ)⁻¹ * ((u : ZMod ℓ) * (d : ZMod ℓ)⁻¹) := by ring
  exact (ZMod.exists_sq_eq_neg_one_iff.1 hsq) h3

/-- The parity criterion for one factor: if `p * p'` is a sum of two squares and no prime
`ℓ ≡ 3 (mod 4)` divides both `p` and `p'`, then `p` is a sum of two squares. -/
theorem isSumTwoSq_left_of_mul {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (hprod : ∃ x y : ℕ, p * p' = x ^ 2 + y ^ 2)
    (hcop : ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 3 → ℓ ∣ p → ¬ ℓ ∣ p') :
    ∃ x y : ℕ, p = x ^ 2 + y ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff] at hprod ⊢
  intro ℓ hℓ h3
  have hℓp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hdvd : ℓ ∣ p := Nat.dvd_of_mem_primeFactors hℓ
  have hnd : ¬ ℓ ∣ p' := hcop ℓ hℓp h3 hdvd
  have := Fact.mk hℓp
  have hmem : ℓ ∈ (p * p').primeFactors :=
    Nat.mem_primeFactors.2 ⟨hℓp, dvd_mul_of_dvd_left hdvd _, by positivity⟩
  have hev := hprod ℓ hmem h3
  rw [padicValNat.mul hp.ne' hp'.ne', padicValNat.eq_zero_of_not_dvd hnd, add_zero] at hev
  exact hev

/-- **Lemma 2.5.** Suppose `4dT = u² + m_d`, where `d` is a prime with `d ≡ 1 (mod 4)`, and
`P = T - A ≥ 1`, `B > 0`. Then `P` and `P + B` are sums of two squares. -/
theorem split {B A d u T : ℤ} (hdprime : d.natAbs.Prime) (hd0 : 0 < d) (hd4 : d % 4 = 1)
    (hB : 0 < B) (h : 4 * d * T = u ^ 2 + mVal B A d) (hP : 1 ≤ T - A) :
    IsSumTwoSq (T - A) ∧ IsSumTwoSq (T - A + B) := by
  obtain ⟨h1, h2, h3⟩ := identity h
  set P := T - A with hPdef
  set Q := 2 * P + B with hQdef
  -- `P (P + B)` is a sum of two squares
  have hprodZ : IsSumTwoSq (P * (P + B)) := by
    apply IsSumTwoSq.of_four_mul
    exact ⟨Q - d, u, by rw [← h3, ← h2]; ring⟩
  -- pass to natural numbers
  lift P to ℕ using (by omega) with p hp
  have hpB : 0 ≤ (p : ℤ) + B := by omega
  lift B to ℕ using hB.le with b hb
  have hp0 : 0 < p := by omega
  have hb0 : 0 < b := by exact_mod_cast hB
  have hprodN : ∃ x y : ℕ, p * (p + b) = x ^ 2 + y ^ 2 := by
    rw [← isSumTwoSq_natCast_iff]; push_cast; exact hprodZ
  -- no prime `ℓ ≡ 3 (mod 4)` divides both `p` and `p + b`
  have hcop : ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 3 → ℓ ∣ p → ¬ ℓ ∣ p + b := by
    intro ℓ hℓ hℓ3 hlp hlpb
    have hlb : ℓ ∣ b := (Nat.dvd_add_right hlp).1 hlpb
    have hlQ : (ℓ : ℤ) ∣ Q := by
      rw [hQdef]
      exact dvd_add (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.2 hlp) _)
        (Int.natCast_dvd_natCast.2 hlb)
    have hlsum : (ℓ : ℤ) ∣ u ^ 2 + d ^ 2 := by
      have hB2 : (ℓ : ℤ) ∣ (b : ℤ) ^ 2 :=
        dvd_pow (Int.natCast_dvd_natCast.2 hlb) two_ne_zero
      have hdQ : (ℓ : ℤ) ∣ 2 * d * Q := dvd_mul_of_dvd_right hlQ _
      have : u ^ 2 + d ^ 2 = 2 * d * Q - (b : ℤ) ^ 2 := by linarith
      rw [this]; exact dvd_sub hdQ hB2
    have hld : (ℓ : ℤ) ∣ d := dvd_of_dvd_sq_add_sq_of_three_mod_four hℓ hℓ3 hlsum
    have hld' : ℓ ∣ d.natAbs := Int.natCast_dvd.1 hld
    have : ℓ = d.natAbs := (Nat.prime_dvd_prime_iff_eq hℓ hdprime).1 hld'
    have hdn : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd0.le
    omega
  constructor
  · have := isSumTwoSq_left_of_mul hp0 (by omega) hprodN hcop
    rw [← isSumTwoSq_natCast_iff] at this
    exact this
  · have hprodN' : ∃ x y : ℕ, (p + b) * p = x ^ 2 + y ^ 2 := by
      rw [mul_comm]; exact hprodN
    have hcop' : ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 3 → ℓ ∣ p + b → ¬ ℓ ∣ p :=
      fun ℓ hℓ h3 h1 h2 => hcop ℓ hℓ h3 h2 h1
    have := isSumTwoSq_left_of_mul (by omega) hp0 hprodN' hcop'
    rw [← isSumTwoSq_natCast_iff] at this
    push_cast at this
    exact this

end Triples
