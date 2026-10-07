import TriplesFinal.TwoAdic.NStar

/-!
# Proposition 3.2: the `2`-adic seed

For an admissible pair `(B, A)` there are `v ≥ 2` and `d₀ ≡ 1 (mod 4)` such that, with
`J = v + 2` and `j = ⌈(v + 2)/2⌉`, for all `d ≡ d₀ (mod 2^J)` and `u ≡ 0 (mod 2^j)`:
`u² + m_d = 2^v w` with `w ≡ d (mod 4)` (so `v₂(u² + m_d) = v`).
Consequently, if moreover `d` is a prime dividing `u² + B²`, then `T = (u² + m_d)/(4d)` is an
integer of the form `2^{v-2} T'` with `T' ≡ 1 (mod 4)`.

Paper: §3, Proposition 3.2. We follow the paper's proof, replacing the `2`-adic square root `t_*`
by a square root modulo a sufficiently high power of `2`.
-/

namespace Triples

/-- Odd square roots modulo `2^(K+3)` of integers `w ≡ 1 (mod 8)`. -/
theorem exists_odd_sqrt_mod {w : ℤ} (hw : w % 8 = 1) (K : ℕ) :
    ∃ ρ : ℤ, ρ % 2 = 1 ∧ (2 : ℤ) ^ (K + 3) ∣ ρ ^ 2 - w := by
  induction K with
  | zero => exact ⟨1, by norm_num, by norm_num; exact Int.dvd_of_emod_eq_zero (by omega)⟩
  | succ K ih =>
    obtain ⟨ρ, hρ, e, he⟩ := ih
    rcases Int.even_or_odd e with ⟨f, hf⟩ | ⟨f, hf⟩
    · refine ⟨ρ, hρ, f, ?_⟩
      rw [he, hf]; ring
    · obtain ⟨g, hg⟩ : ∃ g, ρ = 2 * g + 1 := ⟨ρ / 2, by omega⟩
      refine ⟨ρ + 2 ^ (K + 2), ?_, f + g + 1 + 2 ^ K, ?_⟩
      · have : (2 : ℤ) ^ (K + 2) = 2 * (2 * 2 ^ K) := by ring
        rw [this]; omega
      · have h1 : (ρ + 2 ^ (K + 2)) ^ 2 - w =
            (ρ ^ 2 - w) + 2 ^ (K + 3) * ρ + 2 ^ (2 * K + 4) := by ring
        rw [h1, he, hf, hg]; ring

/-- The exponent `j = ⌈(v + 2)/2⌉`. -/
def jOf (v : ℕ) : ℕ := (v + 3) / 2

theorem two_mul_jOf (v : ℕ) : v + 2 ≤ 2 * jOf v := by unfold jOf; omega

/-- **Proposition 3.2.** -/
theorem seed_exists {B A : ℤ} (h : Admissible B A) :
    ∃ v : ℕ, 2 ≤ v ∧ ∃ d₀ : ℤ, d₀ % 4 = 1 ∧
      ∀ d u : ℤ, d ≡ d₀ [ZMOD 2 ^ (v + 2)] → u ≡ 0 [ZMOD 2 ^ jOf v] →
        ∃ w : ℤ, u ^ 2 + mVal B A d = 2 ^ v * w ∧ w ≡ d [ZMOD 4] := by
  obtain ⟨n, hQ, ⟨s, hs, w, hw, hw8⟩, ⟨τ, w', hT, hw'⟩⟩ := nstar_exists h
  obtain ⟨ρ, -, R, hR⟩ := exists_odd_sqrt_mod hw8 (τ + 4)
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  -- `t = 2^(s+1) ρ` and `d₀ = Q - t`
  set d₀ := 2 * n + B - 2 ^ (r + 2) * ρ with hd₀
  -- the key identity `m_{d₀} = 4 d₀ (n + A) + 4^(s+1) (ρ² - w)`
  have key : mVal B A d₀ = 4 * d₀ * (n + A) + 4 ^ (r + 2) * (ρ ^ 2 - w) := by
    have h1 : mVal B A d₀ - 4 * d₀ * (n + A) =
        (2 ^ (r + 2) * ρ) ^ 2 - 4 * (n * (n + B)) := by
      rw [hd₀]; unfold mVal; ring
    have h2 : (2 ^ (r + 2) * ρ) ^ 2 - 4 * (n * (n + B)) = 4 ^ (r + 2) * (ρ ^ 2 - w) := by
      rw [hw, four_pow_eq_two_pow, four_pow_eq_two_pow]; ring
    linarith
  refine ⟨τ + 2, by omega, d₀, ?_, ?_⟩
  · have : d₀ = 2 * n + B - 4 * (2 ^ r * ρ) := by rw [hd₀]; ring
    rw [this]; omega
  · intro d u hd hu
    obtain ⟨D, hD⟩ := (Int.modEq_iff_dvd.1 hd)
    obtain ⟨U, hU⟩ := (Int.modEq_iff_dvd.1 hu)
    obtain ⟨W, hW⟩ : ∃ W, w' = 4 * W + 1 := ⟨w' / 4, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, 2 * jOf (τ + 2) = (τ + 2 + 2) + e :=
      ⟨2 * jOf (τ + 2) - (τ + 2 + 2), by have := two_mul_jOf (τ + 2); omega⟩
    have hu' : u = -(2 ^ jOf (τ + 2) * U) := by linarith
    have hd' : d = d₀ - 2 ^ (τ + 2 + 2) * D := by linarith
    -- `u² + m_d - 2^v d = 2^(v+2) X`
    set X : ℤ := 2 ^ e * U ^ 2 - D * (2 * d₀ - 2 ^ (τ + 2 + 2) * D + 2 * (2 * A - B)) +
      8 * 4 ^ (r + 2) * R + d₀ * W + 2 ^ (τ + 2) * D with hX
    refine ⟨d + 4 * X, ?_, ?_⟩
    · have hu2 : u ^ 2 = 2 ^ (τ + 2 + 2) * (2 ^ e * U ^ 2) := by
        rw [hu', neg_sq, mul_pow, ← pow_mul, mul_comm (jOf (τ + 2)) 2, he, pow_add]; ring
      have hmd : mVal B A d = mVal B A d₀ -
          2 ^ (τ + 2 + 2) * D * (2 * d₀ - 2 ^ (τ + 2 + 2) * D + 2 * (2 * A - B)) := by
        rw [hd']; unfold mVal; ring
      rw [hu2, hmd, key, hT, hW, hR, hX, hd']
      ring
    · exact Int.modEq_iff_dvd.2 ⟨-X, by ring⟩

/-- **Proposition 3.2, consequence.** If, in addition, `d` is a prime (with `d > 0`) dividing
`u² + B²`, then `u² + m_d = 4d · 2^(v-2) T'` with `T' ≡ 1 (mod 4)`. -/
theorem seed_T {B A : ℤ} {v : ℕ} {d u w : ℤ} (hv : 2 ≤ v) (hdp : Prime d) (hd4 : d % 4 = 1)
    (hdu : d ∣ u ^ 2 + B ^ 2) (hw : u ^ 2 + mVal B A d = 2 ^ v * w) (hwd : w ≡ d [ZMOD 4]) :
    ∃ T' : ℤ, T' % 4 = 1 ∧ u ^ 2 + mVal B A d = 4 * d * (2 ^ (v - 2) * T') := by
  have hdm : d ∣ u ^ 2 + mVal B A d := by
    have h1 := mVal_sub_sq_dvd B A d
    have : u ^ 2 + mVal B A d = (u ^ 2 + B ^ 2) + (mVal B A d - B ^ 2) := by ring
    rw [this]; exact dvd_add hdu h1
  have hdw : d ∣ w := by
    rw [hw] at hdm
    rcases hdp.dvd_or_dvd hdm with h2 | h2
    · exfalso
      have hd2 : d ∣ 2 := hdp.dvd_of_dvd_pow h2
      have hnat : d.natAbs ∣ 2 := by
        have := Int.natAbs_dvd_natAbs.2 hd2
        simpa using this
      rcases (Nat.dvd_prime Nat.prime_two).1 hnat with h1 | h1
      · exact hdp.not_isUnit (Int.isUnit_iff_natAbs_eq.2 h1)
      · rcases Int.natAbs_eq d with h3 | h3 <;> rw [h1] at h3 <;> omega
    · exact h2
  obtain ⟨T', rfl⟩ := hdw
  refine ⟨T', ?_, ?_⟩
  · have hmod : (d * T') % 4 = d % 4 := hwd
    rw [Int.mul_emod, hd4, one_mul, Int.emod_emod] at hmod
    exact hmod
  · rw [hw]
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 2 := ⟨v - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_add]; ring

end Triples
