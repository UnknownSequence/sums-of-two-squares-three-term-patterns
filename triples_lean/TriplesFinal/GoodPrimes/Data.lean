import TriplesFinal.Families.Choice
import TriplesFinal.TwoAdic.Seed

/-!
# Section 4: the data attached to a pattern, and good primes

For a pattern `{0, a, b}` with `a` or `b` odd we fix the choice `(p₀, B, A)` of Lemma 2.3 and a
`2`-adic seed `(v, d₀)` of Proposition 3.2, and put `J = v + 2`, `j = ⌈(v + 2)/2⌉`,
`E = 2^(2j - v) ∈ {4, 8}` (equation (4.1)).

Paper: §4, equations (4.1)–(4.3), Definition of good primes.
-/

namespace Triples

/-- The data fixed for a pattern `{0, a, b}` with `a` or `b` odd. -/
structure PatternData (a b : ℕ) where
  /-- the offset `p₀ ∈ {0, a}` -/
  p₀ : ℤ
  /-- the odd difference `B` of the automatic pair -/
  B : ℤ
  /-- the offset `A` of the detected element -/
  A : ℤ
  /-- the `2`-adic valuation `v` of Proposition 3.2 -/
  v : ℕ
  /-- the residue class `d₀ (mod 2^(v+2))` of Proposition 3.2 -/
  d₀ : ℤ
  ha : 0 < a
  hab : a < b
  hp₀ : p₀ = 0 ∨ p₀ = a
  adm : Admissible B A
  triple : ∀ n : ℤ, ({n + p₀, n + p₀ + B, n + p₀ + A} : Finset ℤ) = {n, n + a, n + b}
  hv : 2 ≤ v
  hd₀ : d₀ % 4 = 1
  seed : ∀ d u : ℤ, d ≡ d₀ [ZMOD 2 ^ (v + 2)] → u ≡ 0 [ZMOD 2 ^ jOf v] →
    ∃ w : ℤ, u ^ 2 + mVal B A d = 2 ^ v * w ∧ w ≡ d [ZMOD 4]

/-- Every pattern with `a` or `b` odd has pattern data (Lemma 2.3 and Proposition 3.2). -/
theorem PatternData.nonempty {a b : ℕ} (h0 : 0 < a) (h1 : a < b)
    (hodd : a % 2 = 1 ∨ b % 2 = 1) : Nonempty (PatternData a b) := by
  obtain ⟨p₀, B, A, hp₀, hadm, htr⟩ :=
    exists_choice (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
      (by omega)
  obtain ⟨v, hv, d₀, hd₀, hseed⟩ := seed_exists hadm
  exact ⟨⟨p₀, B, A, v, d₀, h0, h1, hp₀, hadm, htr, hv, hd₀, hseed⟩⟩

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `J = v + 2`. -/
def J : ℕ := P.v + 2
/-- `j = ⌈(v + 2)/2⌉`. -/
def j : ℕ := jOf P.v
/-- `E = 2^(2j - v)`. -/
def E : ℤ := 2 ^ (2 * P.j - P.v)
/-- `c = 2A - B`. -/
def c : ℤ := 2 * P.A - P.B
/-- `d₁ = 8(|c| + B)`. -/
def d₁ : ℤ := 8 * (|P.c| + P.B)
/-- `m_d = d² + 2cd + B²`. -/
def m (d : ℤ) : ℤ := mVal P.B P.A d
/-- `H_d = 2^(-v) m_d`. -/
def H (d : ℤ) : ℤ := P.m d / 2 ^ P.v
/-- `N_d = E H_d`. -/
def N (d : ℤ) : ℤ := P.E * P.H d
/-- `T_d(ℓ) = 2^(v-2) (E ℓ² + H_d)/d = ((2^j ℓ)² + m_d)/(4d)`, equation (4.3). -/
def T (d ℓ : ℤ) : ℤ := ((2 ^ P.j * ℓ) ^ 2 + P.m d) / (4 * d)

/-- **Good primes** (§4): `d ≡ d₀ (mod 2^J)`, `d > d₁`, and neither `m_d` nor `m_d/3` is a
perfect square. -/
def IsGood (d : ℕ) : Prop :=
  d.Prime ∧ (d : ℤ) ≡ P.d₀ [ZMOD 2 ^ P.J] ∧ P.d₁ < d ∧ (¬ ∃ s : ℤ, P.m d = s ^ 2) ∧
    ¬ ∃ s : ℤ, P.m d = 3 * s ^ 2

theorem j_le_v : P.j ≤ P.v := by
  have := P.hv; unfold j jOf; omega

theorem v_add_two_le_two_j : P.v + 2 ≤ 2 * P.j := two_mul_jOf P.v

/-- `E ∈ {4, 8}`. -/
theorem E_eq : P.E = 4 ∨ P.E = 8 := by
  unfold E j jOf
  have h : 2 * ((P.v + 3) / 2) - P.v = 2 ∨ 2 * ((P.v + 3) / 2) - P.v = 3 := by omega
  rcases h with h | h <;> rw [h] <;> norm_num

/-- `2^v E = 2^(2j)`. -/
theorem two_pow_v_mul_E : (2 : ℤ) ^ P.v * P.E = 2 ^ (2 * P.j) := by
  unfold E
  rw [← pow_add]; congr 1; have := P.v_add_two_le_two_j; omega

/-- For `d ≡ d₀ (mod 2^J)`: `m_d = 2^v H_d` with `H_d ≡ d (mod 4)` (Proposition 3.2 with
`u = 0`). -/
theorem m_eq (d : ℤ) (hd : d ≡ P.d₀ [ZMOD 2 ^ P.J]) :
    P.m d = 2 ^ P.v * P.H d ∧ P.H d ≡ d [ZMOD 4] := by
  obtain ⟨w, hw, hwd⟩ := P.seed d 0 hd (by simp [Int.ModEq])
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hw
  have hH : P.H d = w := by
    unfold H m
    rw [hw, Int.mul_ediv_cancel_left _ (by positivity)]
  unfold m
  rw [hH]
  exact ⟨hw, hwd⟩

/-- Equation (4.2): `(2^j ℓ)² + m_d = 2^v (E ℓ² + H_d)` for `d ≡ d₀ (mod 2^J)`. -/
theorem poly_identity (d ℓ : ℤ) (hd : d ≡ P.d₀ [ZMOD 2 ^ P.J]) :
    (2 ^ P.j * ℓ) ^ 2 + P.m d = 2 ^ P.v * (P.E * ℓ ^ 2 + P.H d) := by
  obtain ⟨hm, -⟩ := P.m_eq d hd
  have h := P.two_pow_v_mul_E
  rw [hm, mul_pow, ← pow_mul, mul_comm P.j 2, ← h]
  ring

/-- `H_d` is odd for `d ≡ d₀ (mod 2^J)`. -/
theorem H_odd (d : ℤ) (hd : d ≡ P.d₀ [ZMOD 2 ^ P.J]) : P.H d % 2 = 1 := by
  obtain ⟨-, hH⟩ := P.m_eq d hd
  have h4 : d % 4 = 1 := by
    have h1 : (2 : ℤ) ^ P.J = 4 * 2 ^ P.v := by unfold J; rw [pow_add]; ring
    have := Int.ModEq.of_mul_right (2 ^ P.v) (h1 ▸ hd)
    have h2 : d % 4 = P.d₀ % 4 := this
    rw [h2]; exact P.hd₀
  have : P.H d % 4 = d % 4 := hH
  omega

end PatternData

end Triples
