import TriplesFinal.Basic.Defs

/-!
# Lemma 2.4: the identity behind the automatic pair

With `c = 2A - B` and `m_d = d² + 2cd + B²` (equation (2.2)), if `4dT = u² + m_d` and
`P = T - A`, `Q = 2P + B`, then `2dQ = u² + d² + B²` and `4P(P + B) = Q² - B² = (Q - d)² + u²`.
Paper: §2, equations (2.1)–(2.2), Lemma 2.4.
-/

namespace Triples

/-- `m_d = d² + 2cd + B²` with `c = 2A - B`, equation (2.2). -/
def mVal (B A d : ℤ) : ℤ := d ^ 2 + 2 * (2 * A - B) * d + B ^ 2

/-- The second form of (2.2): `m_d = (d + c)² + 4A(B - A)`. -/
theorem mVal_eq (B A d : ℤ) : mVal B A d = (d + (2 * A - B)) ^ 2 + 4 * A * (B - A) := by
  unfold mVal; ring

/-- `m_d ≡ B² (mod d)`. -/
theorem mVal_sub_sq_dvd (B A d : ℤ) : d ∣ mVal B A d - B ^ 2 :=
  ⟨d + 2 * (2 * A - B), by unfold mVal; ring⟩

/-- **Lemma 2.4.** If `4dT = u² + m_d`, `P = T - A` and `Q = 2P + B`, then `2dQ = u² + d² + B²`,
`4P(P + B) = Q² - B²` and `Q² - B² = (Q - d)² + u²`. -/
theorem identity {B A d u T : ℤ} (h : 4 * d * T = u ^ 2 + mVal B A d) :
    2 * d * (2 * (T - A) + B) = u ^ 2 + d ^ 2 + B ^ 2 ∧
    4 * (T - A) * (T - A + B) = (2 * (T - A) + B) ^ 2 - B ^ 2 ∧
    (2 * (T - A) + B) ^ 2 - B ^ 2 = (2 * (T - A) + B - d) ^ 2 + u ^ 2 := by
  unfold mVal at h
  exact ⟨by linear_combination h, by ring, by linear_combination h⟩

end Triples
