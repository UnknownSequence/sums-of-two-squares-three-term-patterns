import TriplesFinal.Basic.Defs

/-!
# Definition 2.2 and Lemma 2.3: admissible pairs and the choice of the automatic pair

Paper: §2, Definition 2.2, Lemma 2.3 and Table 2.
-/

namespace Triples

/-- **Definition 2.2.** A pair `(B, A)` is *admissible* if `B > 0` is odd, `A ∉ {0, B}`, and
neither `B ≡ 1, A ≡ 3 (mod 4)` nor `B ≡ 3, A ≡ 2 (mod 4)`. -/
def Admissible (B A : ℤ) : Prop :=
  0 < B ∧ B % 2 = 1 ∧ A ≠ 0 ∧ A ≠ B ∧ ¬(B % 4 = 1 ∧ A % 4 = 3) ∧ ¬(B % 4 = 3 ∧ A % 4 = 2)

/-- The choice `(p₀, B, A)` of Table 2 (for `0 < a < b` with `a` or `b` odd). -/
def choice (a b : ℤ) : ℤ × ℤ × ℤ :=
  if a % 2 = 1 ∧ b % 2 = 0 then
    (if a % 4 = 3 ∧ b % 4 = 2 then (a, b - a, -a) else (0, a, b))
  else if a % 2 = 0 ∧ b % 2 = 1 then
    (if a % 4 = 2 ∧ b % 4 = 3 then (a, b - a, -a) else (0, b, a))
  else
    (if a % 4 = 1 ∧ b % 4 = 3 then (0, b, a) else (0, a, b))

/-- **Lemma 2.3**, with the explicit choice of Table 2: `p₀ ∈ {0, a}`, `(B, A)` is admissible, and
`{n + p₀, n + p₀ + B, n + p₀ + A} = {n, n + a, n + b}` for every `n`. -/
theorem choice_spec {a b : ℤ} (h0 : 0 < a) (h1 : a < b) (hodd : a % 2 = 1 ∨ b % 2 = 1) :
    ((choice a b).1 = 0 ∨ (choice a b).1 = a) ∧
    Admissible (choice a b).2.1 (choice a b).2.2 ∧
    ∀ n : ℤ, ({n + (choice a b).1, n + (choice a b).1 + (choice a b).2.1,
      n + (choice a b).1 + (choice a b).2.2} : Finset ℤ) = {n, n + a, n + b} := by
  unfold choice Admissible
  split_ifs <;> dsimp only <;>
    refine ⟨by simp, ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, fun n => ?_⟩ <;>
    ext m <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> omega

/-- **Lemma 2.3.** For `0 < a < b` with `a` or `b` odd there are `p₀ ∈ {0, a}` and an admissible
pair `(B, A)` with `{n + p₀, n + p₀ + B, n + p₀ + A} = {n, n + a, n + b}` for all `n`. -/
theorem exists_choice {a b : ℤ} (h0 : 0 < a) (h1 : a < b) (hodd : a % 2 = 1 ∨ b % 2 = 1) :
    ∃ p₀ B A : ℤ, (p₀ = 0 ∨ p₀ = a) ∧ Admissible B A ∧
      ∀ n : ℤ, ({n + p₀, n + p₀ + B, n + p₀ + A} : Finset ℤ) = {n, n + a, n + b} :=
  ⟨_, _, _, choice_spec h0 h1 hodd⟩

end Triples
