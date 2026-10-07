import TriplesFinal.Families.Identity
import TriplesFinal.Basic.Reps

/-!
# Lemma 2.6: multiplicities

For fixed `n`, the number of pairs `(d, u)` with `d ≥ 1` and `4dT = u² + m_d` is at most
`r(P(P + B))`, where `P = T - A`.
Paper: §2, Lemma 2.6.
-/

namespace Triples

/-- The set of pairs `(d, u)` with `d ≥ 1` and `4dT = u² + m_d`. -/
def multSet (B A T : ℤ) : Set (ℤ × ℤ) :=
  {du : ℤ × ℤ | 1 ≤ du.1 ∧ 4 * du.1 * T = du.2 ^ 2 + mVal B A du.1}

/-- `(d, u) ↦ (Q - d, u)` maps `multSet` into the representations of `4P(P + B)`. -/
theorem multSet_mapsTo (B A T : ℤ) :
    Set.MapsTo (fun du : ℤ × ℤ => (2 * (T - A) + B - du.1, du.2)) (multSet B A T)
      (repSet (4 * ((T - A) * (T - A + B)))) := by
  rintro ⟨d, u⟩ ⟨-, h⟩
  obtain ⟨-, h2, h3⟩ := identity h
  simp only [repSet, Set.mem_ofPred_eq]
  rw [← h3, ← h2]
  ring

theorem multSet_injOn (B A T : ℤ) :
    Set.InjOn (fun du : ℤ × ℤ => (2 * (T - A) + B - du.1, du.2)) (multSet B A T) := by
  rintro ⟨d, u⟩ - ⟨d', u'⟩ - h
  simp only [Prod.mk.injEq] at h
  ext <;> simp <;> omega

theorem multSet_finite (B A T : ℤ) : (multSet B A T).Finite :=
  Set.Finite.of_injOn (multSet_mapsTo B A T) (multSet_injOn B A T) (repSet_finite _)

/-- **Lemma 2.6.** `#{(d, u) : d ≥ 1, 4dT = u² + m_d} ≤ r(P(P + B))` with `P = T - A`. -/
theorem mult_bound (B A T : ℤ) : (multSet B A T).ncard ≤ r ((T - A) * (T - A + B)) := by
  calc _ ≤ (repSet (4 * ((T - A) * (T - A + B)))).ncard :=
        Set.ncard_le_ncard_of_injOn _ (multSet_mapsTo B A T) (multSet_injOn B A T)
          (repSet_finite _)
    _ = r ((T - A) * (T - A + B)) := by rw [← r_eq_ncard, r_four_mul]

end Triples
