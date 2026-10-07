import TriplesFinal.Basic.Defs

/-!
# Lemma 2.1: reduction to patterns with an odd difference

If `a` and `b` are both even, then `S_{a,b}(x) ≥ S_{a/2,b/2}(x/2)`.
Paper: §2, Lemma 2.1.
-/

namespace Triples

/-- **Lemma 2.1.** If `a` and `b` are both even, then `S_{a/2,b/2}(x/2) ≤ S_{a,b}(x)`. -/
theorem S_half_le_S (a b : ℕ) (x : ℝ) (ha : Even a) (hb : Even b) :
    S (a / 2) (b / 2) (x / 2) ≤ S a b x := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hA : (a' + a') / 2 = a' := by omega
  have hB : (b' + b') / 2 = b' := by omega
  rw [hA, hB]
  unfold S
  refine Set.ncard_le_ncard_of_injOn (fun n => 2 * n) ?_ ?_ (SSet_finite _ _ _)
  · rintro n ⟨h1, hx, h0, ha', hb'⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · push_cast; linarith
    · have := h0.two_mul
      push_cast; exact this
    · have := ha'.two_mul
      push_cast
      convert this using 1; ring
    · have := hb'.two_mul
      push_cast
      convert this using 1; ring
  · intro m _ n _ h
    simp only at h
    omega

end Triples
