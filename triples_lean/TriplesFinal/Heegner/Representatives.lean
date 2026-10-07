import TriplesFinal.Heegner.Reduction

/-!
# Existence of the systems of representatives of §8

There is a system `Λ` of representatives of the `SL₂(ℤ)`-orbits on `Q_N` consisting of reduced
forms (`exists_reduced_orbitReps`), and a system `𝒯` of representatives of the right cosets
`Γ₀(q) \ SL₂(ℤ)` (`exists_cosetReps`).

Paper: §8.
-/

namespace Triples

open CongruenceSubgroup SymMat
open scoped MatrixGroups

/-- The `SL₂(ℤ)`-orbit of `g`. -/
def orbitSL (g : SymMat) : Set SymMat := {g' | ∃ γ : SL(2, ℤ), g' = act γ g}

theorem orbitSL_eq {g g' : SymMat} (h : ∃ γ : SL(2, ℤ), g' = act γ g) :
    orbitSL g' = orbitSL g := by
  obtain ⟨γ, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ * γ, by rw [act_coe_mul]⟩
  · rintro ⟨δ, rfl⟩
    exact ⟨δ * γ⁻¹, by rw [act_coe_mul, act_coe_inv_act]⟩

/-- **Reduced orbit representatives exist** (reduction theory). -/
theorem exists_reduced_orbitReps {N : ℤ} (hN : 0 < N) :
    ∃ Λ : Set SymMat, IsOrbitReps N Λ ∧ ∀ ζ ∈ Λ, IsReduced ζ := by
  classical
  have : Nonempty SymMat := ⟨⟨0, 0, 0⟩⟩
  let red : Set SymMat → Set SymMat := fun O => {ζ | ζ ∈ O ∧ ζ ∈ QN N ∧ IsReduced ζ}
  have hne : ∀ g ∈ QN N, (red (orbitSL g)).Nonempty := by
    intro g hg
    obtain ⟨γ, hγ⟩ := exists_reduced hN hg
    exact ⟨act γ g, ⟨γ, rfl⟩, act_mem_QN hN γ.det_coe hg, hγ⟩
  let f : SymMat → SymMat := fun g => Classical.epsilon (fun ζ => ζ ∈ red (orbitSL g))
  have hf : ∀ g ∈ QN N, f g ∈ red (orbitSL g) := fun g hg => Classical.epsilon_spec (hne g hg)
  refine ⟨f '' QN N, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact (hf g hg).2.1
  · intro g hg
    refine ⟨f g, ⟨⟨g, hg, rfl⟩, ?_⟩, ?_⟩
    · obtain ⟨⟨γ, hγ⟩, -, -⟩ := hf g hg
      exact ⟨γ⁻¹, by rw [hγ, act_coe_inv_act]⟩
    · rintro ζ ⟨⟨g', hg', rfl⟩, γ, hγ⟩
      have h1 : orbitSL g = orbitSL (f g') := orbitSL_eq ⟨γ, hγ⟩
      obtain ⟨⟨δ, hδ⟩, -, -⟩ := hf g' hg'
      have h2 : orbitSL (f g') = orbitSL g' := orbitSL_eq ⟨δ, hδ⟩
      have h3 : orbitSL g = orbitSL g' := h1.trans h2
      simp only [f, h3]
  · rintro _ ⟨g, hg, rfl⟩
    exact (hf g hg).2.2

/-- **Coset representatives exist**: a system of representatives of `Γ₀(q) \ SL₂(ℤ)`. -/
theorem exists_cosetReps (q : ℕ) : ∃ T : Set SL(2, ℤ), IsCosetReps q T := by
  classical
  let r : Setoid SL(2, ℤ) := QuotientGroup.rightRel (Gamma0 q)
  refine ⟨Set.range (fun c : Quotient r => c.out), fun γ => ?_⟩
  have hrel : ∀ τ : SL(2, ℤ), r τ γ ↔ γ * τ⁻¹ ∈ Gamma0 q := fun τ => QuotientGroup.rightRel_apply
  refine ⟨(⟦γ⟧ : Quotient r).out, ⟨⟨_, rfl⟩, γ * ((⟦γ⟧ : Quotient r).out)⁻¹, ?_, ?_⟩, ?_⟩
  · exact (hrel _).1 (Quotient.mk_out (s := r) γ)
  · group
  · rintro τ ⟨⟨c, rfl⟩, δ, hδ, hγ⟩
    have h1 : r c.out γ := by
      rw [hrel, hγ, mul_inv_cancel_right]
      exact hδ
    have h2 : (⟦c.out⟧ : Quotient r) = ⟦γ⟧ := Quotient.sound h1
    rw [Quotient.out_eq] at h2
    rw [h2]

end Triples
