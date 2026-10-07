import TriplesFinal.Poisson.Unfolding

/-!
# Reduction theory for `Q_N`

Every `𝔤 ∈ Q_N` is `SL₂(ℤ)`-equivalent to a reduced matrix (`|2𝔟| ≤ 𝔠 ≤ 𝔞`): take `𝔠` minimal
in the orbit, translate so that `|2𝔟| ≤ 𝔠`, and note that `𝔞 < 𝔠` would allow `S = (0, -1; 1, 0)`
to decrease `𝔠` (`exists_reduced`). There are finitely many reduced matrices
(`finite_reduced`), so every system of orbit representatives is finite (`IsOrbitReps.finite`),
and so is the set of Heegner representatives `𝔤_1, …, 𝔤_I` (`heegnerReps_finite`, with
Lemma 8.3).

Paper: §8.1 ("every `SL₂(ℤ)`-orbit in `Q_N` contains a reduced element, and there are finitely
many reduced elements").
-/

namespace Triples

open scoped MatrixGroups
open CongruenceSubgroup

namespace SymMat

/-- `S = (0, -1; 1, 0)`. -/
def mS : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

theorem det_mS : mS.det = 1 := by simp [mS, Matrix.det_fin_two_of]

/-- `S` as an element of `SL₂(ℤ)`. -/
def sS : SL(2, ℤ) := ⟨mS, det_mS⟩

theorem act_mS (g : SymMat) : act mS g = ⟨g.c, -g.b, g.a⟩ := by
  ext <;> simp [act, mS]

/-- **Reduction theory**: every `𝔤 ∈ Q_N` is `SL₂(ℤ)`-equivalent to a reduced matrix
(`|2𝔟| ≤ 𝔠 ≤ 𝔞`). Take `𝔠` minimal in the orbit, translate so that `|2𝔟| ≤ 𝔠`; then `𝔞 ≥ 𝔠`,
since otherwise `S` would decrease `𝔠`. -/
theorem exists_reduced {N : ℤ} (hN : 0 < N) {g : SymMat} (hg : g ∈ QN N) :
    ∃ γ : SL(2, ℤ), IsReduced (act γ g) := by
  classical
  have hP : ∃ n : ℕ, ∃ γ : SL(2, ℤ), (act γ g).c = n :=
    ⟨g.c.toNat, 1, by rw [act_coe_one, Int.toNat_of_nonneg hg.2.1.le]⟩
  obtain ⟨γ₀, hγ₀⟩ := Nat.find_spec hP
  set n₀ := Nat.find hP with hn₀
  have hmin : ∀ γ : SL(2, ℤ), (n₀ : ℤ) ≤ (act γ g).c := by
    intro γ
    have hpos := (act_mem_QN hN γ.det_coe hg).2.1
    have h1 := Nat.find_min' hP ⟨γ, (Int.toNat_of_nonneg hpos.le).symm⟩
    have h2 : ((act γ g).c.toNat : ℤ) = (act γ g).c := Int.toNat_of_nonneg hpos.le
    omega
  set g₀ := act γ₀ g with hg₀def
  have hg₀ : g₀ ∈ QN N := act_mem_QN hN γ₀.det_coe hg
  have hc0 : 0 < g₀.c := hg₀.2.1
  set t := -((2 * g₀.b + g₀.c) / (2 * g₀.c)) with ht
  set g₁ := act (mT t) g₀ with hg₁def
  have hg₁ : g₁ ∈ QN N := act_mT_mem_QN hN hg₀ t
  have hg₁c : g₁.c = g₀.c := act_mT_c t g₀
  have hg₁b : |2 * g₁.b| ≤ g₁.c := by
    rw [hg₁c, hg₁def, act_mT_b, ht]
    have h2c : 0 < 2 * g₀.c := by linarith
    have hmod := Int.emod_add_mul_ediv (2 * g₀.b + g₀.c) (2 * g₀.c)
    have hlt := Int.emod_lt_of_pos (2 * g₀.b + g₀.c) h2c
    have hnn := Int.emod_nonneg (2 * g₀.b + g₀.c) h2c.ne'
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨sT t * γ₀, ?_⟩
  have e : act ((sT t * γ₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g = g₁ := by
    rw [act_coe_mul]; rfl
  rw [e]
  refine ⟨hg₁b, ?_⟩
  by_contra hlt
  push Not at hlt
  have h := hmin (sS * (sT t * γ₀))
  have e2 : act ((sS * (sT t * γ₀) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g = act mS g₁ := by
    rw [act_coe_mul, e]; rfl
  rw [e2, act_mS] at h
  simp only at h
  have : (n₀ : ℤ) = g₁.c := by rw [hg₁c]; exact hγ₀.symm
  omega

/-- The reduced matrices of `Q_N` form a finite set. -/
theorem finite_reduced {N : ℤ} (hN : 0 < N) : {g | g ∈ QN N ∧ IsReduced g}.Finite := by
  have := finite_ncard_le_of_b_sq (K := 1) hN (S := {g | g ∈ QN N ∧ IsReduced g})
    (fun g hg => hg.1) (fun g hg => by
      have := (reduced_bounds hg.1 hg.2).2.1
      simpa using this)
  exact this.1

/-- A system of representatives of the `SL₂(ℤ)`-orbits on `Q_N` is finite. -/
theorem IsOrbitReps.finite {N : ℤ} (hN : 0 < N) {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ) :
    Λ.Finite := by
  classical
  have hex : ∀ ζ : SymMat, ∃ γ : SL(2, ℤ), ζ ∈ QN N → IsReduced (act γ ζ) := by
    intro ζ
    by_cases hζ : ζ ∈ QN N
    · obtain ⟨γ, hγ⟩ := exists_reduced hN hζ
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨1, fun h => absurd h hζ⟩
  choose F hF using hex
  refine Set.Finite.of_finite_image (f := fun ζ => act (F ζ) ζ) ?_ ?_
  · apply (finite_reduced hN).subset
    rintro _ ⟨ζ, hζ, rfl⟩
    exact ⟨act_mem_QN hN (F ζ).det_coe (hΛ.1 hζ), hF ζ (hΛ.1 hζ)⟩
  · intro ζ hζ ζ' hζ' he
    simp only at he
    -- `ζ' = (F ζ')⁻¹ (F ζ) ⋄ ζ`
    have h1 : ζ' = act (((F ζ')⁻¹ * F ζ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ζ := by
      rw [act_coe_mul, he, act_coe_inv_act]
    exact (ExistsUnique.unique (hΛ.2 ζ' (hΛ.1 hζ')) ⟨hζ', 1, (act_coe_one ζ').symm⟩
      ⟨hζ, _, h1⟩).symm

/-- The Heegner representatives `𝔤_1, …, 𝔤_I` form a finite set. -/
theorem heegnerReps_finite {E H d κ : ℤ} (hE : E = 4 ∨ E = 8) (hH : 0 < H) (hd : Prime d)
    (hd0 : 0 < d) (hd2 : d ≠ 2) (hdH : ¬ d ∣ H) {q : ℕ} (hq : (q : ℤ) = 4 * E * d)
    {Λ : Set SymMat} (hΛ : IsOrbitReps (E * H) Λ) {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) :
    (heegnerReps Λ T (Qkappa E H d κ)).Finite := by
  have hN : 0 < E * H := by rcases hE with rfl | rfl <;> positivity
  have hQ : Qkappa E H d κ ⊆ {g | g ∈ QN (E * H) ∧ d ∣ g.c} := by
    rintro g ⟨hgQ, -, hgc⟩
    refine ⟨hgQ, ?_⟩
    have h1 : 4 * E * d ∣ κ * E * d - g.c := Int.ModEq.dvd hgc
    have h2 : d ∣ κ * E * d - g.c := (dvd_mul_left d (4 * E)).trans h1
    have h4 : d ∣ κ * E * d := dvd_mul_left d (κ * E)
    have := dvd_sub h4 h2
    simpa using this
  refine ((hΛ.finite hN).biUnion (t := fun ζ =>
    (fun τ : SL(2, ℤ) => act τ ζ) '' {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ})
    (fun ζ hζ => (coset_finite hE hd hd0 hd2 hdH hq hT hQ (hΛ.1 hζ)).image _)).subset ?_
  rintro g ⟨hgQ, ζ, hζ, τ, hτ, rfl⟩
  exact Set.mem_biUnion hζ ⟨τ, ⟨hτ, hgQ⟩, rfl⟩

end SymMat

end Triples
