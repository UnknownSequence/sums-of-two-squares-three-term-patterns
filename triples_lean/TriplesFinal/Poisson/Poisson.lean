import TriplesFinal.Poisson.FourierBump
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lemma 9.1(a),(b): Poisson summation

Assume (H).
(a) `Ξ = ∑_{h ≠ 0} W_h`, and the series converges absolutely.
(b) `S(-h; μ) = S(h; μ)`, and `W_{-h}(ψ₂) = W_h(ψ₂⁻)`.

For (a), split `ℓ` into the residue classes `ν mod μ` with `Eν² + H ≡ 0 (mod μ)`
(`sum_lattice_eq`) and apply Poisson summation to `m ↦ ψ₂((ν + mμ)/X)`
(`Poisson/FourierBump.lean`). The term `h = 0` is `(X/μ) ϱ_{E,H}(μ) ∫ψ₂`, which cancels the
subtracted term in `Ξ`. Absolute convergence holds because `ℂ` is finite-dimensional
(`summable_norm_iff`).

Parts (c) and (d) are in `Poisson/PoissonTail.lean` and `Poisson/PoissonDyadic.lean`.

Paper: §9.1, Lemma 9.1.
-/

namespace Triples

open MeasureTheory Filter
open scoped ContDiff Real

/-- The roots `ν mod μ` of `Eν² + H ≡ 0`. -/
def roots (E H μ : ℕ) : Finset ℕ :=
  (Finset.range μ).filter (fun ν : ℕ => (μ : ℤ) ∣ (E : ℤ) * (ν : ℤ) ^ 2 + H)

theorem weylSum_eq (E H : ℕ) (h : ℤ) (μ : ℕ) :
    weylSum E H h μ = ∑ ν ∈ roots E H μ, eC ((h : ℝ) * ν / μ) := rfl

/-- Splitting `ℓ` into residue classes modulo `μ`:
`∑_{|ℓ| ≤ X, μ ∣ Eℓ² + H} ψ(ℓ/X) = ∑_{ν ∈ roots} ∑_m ψ((ν + mμ)/X)` (for `ψ` supported in
`[-1, 1]`). -/
theorem sum_lattice_eq (E H : ℕ) {μ : ℕ} (hμ : 1 ≤ μ) {X : ℝ} (hX : 0 < X) {ψ : ℝ → ℂ}
    (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) :
    ∑ ℓ ∈ lattice E H μ X, ψ ((ℓ : ℝ) / X) =
      ∑ ν ∈ roots E H μ, ∑' m : ℤ, ψ (((ν : ℝ) + m * μ) / X) := by
  classical
  have hμZ : (0 : ℤ) < μ := by exact_mod_cast hμ
  set g : ℤ → ℕ := fun ℓ => (ℓ % μ).toNat with hgdef
  have hgℓ : ∀ ℓ : ℤ, ((g ℓ : ℕ) : ℤ) = ℓ % μ := fun ℓ =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hμZ.ne')
  -- `μ ∣ Eℓ² + H` depends only on `ℓ mod μ`
  have hroot : ∀ ℓ : ℤ, (μ : ℤ) ∣ (E : ℤ) * ℓ ^ 2 + H ↔
      (μ : ℤ) ∣ (E : ℤ) * ((g ℓ : ℕ) : ℤ) ^ 2 + H := by
    intro ℓ
    rw [hgℓ]
    have hm : ℓ % μ ≡ ℓ [ZMOD μ] := Int.mod_modEq ℓ μ
    have h2 : (E : ℤ) * (ℓ % μ) ^ 2 + H ≡ (E : ℤ) * ℓ ^ 2 + H [ZMOD μ] :=
      ((hm.pow 2).mul_left _).add_right _
    exact (Int.ModEq.dvd_iff h2).symm
  have hg : ∀ ℓ ∈ lattice E H μ X, g ℓ ∈ roots E H μ := by
    intro ℓ hℓ
    simp only [lattice, Finset.mem_filter] at hℓ
    simp only [roots, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, (hroot ℓ).1 hℓ.2⟩
    have := Int.emod_lt_of_pos ℓ hμZ
    rw [← hgℓ] at this
    exact_mod_cast this
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  apply Finset.sum_congr rfl
  intro ν hν
  simp only [roots, Finset.mem_filter, Finset.mem_range] at hν
  symm
  rw [tsum_eq_sum (s := ((lattice E H μ X).filter (fun ℓ => g ℓ = ν)).image (fun ℓ => ℓ / (μ : ℤ)))]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro ℓ hℓ
      simp only [Finset.mem_filter] at hℓ
      congr 1
      have h1 : ((ν : ℕ) : ℤ) = ℓ % μ := by rw [← hℓ.2, hgℓ]
      have h2 : ℓ = ℓ % μ + μ * (ℓ / μ) := (Int.emod_add_mul_ediv ℓ μ).symm
      have h3 : (ℓ : ℝ) = (ν : ℝ) + ((ℓ / μ : ℤ) : ℝ) * μ := by
        have : (ℓ : ℤ) = (ν : ℤ) + (ℓ / μ) * μ := by rw [h1]; linarith
        exact_mod_cast this
      rw [h3]
    · intro ℓ hℓ ℓ' hℓ' he
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hℓ hℓ'
      have h1 : ℓ % μ = ℓ' % μ := by rw [← hgℓ, ← hgℓ, hℓ.2, hℓ'.2]
      rw [← Int.emod_add_mul_ediv ℓ μ, ← Int.emod_add_mul_ediv ℓ' μ, h1]
      simp only at he
      rw [he]
  · intro m hm
    by_contra hne
    apply hm
    obtain ⟨h1, h2⟩ := hs _ hne
    set ℓ : ℤ := ν + m * μ with hℓdef
    have hℓR : (ℓ : ℝ) = (ν : ℝ) + m * μ := by rw [hℓdef]; push_cast; ring
    have hℓX : |(ℓ : ℝ)| ≤ X := by
      rw [hℓR, abs_le]
      rw [le_div_iff₀ hX] at h1
      rw [div_le_iff₀ hX] at h2
      constructor <;> linarith
    have hmod : ℓ % μ = ν := by
      rw [hℓdef, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hν.1)
    have hdiv : ℓ / μ = m := by
      rw [hℓdef, Int.add_mul_ediv_right _ _ hμZ.ne', Int.ediv_eq_zero_of_lt (by positivity)
        (by exact_mod_cast hν.1), zero_add]
    rw [Finset.mem_image]
    refine ⟨ℓ, ?_, hdiv⟩
    simp only [Finset.mem_filter, lattice, Finset.mem_Icc]
    have hgℓν : g ℓ = ν := by
      have := hgℓ ℓ
      rw [hmod] at this
      exact_mod_cast this
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hgℓν⟩
    · have : -ℓ ≤ ⌊X⌋ := Int.le_floor.2 (by push_cast; linarith [(abs_le.1 hℓX).1])
      omega
    · exact Int.le_floor.2 (abs_le.1 hℓX).2
    · rw [hroot ℓ, hgℓν]; exact hν.2

/-- `ψ̂(0) = ∫ ψ`. -/
theorem fourier_at_zero (ψ : ℝ → ℂ) : fourier ψ 0 = ∫ t, ψ t := by
  unfold fourier eC; simp

/-- `S(0; μ) = ϱ_{E,H}(μ)`. -/
theorem weylSum_zero (E H μ : ℕ) : weylSum E H 0 μ = rhoEH E H μ := by
  rw [weylSum_eq]; simp [eC, roots, rhoEH]

/-- Poisson summation for one modulus `μ`:
`∑_{|ℓ| ≤ X, μ ∣ Eℓ² + H} ψ(ℓ/X) = ∑_h (X/μ) ψ̂(hX/μ) S(h; μ)`. -/
theorem hasSum_poisson_mu {E H μ : ℕ} (hμ : 1 ≤ μ) {X : ℝ} (hX : 0 < X) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : ∀ t, ψ t ≠ 0 → -1 ≤ t ∧ t ≤ 1) {B : ℝ}
    (hB : ∀ t, ‖iteratedDeriv 2 ψ t‖ ≤ B) :
    HasSum (fun h : ℤ => ((X / μ : ℝ) : ℂ) * fourier ψ (h * X / μ) * weylSum E H h μ)
      (∑ ℓ ∈ lattice E H μ X, ψ ((ℓ : ℝ) / X)) := by
  have hμR : (0 : ℝ) < μ := by exact_mod_cast hμ
  rw [sum_lattice_eq E H hμ hX hs]
  simp_rw [weylSum_eq, Finset.mul_sum]
  exact hasSum_sum fun ν _ => hasSum_poisson hψ hs hB hμR hX ν

/-- **Lemma 9.1(a).** `Ξ = ∑_{h ≠ 0} W_h`, absolutely convergent. -/
theorem poisson_a {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) :
    Summable (fun h : {h : ℤ // h ≠ 0} => ‖Wh E H d κ X K ψ₁ ψ₂ h‖) ∧
      HasSum (fun h : {h : ℤ // h ≠ 0} => Wh E H d κ X K ψ₁ ψ₂ h) (Xi E H d κ X K ψ₁ ψ₂) := by
  classical
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hX : 0 < X := lt_of_lt_of_le (Real.sqrt_pos.2 (by have := hH.hH; positivity)) hH.hX
  have hmu : ∀ μ ∈ moduli d κ K, HasSum (fun h : {h : ℤ // h ≠ 0} =>
      ψ₁ (μ / K) * (((X / μ : ℝ) : ℂ) * fourier ψ₂ ((h : ℤ) * X / μ) * weylSum E H h μ))
      (ψ₁ (μ / K) * ((∑ ℓ ∈ lattice E H μ X, ψ₂ ((ℓ : ℝ) / X)) -
        (rhoEH E H μ : ℂ) / (μ : ℂ) * (X : ℂ) * ∫ t, ψ₂ t)) := by
    intro μ hμ
    have hμ1 : 1 ≤ μ := by
      simp only [moduli, Finset.mem_filter, Finset.mem_Icc] at hμ; exact hμ.1.1
    have hμ0 : (μ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    apply HasSum.mul_left
    have h0 := hasSum_poisson_mu (E := E) (H := H) hμ1 hX hH.smooth₂ hH.supp₂ (hH.deriv₂ 2)
    have h1 := h0.update 0 0
    have hind : Function.update (fun h : ℤ => ((X / μ : ℝ) : ℂ) * fourier ψ₂ (h * X / μ) *
        weylSum E H h μ) 0 0 = Set.indicator {h : ℤ | h ≠ 0} (fun h : ℤ =>
          ((X / μ : ℝ) : ℂ) * fourier ψ₂ (h * X / μ) * weylSum E H h μ) := by
      ext h
      by_cases hh : h = 0
      · subst hh; simp
      · simp [hh]
    rw [hind] at h1
    have h2 : HasSum (fun h : {h : ℤ // h ≠ 0} => ((X / μ : ℝ) : ℂ) * fourier ψ₂ ((h : ℤ) * X / μ) *
        weylSum E H h μ) (0 - ((X / μ : ℝ) : ℂ) * fourier ψ₂ (((0 : ℤ) : ℝ) * X / μ) *
          weylSum E H 0 μ + ∑ ℓ ∈ lattice E H μ X, ψ₂ ((ℓ : ℝ) / X)) :=
      (hasSum_subtype_iff_indicator (s := {h : ℤ | h ≠ 0})).2 h1
    convert h2 using 1
    simp only [Int.cast_zero, zero_mul, zero_div, fourier_at_zero, weylSum_zero]
    push_cast
    field_simp
    ring
  have hall := hasSum_sum hmu
  have hW : HasSum (fun h : {h : ℤ // h ≠ 0} => Wh E H d κ X K ψ₁ ψ₂ h)
      (Xi E H d κ X K ψ₁ ψ₂) := by
    convert hall using 1
    · ext h
      unfold Wh
      apply Finset.sum_congr rfl
      intro μ _
      ring
    · rfl
  exact ⟨summable_norm_iff.2 hW.summable, hW⟩

/-- `e(n + t) = e(t)` for integers `n`. -/
theorem eC_int_add (n : ℤ) (t : ℝ) : eC (n + t) = eC t := by
  unfold eC
  have : (2 * Real.pi * Complex.I * ((n + t : ℝ) : ℂ)) =
      n * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I * (t : ℂ) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- **Lemma 9.1(b)**, first part: `S(-h; μ) = S(h; μ)` (the map `ν ↦ -ν` permutes the roots). -/
theorem weylSum_neg (E H : ℕ) (h : ℤ) (μ : ℕ) : weylSum E H (-h) μ = weylSum E H h μ := by
  unfold weylSum
  rcases Nat.eq_zero_or_pos μ with rfl | hμ
  · simp
  -- the involution `ν ↦ (μ - ν) % μ`
  have hinv : ∀ ν < μ, (μ - (μ - ν) % μ) % μ = ν := by
    intro ν hν
    rcases Nat.eq_zero_or_pos ν with rfl | hν0
    · simp
    · rw [Nat.mod_eq_of_lt (by omega : μ - ν < μ), Nat.mod_eq_of_lt (by omega : μ - (μ - ν) < μ)]
      omega
  have hroot : ∀ ν < μ, ((μ : ℤ) ∣ (E : ℤ) * (ν : ℤ) ^ 2 + H ↔
      (μ : ℤ) ∣ (E : ℤ) * (((μ - ν) % μ : ℕ) : ℤ) ^ 2 + H) := by
    intro ν hν
    have hm : ((((μ - ν) % μ : ℕ) : ℤ)) ≡ -(ν : ℤ) [ZMOD μ] := by
      rcases Nat.eq_zero_or_pos ν with rfl | hν0
      · simp [Int.ModEq]
      · rw [Nat.mod_eq_of_lt (by omega : μ - ν < μ)]
        apply Int.modEq_iff_dvd.2
        exact ⟨-1, by push_cast [Nat.cast_sub hν.le]; ring⟩
    have h2 : (E : ℤ) * (((μ - ν) % μ : ℕ) : ℤ) ^ 2 + H ≡ (E : ℤ) * (ν : ℤ) ^ 2 + H [ZMOD μ] := by
      have := ((hm.pow 2).mul_left (E : ℤ)).add_right (H : ℤ)
      simpa [neg_sq] using this
    have hd := Int.modEq_iff_dvd.1 h2
    constructor
    · intro hx
      have := dvd_sub hx hd
      convert this using 1; ring
    · intro hx
      have := dvd_add hx hd
      convert this using 1; ring
  apply Finset.sum_nbij' (fun ν => (μ - ν) % μ) (fun ν => (μ - ν) % μ)
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν ⊢
    exact ⟨Nat.mod_lt _ hμ, (hroot ν hν.1).1 hν.2⟩
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν ⊢
    exact ⟨Nat.mod_lt _ hμ, (hroot ν hν.1).1 hν.2⟩
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν
    exact hinv ν hν.1
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν
    exact hinv ν hν.1
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν
    rcases Nat.eq_zero_or_pos ν with rfl | hν0
    · simp
    · rw [Nat.mod_eq_of_lt (by omega : μ - ν < μ)]
      have hμ0 : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ.ne'
      have : ((h : ℝ) * ((μ - ν : ℕ) : ℝ) / μ) = (h : ℤ) + ((-h : ℤ) : ℝ) * (ν : ℝ) / μ := by
        rw [Nat.cast_sub hν.1.le]; push_cast; field_simp; ring
      rw [this, eC_int_add]

/-- The Fourier transform of `ψ⁻` is `ξ ↦ ψ̂(-ξ)`. -/
theorem fourier_reflect (ψ : ℝ → ℂ) (ξ : ℝ) : fourier (reflect ψ) ξ = fourier ψ (-ξ) := by
  unfold fourier reflect
  rw [← MeasureTheory.integral_neg_eq_self (fun t => ψ t * eC (-(-ξ * t))) MeasureTheory.volume]
  congr 1
  ext t
  show ψ (-t) * eC (-(ξ * t)) = ψ (-t) * eC (-(-ξ * -t))
  rw [neg_mul_neg]

/-- **Lemma 9.1(b)**, second part: `W_{-h}(ψ₂) = W_h(ψ₂⁻)`. -/
theorem Wh_neg (E H d κ : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) (h : ℤ) :
    Wh E H d κ X K ψ₁ ψ₂ (-h) = Wh E H d κ X K ψ₁ (reflect ψ₂) h := by
  unfold Wh
  apply Finset.sum_congr rfl
  intro μ _
  rw [weylSum_neg, fourier_reflect]
  congr 3
  push_cast; ring

end Triples
