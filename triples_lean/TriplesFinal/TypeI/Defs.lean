import TriplesFinal.Prelim.Roots
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The hypothesis (H) and the Type I sum `Ξ`

**(H)** `E ∈ {4, 8}`; `H ≥ 1` is odd; `d ≥ 3` is a prime with `d ∤ H`; `N = EH` is neither a
square nor three times a square; `q = 4Ed`; `κ ∈ {1, 3}`; `Δ ≥ 1`, `X ≥ N^(1/2)` and
`1 ≤ K ≤ qX`; `ψ₁, ψ₂ : ℝ → ℂ` are smooth, `ψ₁` is supported in `[1, 2]` and `ψ₂` in `[-1, 1]`,
and `‖ψᵢ^(ν)‖_∞ ≤ C_ν Δ^ν` for all `ν ≥ 0`.

Under (H), with `ϱ_{E,H}(μ) = #{ν mod μ : Eν² + H ≡ 0 (mod μ)}`,
`Ξ = ∑_{μ ≡ κd (4d)} ψ₁(μ/K) (∑_{ℓ ∈ ℤ, μ ∣ Eℓ² + H} ψ₂(ℓ/X) - ϱ_{E,H}(μ)/μ · X ∫ψ₂)`
(equation (6.1)). Since `ψ₁` vanishes outside `[1, 2]` and `ψ₂` outside `[-1, 1]`, the sums
run over `1 ≤ μ ≤ 2K` and `|ℓ| ≤ X`; we write them as finite sums over these ranges.

Paper: §6, hypothesis (H) and equation (6.1).
-/

namespace Triples

open scoped ContDiff

/-- The hypothesis **(H)** of §6, with constants `C_ν`. -/
structure HypH (Cν : ℕ → ℝ) (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) : Prop where
  hE : E = 4 ∨ E = 8
  hH : 1 ≤ H
  hHodd : H % 2 = 1
  hd : d.Prime
  hd3 : 3 ≤ d
  hdH : ¬ d ∣ H
  hNsq : ¬ ∃ s : ℕ, E * H = s ^ 2
  hN3 : ¬ ∃ s : ℕ, E * H = 3 * s ^ 2
  hκ : κ = 1 ∨ κ = 3
  hΔ : 1 ≤ Δ
  hX : Real.sqrt ((E * H : ℕ) : ℝ) ≤ X
  hK1 : 1 ≤ K
  hKq : K ≤ (4 * E * d : ℕ) * X
  smooth₁ : ContDiff ℝ ∞ ψ₁
  smooth₂ : ContDiff ℝ ∞ ψ₂
  supp₁ : ∀ t, ψ₁ t ≠ 0 → 1 ≤ t ∧ t ≤ 2
  supp₂ : ∀ t, ψ₂ t ≠ 0 → -1 ≤ t ∧ t ≤ 1
  deriv₁ : ∀ (ν : ℕ) (t : ℝ), ‖iteratedDeriv ν ψ₁ t‖ ≤ Cν ν * Δ ^ ν
  deriv₂ : ∀ (ν : ℕ) (t : ℝ), ‖iteratedDeriv ν ψ₂ t‖ ≤ Cν ν * Δ ^ ν

/-- The moduli `1 ≤ μ ≤ 2K` with `μ ≡ κd (mod 4d)`. -/
noncomputable def moduli (d κ : ℕ) (K : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * K⌋₊).filter (fun μ => μ % (4 * d) = κ * d % (4 * d))

/-- The `ℓ` with `|ℓ| ≤ X` and `μ ∣ Eℓ² + H`. -/
noncomputable def lattice (E H μ : ℕ) (X : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊X⌋) ⌊X⌋).filter (fun ℓ => (μ : ℤ) ∣ (E : ℤ) * ℓ ^ 2 + H)

/-- **The Type I sum** `Ξ = Ξ(ψ₁, ψ₂)` of equation (6.1). -/
noncomputable def Xi (E H d κ : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) : ℂ :=
  ∑ μ ∈ moduli d κ K, ψ₁ ((μ : ℝ) / K) *
    ((∑ ℓ ∈ lattice E H μ X, ψ₂ ((ℓ : ℝ) / X)) -
      (rhoEH E H μ : ℂ) / (μ : ℂ) * (X : ℂ) * ∫ t : ℝ, ψ₂ t)

end Triples
