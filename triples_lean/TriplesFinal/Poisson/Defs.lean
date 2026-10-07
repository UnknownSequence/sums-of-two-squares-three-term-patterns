import TriplesFinal.TypeI.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Weyl sums and the Poisson-dual terms `W_h`

* `e(t) = exp(2πit)` and the Fourier transform `ψ̂(ξ) = ∫ ψ(t) e(-ξt) dt`;
* `S(h; μ) = ∑_{ν mod μ, Eν² + H ≡ 0 (μ)} e(hν/μ)`;
* `W_h = ∑_{μ ≡ κd (4d)} ψ₁(μ/K) (X/μ) ψ̂₂(hX/μ) S(h; μ)`;
* `h₀ = (qX)^η K/X`, `Y = N^(1/2)/(EK)` and `L = Δ + 8(qX)^η` (equation (9.1)).

Paper: §1 (notation) and §9.
-/

namespace Triples

/-- `e(t) = exp(2πit)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The Fourier transform `ψ̂(ξ) = ∫_ℝ ψ(t) e(-ξt) dt`. -/
noncomputable def fourier (ψ : ℝ → ℂ) (ξ : ℝ) : ℂ := ∫ t : ℝ, ψ t * eC (-(ξ * t))

/-- The Weyl sum `S(h; μ) = ∑_{ν mod μ, Eν² + H ≡ 0 (mod μ)} e(hν/μ)`. -/
noncomputable def weylSum (E H : ℕ) (h : ℤ) (μ : ℕ) : ℂ :=
  ∑ ν ∈ (Finset.range μ).filter (fun ν : ℕ => (μ : ℤ) ∣ (E : ℤ) * (ν : ℤ) ^ 2 + H),
    eC ((h : ℝ) * ν / μ)

/-- `W_h = W_h(ψ₂) = ∑_{μ ≡ κd (4d)} ψ₁(μ/K) (X/μ) ψ̂₂(hX/μ) S(h; μ)`. -/
noncomputable def Wh (E H d κ : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ) (h : ℤ) : ℂ :=
  ∑ μ ∈ moduli d κ K, ψ₁ ((μ : ℝ) / K) * ((X / μ : ℝ) : ℂ) * fourier ψ₂ ((h : ℝ) * X / μ) *
    weylSum E H h μ

/-- `h₀ = (qX)^η K/X` with `q = 4Ed`. -/
noncomputable def h₀ (E d : ℕ) (X K η : ℝ) : ℝ := (((4 * E * d : ℕ) : ℝ) * X) ^ η * K / X

/-- `Y = N^(1/2)/(EK)` with `N = EH`. -/
noncomputable def Ypar (E H : ℕ) (K : ℝ) : ℝ := Real.sqrt ((E * H : ℕ) : ℝ) / (E * K)

/-- `L = Δ + 8 (qX)^η`. -/
noncomputable def Lpar (E d : ℕ) (Δ X η : ℝ) : ℝ := Δ + 8 * (((4 * E * d : ℕ) : ℝ) * X) ^ η

/-- `ψ⁻(t) = ψ(-t)`. -/
def reflect (ψ : ℝ → ℂ) : ℝ → ℂ := fun t => ψ (-t)

/-- A smooth dyadic partition of unity: `ψ₀ ≥ 0` smooth, supported in `[1, 2]`, with
`∑_{i ∈ ℤ} ψ₀(t/2^(i/2)) = 1` for `t > 0` (proof of Lemma 7.3). -/
structure DyadicPartition where
  /-- the function `ψ₀` -/
  ψ₀ : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) ψ₀
  nonneg : ∀ t, 0 ≤ ψ₀ t
  support : ∀ t, ψ₀ t ≠ 0 → 1 ≤ t ∧ t ≤ 2
  sum_eq_one : ∀ t : ℝ, 0 < t → HasSum (fun i : ℤ => ψ₀ (t / (2 : ℝ) ^ ((i : ℝ) / 2))) 1

/-- `Ξ_M(ψ₂) = ∑_{h ≥ 1} ψ₀(h/M) W_h(ψ₂)` (a finite sum, since `ψ₀(h/M) ≠ 0` forces
`h ≤ 2M`). -/
noncomputable def XiM (ψ₀ : DyadicPartition) (E H d κ : ℕ) (X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ)
    (M : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊2 * M⌋₊, (ψ₀.ψ₀ (h / M) : ℂ) * Wh E H d κ X K ψ₁ ψ₂ h

/-- The dyadic frequencies `𝓜 = {2^(i/2) : i ≥ -2, 2^(i/2) ≤ 2h₀}`. -/
noncomputable def dyadicSet (h₀ : ℝ) : Finset ℝ :=
  ((Finset.range (Nat.ceil (2 * (Real.log (2 * h₀) / Real.log 2) + 5))).image
    (fun i : ℕ => (2 : ℝ) ^ (((i : ℤ) - 2 : ℤ) / (2 : ℝ)))).filter (fun M => M ≤ 2 * h₀)

end Triples
