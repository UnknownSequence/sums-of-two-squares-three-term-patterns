import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Definitions needed to state the assumptions

* the `K`-Bessel function `besselK ν y`, by its integral representation;
* the point-pair invariant `u(z, w)`, Poincaré series, the Bessel transform, the Selberg
  transform, and the convolution of point-pair invariants;
* the structure `SpectralData q` (an abstract spectral package for `Γ₀(q)`).

Paper: §§9–11.
-/

namespace Triples

open Complex MeasureTheory
open scoped UpperHalfPlane

noncomputable section

/-- The `K`-Bessel function, by the integral representation of [Wat, §6.22]
(Lemma 11.1 of the paper): `K_ν(y) = ½ ∫_ℝ exp(-y cosh σ + νσ) dσ` for `y > 0`. -/
def besselK (ν : ℂ) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∫ σ : ℝ, Complex.exp (-((y * Real.cosh σ : ℝ) : ℂ) + ν * σ)

/-- The point-pair invariant `u(z, w) = |z - w|² / (4 Im z Im w)`. -/
def pointPair (z w : ℍ) : ℝ := ‖(z : ℂ) - w‖ ^ 2 / (4 * z.im * w.im)

/-- `Im(γ z) = Im z / |cz + d|²` for `γ` with bottom row `(c, d)`. -/
def imAct (c d : ℤ) (z : ℍ) : ℝ := z.im / ‖(c : ℂ) * z + d‖ ^ 2

/-- `Re(γ z)` for the matrix `γ = (y, -x; c, d)` with `xc + yd = 1` given by Bézout
(well defined modulo `1` as a function of the coset `Γ_∞ γ`). -/
def reAct (c d : ℤ) (z : ℍ) : ℝ :=
  (((Int.gcdB c d : ℂ) * z - Int.gcdA c d) / ((c : ℂ) * z + d)).re

/-- The coprime bottom rows `(c, d)` with `q ∣ c`; each coset of `Γ_∞ \ Γ₀(q)` corresponds to
exactly two of them, `±(c, d)`. -/
def bottomRows (q : ℕ) : Set (ℤ × ℤ) := {cd | Int.gcd cd.1 cd.2 = 1 ∧ (q : ℤ) ∣ cd.1}

/-- The Poincaré series `P_{g,h}(z) = ∑_{γ ∈ Γ_∞ \ Γ₀(q)} g(Im γz) e(h Re γz)` (Lemma 9.2). -/
def poincare (q : ℕ) (g : ℝ → ℂ) (h : ℤ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' cd : bottomRows q,
    g (imAct cd.1.1 cd.1.2 z) * Complex.exp (2 * Real.pi * I * h * reAct cd.1.1 cd.1.2 z)

/-- The Bessel transform `ǧ(t) = ∫_0^∞ g(y) K_{it}(2π|h|y) y^(-3/2) dy` of (10.2). -/
def besselTransform (g : ℝ → ℂ) (h : ℤ) (t : ℂ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ),
    g y * besselK (I * t) (2 * Real.pi * |(h : ℝ)| * y) * (y : ℂ) ^ (-(3 : ℂ) / 2)

/-- The Selberg transform of the point-pair invariant `k(z, w) = φ(u(z, w))`:
`h_k(t) = ∫_ℍ k(i, z) (Im z)^(1/2 + it) dμ(z)` [Iw, Theorem 1.14]. Here `dμ = dx dy / y²` is
the measure `volume` on `ℍ`. -/
def selbergTransform (φ : ℝ → ℝ) (t : ℂ) : ℂ :=
  ∫ z : ℍ, (φ (pointPair z UpperHalfPlane.I) : ℂ) * ((z.im : ℂ) ^ ((1 / 2 : ℂ) + I * t))

/-- The convolution of point-pair invariants: `(k₁ * k₂)(z, w) = ∫_ℍ k₁(z, v) k₂(v, w) dμ(v)`. -/
def pairConv (φ₁ φ₂ : ℝ → ℝ) (z w : ℍ) : ℝ :=
  ∫ v : ℍ, φ₁ (pointPair z v) * φ₂ (pointPair v w)

/-- Abstract spectral data for `Γ₀(q)`: an orthonormal basis `u_j` of Maass cusp forms, with
spectral parameters `t_j ∈ [0, ∞) ∪ i(0, 1/2)` and Fourier coefficients `ρ_j(n)` at the cusp `∞`
in the normalisation `u_j(z) = y^(1/2) ∑_{n ≠ 0} ρ_j(n) K_{it_j}(2π|n|y) e(nx)` of
[Pas, (3.15)]; the Eisenstein series `E_𝔰(z, 1/2 + ir)` at the (finitely many) cusps `𝔰` with
Fourier coefficients `ρ_𝔰(n, r)` at `∞`; and the volume of `Γ₀(q) \ ℍ`.

No property is required here: the properties that the proof uses are the `Prop`s of
`TriplesFinal/Assumptions/Assumptions.lean`. -/
structure SpectralData (q : ℕ) where
  /-- index set of the orthonormal basis of Maass cusp forms -/
  ι : Type
  /-- spectral parameters -/
  t : ι → ℂ
  /-- the Maass cusp forms -/
  u : ι → ℍ → ℂ
  /-- Fourier coefficients at `∞` -/
  ρ : ι → ℤ → ℂ
  /-- index set of the inequivalent cusps -/
  κ : Type
  [fintypeκ : Fintype κ]
  /-- `Eis 𝔰 r z = E_𝔰(z, 1/2 + ir)` -/
  Eis : κ → ℝ → ℍ → ℂ
  /-- `ρEis 𝔰 r n = ρ_𝔰(n, r)` -/
  ρEis : κ → ℝ → ℤ → ℂ
  /-- `vol(Γ₀(q) \ ℍ)` -/
  vol : ℝ
  vol_pos : 0 < vol
  /-- only finitely many spectral parameters in every bounded region -/
  finite_le : ∀ T : ℝ, {j | ‖t j‖ ≤ T}.Finite
  /-- `t_j ∈ [0, ∞) ∪ i(0, 1/2)` -/
  t_mem : ∀ j, ((t j).im = 0 ∧ 0 ≤ (t j).re) ∨ ((t j).re = 0 ∧ 0 < (t j).im ∧ (t j).im < 1 / 2)

attribute [instance] SpectralData.fintypeκ

namespace SpectralData

variable {q : ℕ} (D : SpectralData q)

/-- `j` is exceptional: `t_j = iθ_j` with `θ_j > 0`. -/
def IsExceptional (j : D.ι) : Prop := 0 < (D.t j).im

end SpectralData

end

end Triples
