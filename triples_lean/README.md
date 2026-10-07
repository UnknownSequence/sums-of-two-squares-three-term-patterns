# Lean formalization of *Sums of two squares in three-term patterns*

This folder is a Lean 4 / Mathlib project that formalizes the paper in `../triples_final`
(`triples_final.pdf`). It contains:

* **an assumptions file** (`TriplesFinal/Assumptions/Assumptions.lean`), stating as named
  propositions the published results that the paper uses (Siegel, Pólya–Vinogradov, the prime
  number theorem in progressions, facts about `K`-Bessel functions, and the spectral theory of
  `Γ₀(q)`, including the large sieve inequalities of Deshouillers–Iwaniec and Pascadi and the
  Kim–Sarnak bound);
* **one file per lemma** of the paper (some lemmas are split over several files), with the
  statement written out in Lean;
* **full proofs of the elementary parts**: Jacobi's two-square formula `r(n) = 4 ∑_{k ∣ n} χ₄(k)`
  (not in Mathlib; proved here from scratch), §2 (the families), §3 (the 2-adic analysis), §4
  (good primes, Proposition 4.2 and the deduction of Theorems 1.1 and 1.3 from Theorem 4.3), the
  hyperbola identity (Lemma 5.1), the root counts (Lemma 5.2) and the character `ψ`
  (Lemma 5.3(a)) of §5, all of Lemma 5.3 (the singular series: the factorization
  `χ f = χ ∗ ψ ∗ β`, the bound for `A_f(t)` via the hyperbola method and Pólya–Vinogradov, the
  convergence of `𝔏_d`, the product formula `𝔏_d = L(1, χ) L(1, ψ) 𝒫_d` with
  `L(1, χ₄) = π/4` and `𝒫_d ≥ (6/π²) φ(dm)/(dm)`, and `𝔏_d ≫ d^(-ε)` from Siegel's theorem),
  Lemma 7.2 (the main term, via smoothed partial sums of `𝔏_d` and the integral of the
  cutoff), Lemma 7.3 (the error term, from Theorem 6.1: a smooth dyadic partition of unity,
  the separation of the variables `k` and `ℓ` by Fourier inversion, and hypothesis (H) for the
  resulting weights), the proof of Theorem 4.3 from Proposition 7.1, §8
  (Heegner points and Lemmas 8.1–8.4), Lemma 9.1 (Poisson summation, via Mathlib's Poisson
  summation formula and `𝓕(f^(k)) = (2πiξ)^k 𝓕f`), Lemma 9.2 (the `Γ₀(q)`-invariance of the
  Poincaré series and the Heegner–Poincaré identities (9.2), (9.3)), reduction theory for `Q_N`,
  the spectral expansion of `Ξ_M` (Lemma 10.1), Pascadi's inequality with smooth weights
  (Lemma 10.5, by Fourier inversion), partial summation (Lemma 10.6), the Heegner side
  (Lemma 10.7: the radial formula for the Selberg transform, areas of hyperbolic discs, the
  `SL₂(ℝ)`-invariance of the measure on `ℍ` and the proper discontinuity of `Γ₀(q)`), the tail
  of the Bessel integral (Lemma 11.1), the Mellin–Barnes formula (Lemma 11.2, by Mellin
  inversion and a contour shift, with a Phragmén–Lindelöf bound for `Γ` in a strip), the Mellin
  transforms `M_h(w)` (Lemma 11.3), the optimisation over `M` (Lemma 12.1), and the whole proof
  of Theorem 6.1 (§12: the spectral side for the discrete and the continuous spectrum, the bound
  (12.2) for `Ξ_M` and the sum over `M`);
* **no `sorry`**: every lemma of the paper is proved, from the assumptions listed in
  `ASSUMPTIONS.md` (see `STATUS.md` for the lemma-by-lemma account).

The main theorems are stated in `TriplesFinal/Main.lean`:

```lean
theorem Triples.theorem_1_1 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hA : AssumptionsAt θ)
    (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ} (hδ : δ < deltaA θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x

theorem Triples.corollary_1_2 (hA : Assumptions) (a b : ℕ) (ha : 0 < a) (hab : a < b) {δ : ℝ}
    (hδ : δ < 25 / 278) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → c * x ^ (1 / 2 + δ) ≤ S a b x
```

Here `S a b x = #{1 ≤ n ≤ x : n, n + a, n + b are sums of two squares}` (`Basic/Defs.lean`),
`deltaA θ = (1 - 2θ)/(10 - 12θ)`, and `Assumptions = AssumptionsAt (7/64)`.

## How the assumptions are used

Nothing is declared with `axiom`. Each published input is a `def … : Prop`, and the theorems
that need it take it as a hypothesis. For example, Theorem 1.1 assumes `AssumptionsAt θ`, which
bundles

| field | content | used in |
|---|---|---|
| `arith.siegel` | Siegel's theorem | Lemma 5.3(d) |
| `arith.polyaVinogradov` | Pólya–Vinogradov inequality | Lemma 5.3(b),(c) |
| `arith.primesInAP` | PNT in arithmetic progressions (lower bound) | deduction of Thm 1.1 (§4) |
| `bessel.besselMellin` | Mellin transform of `K_{it}` [GR 6.561.16] | Lemma 11.2 |
| `bessel.stirling` | Stirling's bound on `Re s = -3/4` | Lemma 11.2 |
| `selbergConv` | convolution of Selberg transforms [Iw, Thm 1.14] | Lemma 10.7 |
| `spectral` | spectral package for all `Γ₀(q)`: Poincaré expansion [Iw, Thm 7.3], pre-trace formula [Iw, Thm 7.4], [DI, Thms 2 and 5], [Pas, Thm 2], `θ_j ≤ θ`, and the continuity of the Eisenstein data in `r` | Lemmas 10.1–10.7, §12 |

The spectral theory is encoded abstractly: `SpectralData q` is a structure holding an index
set, spectral parameters `t_j`, functions `u_j`, Fourier coefficients `ρ_j(n)` (normalised as in
[Pas, (3.15)]), Eisenstein series and their coefficients, and the volume. The required properties
are separate propositions about such data (`PoincareExpansion`, `PreTrace`, `LargeSieveDI2`,
`LargeSieveDI5`, `LargeSievePascadi`, `ExceptionalBound θ`). `SpectralHypothesis θ` asserts
that for every level `q` such data exist, with the large sieve constants independent of `q`.

A wrongly stated assumption cannot make the library inconsistent; it can only make a theorem
that assumes it vacuous. For this reason the statements were written to match the cited sources
and the normalisations of the paper (§10.1).

## Building

The project uses Lean `v4.34.1` and Mathlib `v4.34.1` (see `lean-toolchain` and
`lakefile.toml`). With `elan` installed:

```
cd triples_lean
lake exe cache get     # downloads the compiled Mathlib (a few minutes)
lake build
```

`lake build` compiles every file, without errors and without `sorry`. To see which axioms a
theorem depends on:

```lean
import TriplesFinal
#print axioms Triples.corollary_1_2
```

This lists only `propext`, `Classical.choice` and `Quot.sound`: the published inputs are
hypotheses of the theorems, not axioms. The file `Report.lean` (`lake env lean Report.lean`)
prints the axioms of the main theorems and of the main lemmas, and checks that no declaration
reachable from them uses `sorry`.

## Layout

```
TriplesFinal/
  Assumptions/  Defs.lean (Bessel K, point-pair invariant, Poincaré series, Selberg transform,
                SpectralData), Assumptions.lean (the assumed results)
  Basic/        Defs (S, r, sums of two squares), Reps (r(4z) = r(z)), RootCount (ϱ_m(n),
                Lemma 5.2(a),(b)), Thue, PrimitiveReps, AllReps, Jacobi (Jacobi's formula),
                DivisorBound
  Families/     Lemmas 2.1, 2.3, 2.4, 2.5, 2.6
  TwoAdic/      Lemma 3.1, Proposition 3.2
  GoodPrimes/   §4: pattern data, good primes, Σ_d(x), Proposition 4.2, bad primes
  Prelim/       §5: the weight W, Lemma 5.1, Lemma 5.2, Lemma 5.3 (SingularSeries: ψ and
                5.3(a); Beta, BetaBound: χf = χ∗ψ∗β; AfBound: 5.3(b); Abel: an Abelian theorem;
                SingularSeriesValue, LdProduct: 5.3(c); LValue, LdLower: 5.3(d))
  TypeI/        §6: hypothesis (H), the sum Ξ, Theorem 6.1
  Asymptotic/   §7: Lemma 7.2 (SmoothSum, CutoffIntegral, MainTerm), Lemma 7.3
                (DyadicPartition, WeightFourier, ErrorSetup, Separation, ErrorHyp, ErrorBound,
                ErrorTerm), Proposition 7.1, Theorem 4.3
  Analysis/     general tools: Leibniz and Faà di Bruno bounds, phase functions
                (DerivBounds); Fourier decay and inversion for smooth bumps (FourierDecay);
                Cauchy–Schwarz and countable unions for set integrals (MeasureTools)
  Heegner/      §8: symmetric matrices, Lemmas 8.1–8.4, equation (8.1), reduction theory
  Poisson/      §9: Lemma 9.1 (FourierBump, Poisson, PoissonTail, PoissonDyadic), Lemma 9.2
                (HeegnerPoincare, Unfolding, HeegnerPoincareIdentity)
  Spectral/     §10: Lemmas 10.1–10.7 (Hyperbolic: integration on ℍ for Lemma 10.7;
                TwistMeasure: Lemma 10.6 for families indexed by a measure space)
  Bessel/       §11: Lemmas 11.1–11.3 (GammaBounds: |Γ(iτ)|² ≤ 7/cosh(πτ), G_τ on Re w = -3/2;
                Continuity: K_ν is continuous; MellinBarnesProof: Lemma 11.2)
  TypeIProof/   §12: Lemma 12.1 (Mopt); the set-up (Setup, Psi, SpecFam: an abstract spectral
                family); the spectrum 𝒥₀ (BJ0, Gfun, BlockJ0, BlockJ0Total, BlockJ0DI); the
                spectrum 𝒥₁ (BJ1, BlockJ1Main, BlockTail, BlockRem); the combination of the blocks
                (Combine, SpectralSide, SpectralSum, Measurability); the discrete spectrum
                (DiscreteFamily, DiscreteSide); the continuous spectrum (ContinuousFamily,
                ContinuousSide); the bound (12.2) for Ξ_M (SizeBounds, BoundJ0, SpectralBound,
                XiMBound, FinalAux, FinalBound); Theorem 6.1 (Theorem61)
  Main/         Deduction.lean (§4: from Theorem 4.3 to Theorems 1.1 and 1.3)
  Main.lean     Theorems 1.1, 1.3, Corollary 1.2
TriplesFinal.lean   imports everything
Report.lean         axioms behind the main theorems (and a check for `sorry`)
STATUS.md           lemma-by-lemma status
ASSUMPTIONS.md      the assumptions (published results taken as hypotheses)
```

## Differences from the paper

* Asymptotic statements `A ≪ B` are written with explicit existential constants, and "for
  `x ≥ x₀`" with an explicit `x₀`. The dependence of the constants (on `a, b, ε, η`, the `C_ν`)
  is reflected in the order of the quantifiers.
* Sums over infinitely many terms with compactly supported weights are written as finite sums
  over explicit ranges (for example `Ξ` in `TypeI/Defs.lean`), or as `finsum` (`Σ_d(x)`). The
  singular series `𝔏_d`, which converges only conditionally, is defined as the limit of its
  partial sums.
* Jacobi's formula is proved without `ℤ[i]`: Thue's lemma gives `r*(m) = 4ϱ₁(m)` for the
  primitive representations, so `r(n)/4 = (ϱ₁ ∗ 𝟙_□)(n)`, and the multiplicative functions
  `ϱ₁ ∗ 𝟙_□` and `χ₄ ∗ 1` agree on prime powers by Lemma 5.2(b).
* Lemma 8.1(a) is proved directly (if `γ ⋄ 𝔤 = 𝔤` with `γ = (p q; r s)`, then
  `𝔞²((p+s)² - 4) + 4Nq² = 0`), instead of via the stabilisers of points of `ℍ`.
* Lemma 8.3 records a coset by normal forms of its bottom row in `ℙ¹(ℤ/4Eℤ)` and `ℙ¹(𝔽_d)`
  instead of using the bijection `ℙ¹(ℤ/qℤ) = ℙ¹(ℤ/4Eℤ) × ℙ¹(𝔽_d)`.
* Lemma 8.4 counts with the divisor bound for `τ(N + 𝔟²)` instead of the bound for `ϱ_N(𝔠)`:
  `𝔴 ↦ (𝔟, 𝔠)` is injective with `𝔠 ∣ N + 𝔟²` and `𝔟² ≪ N`.
* Lemma 5.3 is proved over `ℤ`-valued arithmetic functions, with `β := χf ∗ μχ ∗ μψ`, so
  that `χ f = χ ∗ ψ ∗ β` holds by construction; the values of `β` at prime powers are then
  computed. In (c), instead of analytic continuation to `Re s > 1/2`, both sides of
  `∑ χf(n) n^(-s) = L(s, χ) L(s, ψ) ∑ β(n) n^(-s)` are followed as `s → 1⁺` along the reals,
  using an Abelian theorem (summation by parts and dominated convergence); the same theorem and
  Leibniz's series give `L(1, χ₄) = π/4`. For `ℓ ∣ m` with `χ(ℓ) = -1` the Euler factor bound
  `P_ℓ(1/ℓ) ≥ 1 - 1/ℓ` is proved from `ϱ(ℓ^(i+1)) ≤ ℓ ϱ(ℓ^i)` (alternating series) instead of
  the Haar measure argument. The Pólya–Vinogradov inequality is assumed for all non-principal
  characters (as in [Da, Ch. 23]), so no reduction to the primitive character is needed.
* In Lemma 7.2 the substitution `T = T(t)` is replaced by the linear substitution
  `t = √(x/A) s` (with `T(t) = At² + B`), giving `∫ F(T(t)/x) dt = √(x/A) ∫ F(s² + B/x) ds`, and
  `c_F = ∫ F(s²) ds`; the error from `B/x` comes from the Lipschitz bound for `F`. The estimate
  for `𝔏_d - G(y)` is proved by discrete summation by parts with the weight
  `(1 - W(k/y))/k`, using a Lipschitz bound for `W`.
* In Lemma 7.3 the weight `W` is not removed by Mellin inversion on `Re w = 1`. Instead, with
  `u₀ = log(2^((v-2)/2) K/√x)`, the function `f(v) = W(e^(u₀ + v)) β(v)` (`β` a fixed bump equal
  to `1` on `[0, 2]`) is smooth with compact support, so Fourier inversion gives
  `W(2^((v-2)/2) k/√T(t)) = ∫ 𝓕f(ξ) (k/K)^(2πiξ) (T(t)/x)^(-πiξ) dξ` on the support, with
  `|𝓕f(ξ)| ≪_n (1 + |ξ|)^(-n)` uniformly in `u₀`. This also covers the range `K ≤ k₋` of the
  paper, so no case distinction is needed. The partition of unity is
  `ψ₀(t) = χ(t/√2) - χ(t)` (a telescoping sum), and the derivative bounds of (H) for the
  weights `ψ₀(s) s^(2πiξ)` and `F(Q(s)) Q(s)^(-πiξ)` are proved with the Leibniz and Faà di
  Bruno bounds.
* Lemma 10.5 is stated with a constant that is uniform in the level `q` (it depends only on `η`
  and the large sieve constants), as the proof of Theorem 6.1 requires.
* In Lemma 10.7 the Selberg transform of `k₀` is computed by the radial formula
  `h(t) = ∫ 2 cos(rt) g(r) dr`, `g(r) = ∫ φ₁(w² + sinh²(r/2)) dw` (substituting `x = 2√y w`,
  `y = e^r`), instead of bounding `(Im z)^(1/2+it)` on the support of `k₀(·, i)`; since
  `g(r) = 0` unless `sinh²(r/2) ≤ β₀`, this gives `h(t) ≥ (31/32) ∫ 2g` for real `|t| ≤ T`, and
  `∫ 2g ≥ (64/65) · 2πβ₀` from the area of the disc `u ≤ β₀/2`. The pre-trace formula is stated
  with the sum over `Γ₀(q)/{±1}` (half the sum over matrices), so the proof gives the constant
  `128/π` in place of `256/π`.
* In Lemma 9.2 a coset `Γ_∞ γ` is recorded by the bottom row `±(c, d)` of `γ` (the Poincaré
  series is half the sum over all coprime bottom rows with `q ∣ c`), and a class `Γ_∞ ⋄ 𝔤` by its
  translate with `0 ≤ 𝔟 < 𝔠`. The identity (9.2) is proved for every `g` that vanishes near `0`
  (`heegner_poincare_core`); smoothness is not used, as the paper remarks.
* In §4 the paper bounds the primes with `m_d = 3s²` up to `y` by `O(log y)`. The deduction only
  needs primes in a dyadic range `(y/2, y]`, and the formalization proves the simpler bound
  `O(1)` there (`GoodPrimes/BadPrimes.lean`, `pell_dyadic`).
* The weight `W` of (5.1) and the cutoff `F` of §4 are constructed explicitly from Mathlib's
  smooth transition function.
* Lemma 11.2: Mellin inversion is applied on `Re w = 1/2`, and the contour is moved to
  `Re w = -3/2`. The poles at `w = ±it` are removed by writing
  `G_t(w) y^(-w) = (2/(it)) (P(w)/(w - it) - P(w)/(w + it))` with `P` holomorphic on
  `Re w > -2`, so that `h = (2/(it)) (dslope P (it) - dslope P (-it))` is holomorphic and
  Cauchy's theorem on rectangles applies; the principal parts contribute
  `∫ (1/(1/2 + iu) - 1/(-3/2 + iu)) du = 2π`. The decay of `G_t` on the horizontal sides comes
  from a bound `|Γ(s)| ≪ e^(-π|Im s|/2)` on `-3/4 ≤ Re s ≤ 1/4`, obtained by Phragmén–Lindelöf
  for `Γ(s+1) e^(-iπs/2)/(s+2)` from Stirling's bound on `Re s = -3/4` (the only form of
  Stirling's formula that is assumed).
* In §12 the spectral side is proved once, for an abstract spectral family (a measure space of
  spectral points with the large sieve inequality and the Heegner side bound as hypotheses), and
  applied to the discrete spectrum (counting measure) and to the continuous spectrum
  (`(1/4π) dr` on cusps × ℝ). The constants are tracked explicitly; the proof of Theorem 6.1
  runs with `η' = min(η, 1)/18` and gives the exponent `c = max(9, ⌈4/η'⌉ + 2)` of `Δ`.
  The tail `t > T₁` is handled with Lemma 11.3 at `k = ⌈1/η'⌉ + 3`, so that
  `C_k L^k T₁^(3-k) Q ≤ C_k L³`.
