# Rescaled families and sums of two squares in three-term patterns and along n³ + a³

**Claude (Anthropic).** A follow-up note to the final paper in [`../triples_final/`](../triples_final/), which
it cites as `[IC]`. The family construction it starts from is due to Siddharth Iyer; see
[Provenance](#provenance).

**Status.** Research draft, not refereed. An independent AI referee pass found no errors of substance,
granting the Type I estimate of `[IC, Theorem 6.1]` as stated. **This note has no Lean formalization**; the
Lean project in [`../triples_lean/`](../triples_lean/) covers the final paper only.

## Contents

| file | |
|---|---|
| `rescaled_families.pdf` | the note (14 pages) |
| `rescaled_families.tex` | its LaTeX source (a single file, `amsart`; compile twice with `pdflatex`) |
| `numerics/` | the scripts behind Section 8 and their outputs; see `numerics/README.md` |

## Results

For a fixed integer `a ≥ 1` let `C_a(x)` be the number of `n ≤ x` such that `n³ + a³` is a sum of two squares,
and for fixed integers `0 < a < b` let `S_{a,b}(x)` be the number of `n ≤ x` such that `n`, `n + a` and `n + b`
are all sums of two squares. Let `θ` be an exponent towards Selberg's eigenvalue conjecture for all `Γ₀(q)`.

* **Theorems 1.1 and 1.2.** `C_a(x) ≫ x^{1/2+δ}` and `S_{a,b}(x) ≫ x^{1/2+δ}` for every
  `δ < (1 − 2θ)/(8 − 8θ)`. With the Kim–Sarnak exponent `θ = 7/64` this is every `δ < 25/228 = 0.1096…`, and
  under Selberg's conjecture every `δ < 1/8`.
* **Theorem 1.4.** With only the large sieve inequalities of Deshouillers and Iwaniec, every
  `δ < (1 − 2θ)/(8 − 4θ)`, which is `25/242 = 0.1033…` for `θ = 7/64`.

| `θ` | final paper, Thm 1.1 | this note, Thms 1.1–1.2 | final paper, Thm 1.3 (DI only) | this note, Thm 1.4 (DI only) |
|---|---|---|---|---|
| `1/4` (Selberg) | `1/14` | `1/12` | `1/16` | `1/14` |
| `7/64` (Kim–Sarnak) | `25/278 = 0.0899` | `25/228 = 0.1096` | `25/292 = 0.0856` | `25/242 = 0.1033` |
| `0` (Selberg's conjecture) | `1/10` | `1/8` | `1/10` | `1/8` |

The results of the final paper are for three-term patterns only.

## The idea

The final paper makes two of the three numbers sums of two squares through the identity
`2dQ = u² + d² + B²` and counts the third along a quadratic polynomial of level `d` and discriminant `≍ d²`.
Its Type I estimate loses a factor `H^{1/4}` that depends on the discriminant `H` but not on the level. Inserting
a square factor `r²`, with `r ≡ 1 (mod 4)` prime,

```
2rdQ = u² + d² + r²B²   ⟹   4r²P(P + B) = (rQ − d)² + u²,
```

gives families of level `rd` and discriminant `≍ (r + d)²`, so for `r ≍ d` the discriminant is of the size of
the level instead of its square. For `n³ + a³ = m(m² − 3am + 3a²)` with `m = n + a`, the analogous families come
from

```
rDm = ℓ² + ((D + 3ar)/2)² − 3a²r²   ⟹   (2ℓ)² + (2rm − 3ar − D)² = 4r²(m² − 3am + 3a²).
```

The analytic input is `[IC, Theorem 6.1]`, extended in Section 3 to levels with at most two prime factors and to
`E = 1` (needed because, for `a ≡ 3 (mod 4)`, the variable `ℓ` must be odd). Remark 7.2 shows that
`(1 − 2θ)/(8 − 8θ)` is the limit of rescaled families combined with this Type I estimate.

## Provenance

This note was written by Claude (Anthropic). The family construction of the final paper, that is, making two of
the three numbers sums of two squares through the identity `2dQ = u² + d² + B²` and counting the third along
the resulting quadratic polynomial, is due to Siddharth Iyer (steps 1 and 2 in the
[Provenance](../README.md#provenance) section of the main README); that is his only contribution to this note.
The rescaled families, their analogue for `n³ + a³`, the extension of the Type I estimate, the proofs and the
computations were developed by Claude.
