# Numerical checks for "Rescaled families and sums of two squares in three-term patterns and along n^3+a^3"

These scripts produce the numbers in Section 8 of `rescaled_families.pdf`. Section and lemma numbers
refer to that note; `[IC]` is the final paper *Sums of two squares in three-term patterns* in
`../../triples_final/`. Python 3 with `numpy` and `scipy`, and one C program. `seedsA.py`, `Ld.py` and
`typeI.py` are unchanged copies of the scripts in `../../triples_final/numerics/`, used here as libraries.

| file | what it does | note |
|---|---|---|
| `fam.py` | Library: primality, factorisation (Pollard rho), the classes `D_a`, `H_{r,D}`, good pairs for `n^3+a^3`, roots of `E l^2 + H` modulo `p1 p2`. | §§5–6 |
| `check_identities.py` | Random members of random families: for `n^3+a^3` (odd `a <= 23`) checks Lemma 5.2 (`m = 2 mod 8`), the identity (2.1), and `G_a(m)` in S by factorisation; for eight patterns checks Lemma 6.1, the identities of Lemma 2.2, and `P, P+B` in S. | Lemmas 2.1, 2.2, 5.2, 6.1 |
| `famcount.c` | Sharp sum of `r(T(l))` along one family `T(l) = 2^{s-s_0}(E l^2+H)/(p1 p2)`, over `l` in Z or odd `l`; also counts violations of (F4) and, for patterns, of Lemma 2.2. Compile: `gcc -O2 -o famcount famcount.c -lm`. | §§4–6 |
| `Lfam.py` | The singular series `L = L(1,chi) L(1,psi) P` of Lemma 4.2(c). | Lemma 4.2 |
| `table.py` | Table 2: sharp counts against the main term `64 c_Lambda L sqrt(x/(kappa_0 E L))`. Run `python3 table.py 1e13`. | Table 2 |
| `table_big.py` | The two largest deviations of Table 2 at `x = 1e14`. | §8 |
| `typeI_composite.py` | The Type I sums `Xi` of (3.1) at composite levels `d = p1 p2`, with `E = 1, 4` (cubes) and `E = 8` (pattern {0,1,2}). | Theorem 3.1 |
| `check_remark.py` | Remark 5.1: for `a = 3 (mod 4)`, family members with `4 | l` have `m` with odd part `3 (mod 4)`. | Remark 5.1 |
| `multiplicity.py` | How often one `m` arises from several families (cubes, `a = 1, 3`). | Lemma 2.3 |
| `exponents.py` | Table 1 in exact arithmetic. | Table 1 |

## Results

* `results_identities.txt`: 1800 cube-family members and 800 pattern-family members, no failures.
* `results_table_1e12.txt`, `results_table_1e13.txt`: ratios of sharp counts to main terms between 0.963 and
  1.062 at `x = 1e13`; `results_table_big.txt`: the two largest deviations become 0.995 and 1.016 at
  `x = 1e14`. No violations of (F4) or of Lemma 2.2.
* `results_typeI_composite.txt`: `|Xi| <= 0.0005 X^{1/2} H^{1/4}`; for `K >= 4X`, `|Xi| <= 1.02 M^{1/2}`. Only `K <= 64X`
  was computed; the application in Lemma 4.5 needs `K/X` up to about `sqrt(2L)` (cubes) or `4 sqrt(2L)` (pattern {0,1,2}).
* `results_remark.txt`: 23200 members with `4 | l`, all with odd part of `m` equal to `3 (mod 4)`.
* `results_multiplicity.txt`: `a = 1`: every `m` from exactly one family; `a = 3`: 6 of 38772 values from
  two families.
* `results_exponents.txt`: 25/228, 25/242, 1/8, 1/12, 1/14.

## Running

```
gcc -O2 -o famcount famcount.c -lm
python3 check_identities.py > results_identities.txt      # ~20 s
python3 table.py 1e13 > results_table_1e13.txt            # ~1 min
python3 table_big.py > results_table_big.txt              # ~10 min
python3 typeI_composite.py > results_typeI_composite.txt  # ~15 min
python3 check_remark.py > results_remark.txt
python3 multiplicity.py > results_multiplicity.txt
python3 exponents.py > results_exponents.txt
```

## Provenance

Written by Claude (Anthropic), together with the note.
