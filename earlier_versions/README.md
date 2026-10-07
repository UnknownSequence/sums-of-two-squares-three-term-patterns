# Earlier versions

The stages of the project before the final paper ([`../triples_final/`](../triples_final/)), in the order in
which they were written. None of them is needed to read the final paper;
[`../triples_final/README.md`](../triples_final/README.md) says what each one contributed to it.

1. [`1_consecutive_sos/`](1_consecutive_sos/): *Three consecutive sums of two squares: a power saving over the
   square-root bound*. The pattern `{n − 1, n, n + 1}`, through the integers `N = (d + (b² + 1)/d)/2` with
   `d | b² + 1`, by Hooley's method (Gauss's correspondence and Weil's bound). Result: `δ < 1/52`.
2. [`2_general_triples/`](2_general_triples/): *Sums of two squares in three-term patterns: beyond the
   square-root bound*. All patterns `{0, a, b}`, with a 2-adic analysis; still Hooley's method. Result:
   `δ < 1/24`.
3. [`3_triples_II/`](3_triples_II/): *Sums of two squares in three-term patterns, II: automorphic kernels and an
   improved exponent*. Heegner points of discriminant `−4EH_d` on `Γ₀(4Ed)` and Theorem 8.1 of
   Grimmelt–Merikoski (arXiv:2505.00489). Result: `δ < 25/278`, relying on an unrefereed preprint.
4. [`4_GM_Theorem8.1_verification/`](4_GM_Theorem8.1_verification/): *Theorem 8.1 of Grimmelt–Merikoski: a
   verification report*. A line-by-line check of the external input of 3, with numerical tests.
5. [`5_triples_kuznetsov/`](5_triples_kuznetsov/): *Sums of two squares in three-term patterns via the
   Kuznetsov formula*. A second proof of the Type I estimate by the method of Duke–Friedlander–Iwaniec, from
   published inputs only. Results: `δ < 25/278`, and `δ < 25/292` with the Deshouillers–Iwaniec inequalities
   alone.

Each folder holds the `.tex` source, the compiled `.pdf` and a `numerics/` folder with the scripts behind the
numerical checks.
