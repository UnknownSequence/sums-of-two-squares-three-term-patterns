# Status of the formalization

Legend:

* **proved**: fully proved in Lean, from the assumptions it lists (there is no `sorry` left in
  the library).
* **assumed**: a published result, stated in `Assumptions/Assumptions.lean` and taken as a
  hypothesis.

Paper numbering refers to `triples_final.pdf`.

## Assumptions (`TriplesFinal/Assumptions/Assumptions.lean`)

| name | content | source |
|---|---|---|
| `SiegelTheorem` | `L(1, χ) ≫_ε q^(-ε)` for primitive real `χ` | [Da, Ch. 21] |
| `PolyaVinogradov` | `∑_{n ≤ y} χ(n) ≪ √q log q` | [Da, Ch. 23] |
| `PrimesInAPLowerBound` | `≫ x / log x` primes `≡ a (mod q)` in `(x/2, x]` | PNT in APs |
| `BesselMellin` | `∫_0^∞ K_{it}(y) y^(w-1) dy = 2^(w-2) Γ((w+it)/2) Γ((w-it)/2)` | [GR, 6.561.16] |
| `StirlingBound` | `Γ(-3/4 + iτ) ≪ (1+|τ|)^(-5/4) e^(-π|τ|/2)` | Stirling |
| `SpectralData.PoincareExpansion` | spectral expansion of Poincaré series, with unfolding | [Iw, Thm 7.3] |
| `SpectralData.PreTrace` | pre-trace formula summed over points | [Iw, Thm 7.4] |
| `SpectralData.LargeSieveDI2` | large sieve for the full spectrum | [DI, Thm 2], [Pas, Lemma H] |
| `SpectralData.LargeSieveDI5` | large sieve for the exceptional spectrum | [DI, Thm 5], [Pas, Thm A] |
| `SpectralData.LargeSievePascadi` | large sieve for exceptional forms with phases | [Pas, Thm 2] |
| `SpectralData.ExceptionalBound θ` | `θ_j ≤ θ` (admissibility; Kim–Sarnak: `θ = 7/64`) | [Kim, App. 2] |
| `SpectralData.EisensteinContinuous` | `r ↦ ρ_𝔰(n, r)` and `r ↦ E_𝔰(z, 1/2 + ir)` are continuous | [Iw, Ch. 6] |
| `SelbergConvolution` | Selberg transform of a convolution is the product | [Iw, Thm 1.14] |

Bundles: `ArithmeticAssumptions`, `BesselAssumptions`, `SpectralHypothesis θ`,
`SpectralHypothesisDI θ`, `AssumptionsAt θ`, `AssumptionsDIAt θ`, and
`Assumptions = AssumptionsAt (7/64)`.

## Lemma by lemma

| paper | Lean file | declaration(s) | status |
|---|---|---|---|
| §1 Theorem 1.1 | `Main.lean` | `theorem_1_1` | proved |
| §1 Corollary 1.2 | `Main.lean` | `corollary_1_2`, `corollary_1_2_selberg`, `corollary_1_2_consecutive` | proved |
| §1 Theorem 1.3 | `Main.lean` | `theorem_1_3` | proved |
| §1 Table 1 (exponents) | `Main.lean` | `deltaA_kim_sarnak`, `deltaB_kim_sarnak`, `delta_selberg`, `delta_selberg_bound` | proved |
| Thue's lemma | `Basic/Thue.lean` | `thue` | proved |
| `r*(m) = 4 ϱ₁(m)` (primitive representations) | `Basic/PrimitiveReps.lean` | `exists_primRep`, `fiber_eq_rot4`, `rootOf_spec`, `card_primReps` | proved |
| `r(n) = ∑_{k² ∣ n} r*(n/k²)` | `Basic/AllReps.lean` | `card_allReps` | proved |
| §1 `r(n) = 4 ∑ χ(k)` (Jacobi) | `Basic/Jacobi.lean` | `rho_one_prime`, `rho_one_two_pow`, `rhoAF_mul_sqAF`, `r_eq_four_mul_sum_chi` | proved |
| `r(n) ≤ 4τ(n)` | `Basic/Jacobi.lean` | `r_le_four_mul_card_divisors` | proved |
| divisor bound `τ(n) ≪ n^ε` | `Basic/DivisorBound.lean` | `card_divisors_le_rpow`, `r_le_rpow` | proved |
| `r(4z) = r(z)` | `Basic/Reps.lean` | `r_four_mul` | proved |
| §2 Lemma 2.1 | `Families/Reduce.lean` | `S_half_le_S` | proved |
| §2 Definition 2.2, Lemma 2.3 | `Families/Choice.lean` | `Admissible`, `choice_spec`, `exists_choice` | proved |
| §2 Lemma 2.4 | `Families/Identity.lean` | `identity` | proved |
| §2 Lemma 2.5 | `Families/Split.lean` | `split` | proved |
| §2 Lemma 2.6 | `Families/Mult.lean` | `mult_bound` | proved |
| §3 Lemma 3.1 | `TwoAdic/NStar.lean` | `nstar_exists` | proved |
| §3 Proposition 3.2 | `TwoAdic/Seed.lean` | `seed_exists`, `seed_T` | proved |
| §4 (4.1), good primes | `GoodPrimes/Data.lean`, `GoodPrimes/Properties.lean` | `PatternData`, `IsGood`, `m_bounds`, `IsGood.not_dvd_H`, `IsGood.N_not_sq`, … | proved |
| §4 (4.2) | `GoodPrimes/Data.lean` | `poly_identity` | proved |
| §4 (4.4), integrality of `T_d(ℓ)` | `GoodPrimes/Sigma.lean` | `Sigma`, `IsGood.T_spec`, `IsGood.dvd_iff`, `IsGood.split` | proved |
| §4 Proposition 4.2 | `GoodPrimes/Reduction.lean`, `Main/Deduction.lean` | `reduction`, `multWeight_bound` | proved |
| §4 bad primes | `GoodPrimes/BadPrimes.lean` | `pell_dyadic`, `sq_sub_sq_finite`, `bad_primes_dyadic` | proved |
| §4 good primes in dyadic ranges | `Main/Deduction.lean` | `good_primes_lower` | proved (uses PNT in APs) |
| §4 Theorem 4.3 | `Asymptotic/SigmaLower.lean` | `sigma_lower_a`, `sigma_lower_b` | proved |
| §4 deduction of Thms 1.1, 1.3 | `Main/Deduction.lean` | `lower_from_sigma`, `exists_odd_reduction`, `lower_general` | proved |
| §4 the cutoff `F` | `Main/Deduction.lean`, `Asymptotic/Setup.lean` | `exists_cutoff`, `Cutoff.cF_pos` | proved |
| §5 (5.1), the weight `W` | `Prelim/Weight.lean` | `HyperbolaWeight`, `exists_hyperbolaWeight` | proved |
| §5 Lemma 5.1 | `Prelim/Hyperbola.lean` | `hyperbola_identity` | proved |
| §5 Lemma 5.2(a) | `Basic/RootCount.lean` | `rho_eq_rhoEH` | proved |
| §5 multiplicativity of `ϱ` | `Basic/RootCount.lean` | `rho_mul` | proved |
| §5 Lemma 5.2(b) | `Basic/RootCount.lean` | `rho_prime`, `rho_succ` (Hensel), `rho_prime_pow_of_not_dvd`, `roots_pm`, `rho_prime_pow_le`, `rho_le` | proved |
| §5 Lemma 5.2(c) | `Prelim/Roots.lean` | `IsGood.legendre_neg_m`, `IsGood.rho_pow` | proved |
| §5 Lemma 5.3(a) | `Prelim/SingularSeries.lean` | `psiChar`, `psiChar_sq`, `exists_jacobiSym_eq_neg_one`, `IsGood.psi_character` | proved |
| §5 `χ f = χ ∗ ψ ∗ β`, values of `β` | `Prelim/Beta.lean` | `gAF_eq`, `IsGood.fAF_eq`, `betaAF_two_pow`, `IsGood.betaAF_d`, `IsGood.betaAF_prime_sq_of_not_dvd`, `IsGood.betaAF_prime_pow_of_dvd`, … | proved |
| §5 `∑ abs(β(n)) n^(-1/2-ε) ≪ d^ε` | `Prelim/BetaBound.lean` | `sum_Icc_le_prod_tsum` (Euler product bound), `betaWeight_sum_le` | proved |
| §5 Lemma 5.3(b) | `Prelim/AfBound.lean` | `sum_Icc_mul_eq`, `abs_sum_hypSet_le` (hyperbola method), `IsGood.abs_sum_psi_le`, `Af_bound` | proved (from `PolyaVinogradov`) |
| §5 Abelian theorem at `s = 1` | `Prelim/Abel.lean` | `sum_range_mul_eq_abel`, `tendsto_sum_div`, `abs_tsum_abelTerm_le`, `tendsto_tsum_rpow` | proved |
| §5 Lemma 5.3(c), convergence and size | `Prelim/SingularSeriesValue.lean` | `IsGood.Ld_eq_and_tendsto`, `Ld_tendsto`, `Ld_bound` | proved (from `PolyaVinogradov`) |
| §5 Lemma 5.3(c), product formula | `Prelim/LdProduct.lean` | `tsum_abelTerm_chiR` (`L(1, χ₄) = π/4`), `IsGood.LSeries_gR`, `IsGood.Ld_eq_product`, `rho_mul_le`, `IsGood.tsum_fP_of_dvd_ge`, `prod_primesBelow_one_sub_inv_sq_ge`, `IsGood.Pd_ge`, `Ld_product` | proved (from `PolyaVinogradov`) |
| §5 real characters at `s = 1` | `Prelim/LValue.lean` | `totient_div_ge_rpow`, `LFunction_one_eq_norm` (`L(1, χ) > 0`), `norm_LFunction_one_ge` (Siegel for imprimitive `χ`) | proved (the last from `SiegelTheorem`) |
| §5 Lemma 5.3(d) | `Prelim/LdLower.lean` | `Ld_lower` | proved (from Siegel and Pólya–Vinogradov) |
| §6 hypothesis (H), (6.1) | `TypeI/Defs.lean` | `HypH`, `Xi` | definitions |
| §6 Theorem 6.1(a),(b) | `TypeI/Theorem.lean`, `TypeIProof/Theorem61.lean` | `typeI_a`, `typeI_b` (`typeI_a_proof`, `typeI_b_proof`) | proved (the proof is §§8–12; see the rows for §12) |
| §7 (7.3) | `Asymptotic/Setup.lean` | `IsGood.Sigma_expand` | proved (from Lemma 5.1) |
| §7 Lemma 7.2, smoothed partial sums | `Asymptotic/SmoothSum.lean` | `HyperbolaWeight.exists_lipschitz`, `Gsum`, `abs_wgt_sub_le`, `abs_Ld_sub_Gsum_le` | proved (from `PolyaVinogradov`) |
| §7 Lemma 7.2, the integral of `F` | `Asymptotic/CutoffIntegral.lean` | `Cutoff.exists_lipschitz`, `Cutoff.cF_eq_J_zero`, `Cutoff.abs_J_sub_cF_le`, `Cutoff.integral_quadratic` | proved |
| §7 Lemma 7.2 | `Asymptotic/MainTerm.lean` | `IsGood.Md_eq`, `IsGood.sum_kRange_eq_Gsum`, `main_term` | proved (from `PolyaVinogradov`) |
| §7 Lemma 7.3, tools | `Analysis/DerivBounds.lean`, `Analysis/FourierDecay.lean` | `norm_iteratedDeriv_mul_le_of_isOpen`, `norm_iteratedDeriv_comp_le_of_isOpen`, `exists_bound_phaseFn`, `one_add_pow_mul_norm_fourier_le`, `fourier_inversion_of_compactSupport` | proved |
| §7 Lemma 7.3, partition of unity | `Asymptotic/DyadicPartition.lean` | `dyadicPartition` | proved |
| §7 Lemma 7.3, the weight `W` | `Asymptotic/WeightFourier.lean` | `W_exp_eq_integral`, `exists_fourier_bound_fW'` | proved |
| §7 Lemma 7.3, set-up | `Asymptotic/ErrorSetup.lean` | `IsGood.Xpar_spec`, `IsGood.Phi_eq_zero_of_kplus_le`, `IsGood.Ed_eq_sum_ek` | proved |
| §7 Lemma 7.3, separation of variables | `Asymptotic/Separation.lean` | `IsGood.psi0_mul_Phi_eq`, `IsGood.sum_psi0_ek_eq`, `sum_moduli_eq` | proved |
| §7 Lemma 7.3, hypothesis (H) | `Asymptotic/ErrorHyp.lean` | `exists_bound_psiOne`, `exists_bound_psiTwo`, `IsGood.hypH` | proved |
| §7 Lemma 7.3, dyadic decomposition | `Asymptotic/ErrorBound.lean` | `IsGood.Ed_eq_sum_EK`, `abs_Ed_le_of_typeI` | proved |
| §7 Lemma 7.3 | `Asymptotic/ErrorTerm.lean` | `error_term_a`, `error_term_b` | proved (from Theorem 6.1) |
| §7 Proposition 7.1 | `Asymptotic/Formula.lean` | `asymptotic_a`, `asymptotic_b` | proved |
| §8 `Q_N`, the action `⋄` | `Heegner/SymMat.lean` | `SymMat`, `act`, `act_mul`, `det_act`, `act_mem_QN` | proved |
| §8 Lemma 8.1(a) | `Heegner/Stabiliser.lean` | `stabiliser`, `stabiliser_SL` | proved |
| §8 Lemma 8.1(b) | `Heegner/Orbits.lean` | `orbit_reps_exists`, `orbit_reps_unique` | proved |
| §8 (8.1), Heegner points | `Heegner/HeegnerPoint.lean` | `zpt`, `zpt_act`, `zpt_injOn` | proved |
| §8 Lemma 8.2(a) | `Heegner/Qkappa.lean`, `Heegner/HeegnerPoint.lean` | `ofPair_bijOn`, `zpt_ofPair` | proved |
| §8 Lemma 8.2(b) | `Heegner/Qkappa.lean` | `Qkappa_invariant` | proved |
| §8 Lemma 8.3 | `Heegner/Cosets.lean` | `eq_of_dvd_cross`, `p1Two_cross`, `p1Prime_cross`, `card_p1Zeros`, `coset_count` | proved |
| §8 Lemma 8.4 | `Heegner/Pairs.lean` | `pointPair_smul`, `near_b_sq_le`, `card_bcSet_le_rpow`, `inner_le`, `pair_count` | proved |
| §9 Fourier decay, Poisson summation | `Poisson/FourierBump.lean` | `norm_fourier_le`, `hasSum_poisson` | proved |
| §9 Lemma 9.1(a) | `Poisson/Poisson.lean` | `sum_lattice_eq`, `hasSum_poisson_mu`, `poisson_a` | proved |
| §9 Lemma 9.1(b) | `Poisson/Poisson.lean` | `weylSum_neg`, `Wh_neg`, `fourier_reflect` | proved |
| §9 Lemma 9.1(c) | `Poisson/PoissonTail.lean` | `norm_Wh_le`, `poisson_c` | proved |
| §9 Lemma 9.1(d) | `Poisson/PoissonDyadic.lean` | `dyadic_weight_eq_one`, `card_dyadicSet_le`, `poisson_d` | proved |
| §9 Lemma 9.2, invariance | `Poisson/HeegnerPoincare.lean` | `mobBR_smul`, `brEquiv`, `poincare_invariant` | proved |
| §9 Lemma 9.2, unfolding | `Poisson/Unfolding.lean` | `Ψ_surj`, `Ψ_fiber_eq`, `sum_poincare_eq` | proved |
| §9 Lemma 9.2, (9.2) and (9.3) | `Poisson/HeegnerPoincareIdentity.lean` | `sum_fund_Qkappa`, `heegner_poincare_core`, `heegner_poincare`, `gh_apply`, `Wh_eq_sum_poincare` | proved |
| §8.1 reduction theory | `Heegner/Reduction.lean` | `exists_reduced`, `finite_reduced`, `IsOrbitReps.finite`, `heegnerReps_finite` | proved |
| §10 Lemma 10.1 | `Spectral/Expansion.lean` | `contDiff_gh`, `gh_support`, `SpectralData.expansion` | proved (from `PoincareExpansion`) |
| §10 Lemmas 10.2–10.4 | `Spectral/LargeSieve.lean` | `large_sieve`, `large_sieve_DI` | assumed |
| §10 Lemma 10.5 | `Spectral/Smooth.lean` | `fourier_inversion_weight`, `norm_integral_mul_sq_le`, `exc_phase_sum_le`, `SpectralData.smooth_weights` | proved (uniformly in `q`) |
| §10 Lemma 10.6 | `Spectral/Twist.lean` | `twist_removal` | proved |
| §10 Lemma 10.7, hyperbolic integrals | `Spectral/Hyperbolic.lean` | `integral_radial_cosh` (radial formula for the Selberg transform), `le_integral_area`, `integral_area_le` (areas of discs), `integral_pointPair_left` (`SL₂(ℝ)`-invariance), `finite_pointPair_le` (proper discontinuity) | proved |
| §10 Lemma 10.7 | `Spectral/HeegnerSide.lean` | `bump`, `lower_real`, `lower_imag`, `pairConv_le`, `pointPair_le_of_pairConv_ne_zero`, `SpectralData.heegner_side` | proved (from `PreTrace` and `SelbergConvolution`) |
| §11 Lemma 11.1 | `Bessel/Integral.lean` | `besselK` (definition), `besselK_tail` | proved |
| §11 Lemma 11.2 | `Bessel/MellinBarnes.lean` | `Gt_bound` | proved (from Stirling's bound in `BesselAssumptions`) |
| §11 Lemma 11.2, `Γ` in vertical strips | `Bessel/MellinBarnesProof.lean` | `norm_Gamma_le_Gamma_re`, `norm_Gamma_strip_aux` (Phragmén–Lindelöf), `norm_Gamma_strip`, `norm_Gt_strip`, `norm_Gt_half` | proved (from Stirling's bound) |
| §11 Lemma 11.2 | `Bessel/MellinBarnesProof.lean`, `Bessel/Continuity.lean` | `continuousOn_besselK`, `integral_principal`, `hmb_eq` (the poles at `±it` removed with `dslope`), `integral_hmb_diff` (Cauchy's theorem on rectangles), `mellin_barnes` (Mellin inversion on `Re w = 1/2` and the contour shift to `Re w = -3/2`) | proved (from `BesselAssumptions`) |
| §11 Lemma 11.3 | `Bessel/Mh.lean` | `Mh_bound`, `Mh_deriv_bound` (with `exists_bound_w1`, `exists_bound_gMh`, `integral_parts`) | proved |
| §12 Lemma 12.1 | `TypeIProof/Mopt.lean` | `mul_rpow_le_of_endpoints`, `M_optimisation` | proved |
| §12 set-up, (12.1) | `TypeIProof/Setup.lean` | `Setup` (the parameters `q, Q, Y, L, V, ℓ, T₁`), `XK_le`, `MY_le`, `MY_ge`, `V_ge`, `ℓ_le`, `L_le`, `M_pow_le`, … | proved |
| §12 abstract spectral family | `TypeIProof/SpecFam.lean` | `SpecFam` (a measure space of spectral points), `LS`, `HS`, `ExcA`, `ExcB`, `ExcBound` | definitions and basic lemmas |
| §11–12 `Ψ_h(t)` | `TypeIProof/Psi.lean` | `besselTransform_gh`, `PsiH_J0` (Lemma 11.1 applied), `PsiH_J1` (Lemma 11.2 applied) | proved |
| §12.2 `|B_j|²` on `𝒥₀` | `TypeIProof/BJ0.lean`, `TypeIProof/Gfun.lean` | `normSq_B_le_m0`, `exists_bound_Gfun` (`‖G_σ^(k)‖ ≪ L^k`) | proved |
| §12.2 the block `𝒥₀` | `TypeIProof/BlockJ0.lean`, `BlockJ0Total.lean`, `BlockJ0DI.lean` | `J0_inner`, `J0_block` (Fubini in `(s, σ)`), `J0_exc` (via Lemma 10.5), `J0_exc_DI` (via Lemma 10.3) | proved |
| §12.3 the splitting `B = B⁺ + B⁻ + Bᴿ` | `TypeIProof/BJ1.lean`, `Bessel/GammaBounds.lean` | `B_eq_J1`, `normSq_Bmain_le`, `normSq_Brem_le`, `norm_Gamma_I_mul_sq_le` | proved |
| §12.3 the range `1 < t ≤ T₁` | `TypeIProof/BlockJ1Main.lean`, `Spectral/TwistMeasure.lean` | `twist_removal_measure`, `phiT_deriv`, `LS_partial`, `J1_main_block` | proved |
| §12.3 the range `t > T₁` | `TypeIProof/BlockTail.lean` | `tail_block` | proved |
| §12.4 the remainder | `TypeIProof/BlockRem.lean` | `peetre_two`, `Gt_sq_mul_cosh_le`, `LS_Dsum`, `rem_inner`, `rem_block` (Fubini in `(t, ξ)`) | proved |
| §12 the blocks combined | `TypeIProof/Combine.lean`, `SpectralSide.lean`, `SpectralSum.lean`, `Measurability.lean`, `Analysis/MeasureTools.lean` | `setIntegral_mul_le_tsum`, `normSq_B_le_J1`, `block_sq_bound`, `summable_blocks`, `measurable_B_comp`, `spectral_side'` | proved |
| §12 the discrete spectrum | `TypeIProof/DiscreteFamily.lean`, `TypeIProof/DiscreteSide.lean` | `discFam` (counting measure), `discFam_LS` (from Lemma 10.2), `discFam_HS` (from Lemma 10.7), `discFam_ExcB` (Lemma 10.3), `discFam_ExcA` (Lemma 10.5), `discrete_side` (`∑_j |B_j U_j|` bounded) | proved |
| §12 the continuous spectrum | `TypeIProof/ContinuousFamily.lean`, `TypeIProof/ContinuousSide.lean` | `contFam` (the measure `(1/4π) count × dr` on cusps × ℝ), `contFam_LS`, `contFam_HS`, `contFam_exc` (no exceptional points), `contFam_integral` | proved (uses `EisensteinContinuous`) |
| §12 the size estimates | `TypeIProof/SizeBounds.lean`, `TypeIProof/BoundJ0.lean`, `TypeIProof/SpectralBound.lean` | `W` (`= (1 + M/q) M`), `qM_rpow_le`, `Q4_exp_le`, `boundJ0_le`, `boundA1_le`, `Wtail_le`, `spectral_rhs_le` (the explicit bound reduced to `K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √W √𝒫`) | proved |
| §12 (12.2), the bound for `Ξ_M` | `TypeIProof/XiMBound.lean`, `TypeIProof/FinalAux.lean`, `TypeIProof/FinalBound.lean`, `Heegner/Representatives.lean` | `continuous_side`, `XiM_le`, `exists_reduced_orbitReps`, `exists_cosetReps`, `XiM_le_pair` (with Lemma 8.4), `exc_a` (Lemma 10.5), `exc_b` (Lemma 10.3), `tail_const`, `Kspec_eq` (the constant depends only on `η` and `C₀`), `Mopt_a`, `Mopt_b` (Lemma 12.1), `XiM_bound_a`, `XiM_bound_b` | proved |
| §12.6 the sum over `M`, Theorem 6.1 | `TypeIProof/Theorem61.lean` | `typeI_assemble` (Lemma 9.1(d), `log Q ≤ Q^η'/η'`), `typeI_a_proof`, `typeI_b_proof` (with `η' = min(η, 1)/18`) | proved |

## Summary

`lake build` compiles all files without errors, and no declaration contains `sorry`. Every
lemma of the paper is formalized and proved, from the assumptions of
`Assumptions/Assumptions.lean` (see `ASSUMPTIONS.md`).

**§12 (the proof of Theorem 6.1).** The spectral side is formalized for an abstract spectral
family (`SpecFam`: a measure space of spectral points with the large sieve inequality and the
Heegner side bound as hypotheses). `spectral_side'` bounds `∫ |B(ρ_t, t)| |U|` by an explicit
expression, combining the blocks `‖t‖ ≤ 1` (§12.2), `1 < ‖t‖ ≤ T₁` (§12.3, by the twist removal)
and the dyadic blocks beyond `T₁` (§§12.3–12.4), with Cauchy–Schwarz on each block. It is applied
to the discrete spectrum (`discFam`: the Maass forms with the counting measure) and to the
continuous spectrum (`contFam`: cusps × ℝ with `(1/4π) dr`), whose hypotheses come from
`LargeSieveDI2`, `heegner_side`, `LargeSieveDI5` and Lemma 10.5. `spectral_rhs_le` reduces the
explicit bound to the shape (12.2) of the paper, and `XiM_bound_a`, `XiM_bound_b` combine it with
the pair count (Lemma 8.4) and Lemma 12.1. `typeI_assemble` sums over `M ∈ 𝓜` (Lemma 9.1(d)).

## What the main theorems depend on

`Report.lean` (run with `lake env lean Report.lean`) prints the axioms of the main theorems and
lists the declarations of the project, reachable from them, whose proofs contain `sorry`:

| theorem | axioms | `sorry` reached through |
|---|---|---|
| `Triples.theorem_1_1`, `Triples.corollary_1_2` | `propext`, `Classical.choice`, `Quot.sound` | none |
| `Triples.theorem_1_3` | the same | none |
| `Triples.typeI_a`, `Triples.typeI_b` (Theorem 6.1) | the same | none |
| `Triples.mellin_barnes` (Lemma 11.2) | the same | none |

So the main theorems are proved from the assumptions of `Assumptions/Assumptions.lean` alone,
which enter as hypotheses of the theorems (no `axiom` is declared).
`Report.lean` also checks that the fully proved lemmas, for instance `Triples.identity`
(Lemma 2.4), `Triples.seed_exists` (Proposition 3.2), `Triples.PatternData.reduction`
(Proposition 4.2), `Triples.rho_le` (Lemma 5.2(b)), `IsGood.psi_character` (Lemma 5.3(a)),
`coset_count` (Lemma 8.3), `pair_count` (Lemma 8.4), `poincare_invariant`, `heegner_poincare`
and `Wh_eq_sum_poincare` (Lemma 9.2), `poisson_a`, `poisson_c`, `poisson_d` (Lemma 9.1),
`smooth_weights` (Lemma 10.5), `expansion` (Lemma 10.1), `exists_reduced` (reduction theory),
`twist_removal` (Lemma 10.6), `heegner_side` (Lemma 10.7), `besselK_tail` (Lemma 11.1), `M_optimisation` (Lemma 12.1),
`r_eq_four_mul_sum_chi` (Jacobi's formula), `LFunction_one_eq_norm` (`L(1, χ) > 0` for real
`χ`), `norm_LFunction_one_ge` (Siegel's bound for imprimitive characters, from
`SiegelTheorem`), `tsum_abelTerm_chiR` (`L(1, χ₄) = π/4`) and all parts of Lemma 5.3
(`Af_bound`, `Ld_tendsto`, `Ld_bound`, `Ld_product`, `Ld_lower`), Lemma 7.2 (`main_term`) and
the reduction of Lemma 7.3 to a Type I estimate (`abs_Ed_le_of_typeI`, with the separation of
variables `IsGood.sum_psi0_ek_eq` and hypothesis (H) `IsGood.hypH`), which take the arithmetic
assumptions as hypotheses, depend only on `propext`, `Classical.choice` and `Quot.sound`.
So do `error_term_a` and `error_term_b` (Lemma 7.3), Theorem 6.1 and Lemma 11.2.
