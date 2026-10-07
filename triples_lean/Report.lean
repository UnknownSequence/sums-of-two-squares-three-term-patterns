import TriplesFinal

/-!
# Report on the main theorems

Run with `lake env lean Report.lean` after `lake build`. It prints the axioms used by the main
theorems and the declarations of the project, reachable from them, whose proofs contain `sorry`.
-/

open Lean Elab Command

/-- The declarations in the namespace `Triples`, reachable from `n`, whose own value or type
uses `sorryAx`. -/
partial def sorryDeps (env : Environment) : List Name → NameSet → NameSet → NameSet
  | [], _, out => out
  | n :: rest, vis, out =>
    if vis.contains n then sorryDeps env rest vis out else
    let vis := vis.insert n
    match env.find? n with
    | some ci =>
      let cs := ci.getUsedConstantsAsSet
      let out := if cs.contains ``sorryAx then out.insert n else out
      let next := cs.toList.filter (fun c => (`Triples).isPrefixOf c)
      sorryDeps env (next ++ rest) vis out
    | none => sorryDeps env rest vis out

elab "#sorry_deps " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let out := sorryDeps env [n] {} {}
  let names := out.toList.map toString |>.toArray.qsort (· < ·)
  logInfo m!"{n} uses sorry through {names.size} declarations: {names}"

#print axioms Triples.corollary_1_2
#print axioms Triples.theorem_1_3
#print axioms Triples.identity
#print axioms Triples.seed_exists
#print axioms Triples.PatternData.reduction
#print axioms Triples.rho_le
#print axioms Triples.PatternData.IsGood.rho_pow
#print axioms Triples.PatternData.IsGood.psi_character
#print axioms Triples.twist_removal
#print axioms Triples.poincare_invariant
#print axioms Triples.besselK_tail
#print axioms Triples.M_optimisation
#print axioms Triples.r_eq_four_mul_sum_chi
#print axioms Triples.SymMat.coset_count
#print axioms Triples.SymMat.pair_count
#print axioms Triples.heegner_poincare
#print axioms Triples.Wh_eq_sum_poincare
#print axioms Triples.poisson_a
#print axioms Triples.poisson_c
#print axioms Triples.poisson_d
#print axioms Triples.SpectralData.smooth_weights
#print axioms Triples.SpectralData.expansion
#print axioms Triples.SymMat.exists_reduced
#print axioms Triples.LFunction_one_eq_norm
#print axioms Triples.norm_LFunction_one_ge
#print axioms Triples.PatternData.Ld_lower
#print axioms Triples.PatternData.Ld_product
#print axioms Triples.PatternData.Ld_tendsto
#print axioms Triples.PatternData.Ld_bound
#print axioms Triples.PatternData.Af_bound
#print axioms Triples.PatternData.betaWeight_sum_le
#print axioms Triples.PatternData.gAF_eq
#print axioms Triples.tsum_abelTerm_chiR
#print axioms Triples.tendsto_tsum_rpow
#print axioms Triples.PatternData.main_term
#print axioms Triples.PatternData.abs_Ld_sub_Gsum_le
#print axioms Triples.Cutoff.integral_quadratic
#print axioms Triples.Gt_bound
#print axioms Triples.PatternData.error_term_a
#print axioms Triples.PatternData.error_term_b
#print axioms Triples.PatternData.abs_Ed_le_of_typeI
#print axioms Triples.PatternData.IsGood.sum_psi0_ek_eq
#print axioms Triples.PatternData.IsGood.Ed_eq_sum_EK
#print axioms Triples.PatternData.IsGood.hypH
#print axioms Triples.dyadicPartition
#print axioms Triples.exists_bound_phaseFn
#print axioms Triples.fourier_inversion_of_compactSupport
#print axioms Triples.WeightFourier.W_exp_eq_integral
#print axioms Triples.Mh_bound
#print axioms Triples.Mh_deriv_bound
#print axioms Triples.SpectralData.heegner_side
#print axioms Triples.Hyperbolic.integral_radial_cosh
#print axioms Triples.Hyperbolic.integral_pointPair_left
#print axioms Triples.Hyperbolic.le_integral_area
#print axioms Triples.Hyperbolic.integral_area_le
#print axioms Triples.Hyperbolic.finite_pointPair_le
#print axioms Triples.twist_removal_measure
#print axioms Triples.Setup.J0_block
#print axioms Triples.Setup.J0_exc
#print axioms Triples.Setup.J0_exc_DI
#print axioms Triples.Setup.J1_main_block
#print axioms Triples.Setup.tail_block
#print axioms Triples.Setup.rem_block
#print axioms Triples.Setup.summable_blocks
#print axioms Triples.Setup.measurable_B_comp
#print axioms Triples.Setup.spectral_side'
#sorry_deps Triples.Setup.spectral_side'
#print axioms Triples.SpectralData.discFam_LS
#print axioms Triples.SpectralData.discFam_HS
#print axioms Triples.SpectralData.discFam_ExcA
#print axioms Triples.norm_Gamma_strip
#print axioms Triples.mellin_barnes
#print axioms Triples.SpectralData.contFam_LS
#print axioms Triples.Setup.continuous_side
#print axioms Triples.Setup.XiM_le
#print axioms Triples.Setup.XiM_bound_a
#print axioms Triples.Setup.XiM_bound_b
#print axioms Triples.typeI_assemble
#print axioms Triples.typeI_a
#print axioms Triples.typeI_b
#print axioms Triples.theorem_1_1
#print axioms Triples.theorem_1_3
#sorry_deps Triples.Setup.discrete_side
#sorry_deps Triples.mellin_barnes
#sorry_deps Triples.typeI_a
#sorry_deps Triples.typeI_b
#sorry_deps Triples.corollary_1_2
#sorry_deps Triples.theorem_1_1
#sorry_deps Triples.theorem_1_3
