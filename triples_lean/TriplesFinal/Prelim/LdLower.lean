import TriplesFinal.Prelim.LdProduct
import TriplesFinal.Prelim.LValue

/-!
# Lemma 5.3(d): `𝔏_d ≫_ε d^(-ε)`

From the product formula of Lemma 5.3(c), Siegel's theorem (through `norm_LFunction_one_ge`),
the positivity of `L(1, ψ)` (`LFunction_one_eq_norm`) and `φ(n)/n ≫_ε n^(-ε)`.

Paper: §5.3, proof of Lemma 5.3(d).
-/

namespace Triples

open ZMod Filter Topology

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- **Lemma 5.3(d).** `𝔏_d ≫_ε d^(-ε)`, uniformly in good primes `d`. The implied constant is
ineffective (Siegel's theorem).

Proof: by (c), `𝔏_d = (π/4) L(1, ψ) 𝒫_d`. Here `L(1, ψ) > 0` (`LFunction_one_eq_norm`),
`|L(1, ψ)| ≫ (8m)^(-ε') φ(8m)/(8m)` (Siegel, `norm_LFunction_one_ge`), `φ(n)/n ≫ n^(-ε')`, and
`8m, dm ≤ 16 d³`; take `ε' = ε/9`. -/
theorem Ld_lower (hA : ArithmeticAssumptions) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, P.IsGood d → c * (d : ℝ) ^ (-ε) ≤ P.Ld d := by
  set ε' := ε / 9 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨c₁, hc₁, hL⟩ := norm_LFunction_one_ge hA.siegel hε'pos
  obtain ⟨cφ, hcφ, hφ⟩ := totient_div_ge_rpow hε'pos
  set K : ℝ := Real.pi / 4 * (c₁ * cφ) * (6 / Real.pi ^ 2 * cφ) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K * (16 : ℝ) ^ (-(3 * ε')), by positivity, fun d hd => ?_⟩
  have hd1 : P.d₁ < (d : ℤ) := hd.d₁_lt
  have hmpos : 0 < P.m d := P.m_pos hd1
  have hmb := P.m_bounds hd1
  have hMm : ((P.m d).natAbs : ℤ) = P.m d := Int.natAbs_of_nonneg hmpos.le
  have hM1 : 1 ≤ (P.m d).natAbs := by omega
  have hMle : ((P.m d).natAbs : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
    have : ((P.m d).natAbs : ℤ) ≤ 2 * (d : ℤ) ^ 2 := hMm ▸ hmb.2
    exact_mod_cast this
  have hdge1 : 1 ≤ d := hd.prime.one_lt.le
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdge1
  have : NeZero (8 * (P.m d).natAbs) := ⟨by omega⟩
  obtain ⟨ψ', hψ'v, Pd, hPd, hLd⟩ := P.Ld_product hA.polyaVinogradov hd
  obtain ⟨ψ'', hne, hsq, hψ''v⟩ := hd.psi_character
  have hψeq : ψ' = ψ'' := by
    apply MulChar.ext'
    intro u
    have h1 := hψ'v u.val
    have h2 := hψ''v u.val
    rw [ZMod.natCast_zmod_val] at h1 h2
    rw [h1, h2]
  rw [← hψeq] at hne hsq
  -- `L(1, ψ)` is a positive real number
  rw [LFunction_one_eq_norm hsq hne] at hLd
  have hLd' : P.Ld d = Real.pi / 4 * ‖DirichletCharacter.LFunction ψ' 1‖ * Pd := by
    exact_mod_cast hLd
  -- the sizes
  set X : ℝ := ((8 * (P.m d).natAbs : ℕ) : ℝ) with hX
  set Y : ℝ := ((d * (P.m d).natAbs : ℕ) : ℝ) with hY
  set D : ℝ := 16 * (d : ℝ) ^ 3 with hD
  have hXpos : 0 < X := by rw [hX]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hYpos : 0 < Y := by rw [hY]; exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hd2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 := by
    rw [pow_succ]; nlinarith
  have hXD : X ≤ D := by
    rw [hX, hD]; push_cast; nlinarith
  have hYD : Y ≤ D := by
    rw [hY, hD]; push_cast
    have : (d : ℝ) * ((P.m d).natAbs : ℝ) ≤ (d : ℝ) * (2 * (d : ℝ) ^ 2) := by gcongr
    nlinarith
  have hXe : D ^ (-ε') ≤ X ^ (-ε') := Real.rpow_le_rpow_of_nonpos hXpos hXD (by linarith)
  have hYe : D ^ (-ε') ≤ Y ^ (-ε') := Real.rpow_le_rpow_of_nonpos hYpos hYD (by linarith)
  have hDe : 0 < D ^ (-ε') := Real.rpow_pos_of_pos (by positivity) _
  -- lower bound for `|L(1, ψ)|`
  have hLb : c₁ * cφ * (D ^ (-ε')) ^ 2 ≤ ‖DirichletCharacter.LFunction ψ' 1‖ := by
    have h1 := hL _ ψ' hsq hne
    have h2 := hφ (8 * (P.m d).natAbs) (by omega)
    calc c₁ * cφ * (D ^ (-ε')) ^ 2 = c₁ * D ^ (-ε') * (cφ * D ^ (-ε')) := by ring
      _ ≤ c₁ * X ^ (-ε') * (cφ * X ^ (-ε')) := by gcongr c₁ * ?_ * (cφ * ?_)
      _ ≤ c₁ * X ^ (-ε') * (((8 * (P.m d).natAbs).totient : ℝ) / X) := by gcongr
      _ ≤ _ := h1
  -- lower bound for `𝒫_d`
  have hPb : 6 / Real.pi ^ 2 * cφ * D ^ (-ε') ≤ Pd := by
    have h2 := hφ (d * (P.m d).natAbs) (Nat.mul_pos (by omega) (by omega))
    calc 6 / Real.pi ^ 2 * cφ * D ^ (-ε') ≤ 6 / Real.pi ^ 2 * (cφ * Y ^ (-ε')) := by
          rw [mul_assoc]; gcongr
      _ ≤ 6 / Real.pi ^ 2 * (((d * (P.m d).natAbs).totient : ℝ) / Y) := by gcongr
      _ = 6 / Real.pi ^ 2 * ((d * (P.m d).natAbs).totient : ℝ) / (d * (P.m d).natAbs) := by
          rw [hY]; push_cast; ring
      _ ≤ Pd := hPd
  -- `D^(-3ε') = 16^(-3ε') d^(-ε)`
  have hDpow : (D ^ (-ε')) ^ 3 = (16 : ℝ) ^ (-(3 * ε')) * (d : ℝ) ^ (-ε) := by
    rw [← Real.rpow_mul_natCast (by positivity), hD, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_natCast_mul (by positivity)]
    congr 2
    · push_cast; ring
    · push_cast; rw [hε']; ring
  calc K * (16 : ℝ) ^ (-(3 * ε')) * (d : ℝ) ^ (-ε) = K * (D ^ (-ε')) ^ 3 := by
        rw [hDpow]; ring
    _ = Real.pi / 4 * (c₁ * cφ * (D ^ (-ε')) ^ 2) * (6 / Real.pi ^ 2 * cφ * D ^ (-ε')) := by
        rw [hK]; ring
    _ ≤ Real.pi / 4 * ‖DirichletCharacter.LFunction ψ' 1‖ * Pd := by
        gcongr
    _ = P.Ld d := hLd'.symm

end PatternData

end Triples
