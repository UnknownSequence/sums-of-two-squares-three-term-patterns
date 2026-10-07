import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lemma 12.1: the optimisation over the frequency scale `M`

Under (H), with `q = 4Ed`, `N = EH`, `h₀ = (qX)^η K/X`, `V = (qX)^η EK/(M√N)`,
`𝔈_P = (1 + V/max(M, q))^θ` and `𝔈_DI = (1 + V/max(1, q/M))^θ`: for `1/2 ≤ M ≤ 2h₀`,
`X K^(-1/2) ((1 + M/q) M)^(1/2) 𝔈_P ≤ 6 (qX)^η X^(1/2) (1 + X/(d H^(1/2)))^θ` and
`X K^(-1/2) ((1 + M/q) M)^(1/2) 𝔈_DI ≤ 6 (qX)^(2η) X^(1/2) (1 + K/(d H^(1/2)))^θ`.

This is an elementary inequality between real numbers. The proof uses that `θ ↦ (a/b)^θ` is
monotone, so that it suffices to prove the inequalities for `θ = 0` and `θ = 1/2`
(`mul_rpow_le_of_endpoints`); for these exponents they follow from `M ≤ 2h₀`, `K ≤ qX` and
`(1 + M/q)/max(M, q) ≤ 2/q`.

Paper: §12.6, Lemma 12.1.
-/

namespace Triples

/-- If `0 ≤ θ ≤ 1/2`, `T ≤ R` and `T² a ≤ R² b` with `a, b ≥ 1`, then `T a^θ ≤ R b^θ`
(the function `θ ↦ (a/b)^θ` is monotone, so it suffices to check `θ = 0` and `θ = 1/2`). -/
theorem mul_rpow_le_of_endpoints {T R a b θ : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (h0 : T ≤ R) (h1 : T ^ 2 * a ≤ R ^ 2 * b) :
    T * a ^ θ ≤ R * b ^ θ := by
  rcases le_total a b with hab | hab
  · exact mul_le_mul h0 (Real.rpow_le_rpow (by linarith) hab hθ0) (by positivity) hR
  · have hb0 : 0 < b := by linarith
    have hr : 1 ≤ a / b := by rw [le_div_iff₀ hb0]; linarith
    have e : a ^ θ = b ^ θ * (a / b) ^ θ := by
      rw [← Real.mul_rpow hb0.le (by positivity)]
      congr 1
      field_simp
    have h2 : (a / b) ^ θ ≤ Real.sqrt (a / b) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hr hθ
    have h3 : T * Real.sqrt (a / b) ≤ R := by
      rw [← Real.sqrt_sq hT, ← Real.sqrt_mul (sq_nonneg T), ← Real.sqrt_sq hR]
      apply Real.sqrt_le_sqrt
      rw [← mul_div_assoc, div_le_iff₀ hb0]
      exact h1
    calc T * a ^ θ = b ^ θ * (T * (a / b) ^ θ) := by rw [e]; ring
      _ ≤ b ^ θ * (T * Real.sqrt (a / b)) := by gcongr
      _ ≤ b ^ θ * R := by gcongr
      _ = R * b ^ θ := by ring

/-- **Lemma 12.1.** -/
theorem M_optimisation {E H d X K η θ M : ℝ} (hE : 1 ≤ E) (hH : 1 ≤ H) (hd : 1 ≤ d)
    (hX : Real.sqrt (E * H) ≤ X) (hK1 : 1 ≤ K) (hKq : K ≤ 4 * E * d * X) (hη : 0 < η)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hM1 : 1 / 2 ≤ M)
    (hM2 : M ≤ 2 * ((4 * E * d * X) ^ η * K / X)) :
    let q := 4 * E * d
    let V := (q * X) ^ η * E * K / (M * Real.sqrt (E * H))
    X * K ^ (-(1 / 2 : ℝ)) * Real.sqrt ((1 + M / q) * M) * (1 + V / max M q) ^ θ ≤
        6 * (q * X) ^ η * Real.sqrt X * (1 + X / (d * Real.sqrt H)) ^ θ ∧
      X * K ^ (-(1 / 2 : ℝ)) * Real.sqrt ((1 + M / q) * M) * (1 + V / max 1 (q / M)) ^ θ ≤
        6 * (q * X) ^ (2 * η) * Real.sqrt X * (1 + K / (d * Real.sqrt H)) ^ θ := by
  intro q V
  have hq : q = 4 * E * d := rfl
  have hVdef : V = (q * X) ^ η * E * K / (M * Real.sqrt (E * H)) := rfl
  clear_value q V
  rw [← hq] at hM2 hKq
  -- basic facts
  have hEd : 1 ≤ E * d := one_le_mul_of_one_le_of_one_le hE hd
  have hq4 : 4 ≤ q := by rw [hq, mul_assoc]; linarith
  have hqpos : 0 < q := by linarith
  have hEH : 1 ≤ E * H := one_le_mul_of_one_le_of_one_le hE hH
  have hsEH : 1 ≤ Real.sqrt (E * H) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hEH
  have hsEHpos : 0 < Real.sqrt (E * H) := by linarith
  have hX1 : 1 ≤ X := le_trans hsEH hX
  have hXpos : 0 < X := by linarith
  have hKpos : 0 < K := by linarith
  have hMpos : 0 < M := by linarith
  have hdpos : 0 < d := by linarith
  have hEpos : 0 < E := by linarith
  have hqX : 1 ≤ q * X := one_le_mul_of_one_le_of_one_le (by linarith) hX1
  set L := (q * X) ^ η with hL
  have hL1 : 1 ≤ L := Real.one_le_rpow hqX hη.le
  have hLL : L ≤ L ^ 2 := le_self_pow₀ hL1 two_ne_zero
  have hL2 : (q * X) ^ (2 * η) = L ^ 2 := by
    rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hL2]
  clear_value L
  have hM2' : M ≤ 2 * L * K / X := by
    calc M ≤ 2 * (L * K / X) := hM2
      _ = 2 * L * K / X := by ring
  have hKqX : K ≤ q * X := hKq
  have hsH : Real.sqrt H ≤ Real.sqrt (E * H) := Real.sqrt_le_sqrt (by nlinarith)
  have hsHpos : 0 < Real.sqrt H := Real.sqrt_pos.2 (by linarith)
  set A := X / (d * Real.sqrt H) with hA
  set B := K / (d * Real.sqrt H) with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  clear_value A B
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  -- `P = X (1 + M/q) M / K`
  set P := X * ((1 + M / q) * M) / K with hP
  have hP0 : 0 ≤ P := by positivity
  clear_value P
  have hPle : P ≤ 8 * L ^ 2 := by
    rcases le_total M q with h | h
    · have h1 : 1 + M / q ≤ 2 := by
        have : M / q ≤ 1 := (div_le_one hqpos).2 h
        linarith
      calc P ≤ X * (2 * M) / K := by
            rw [hP]; gcongr
        _ ≤ X * (2 * (2 * L * K / X)) / K := by gcongr
        _ = 4 * L := by field_simp; ring
        _ ≤ 8 * L ^ 2 := by linarith
    · have h1 : 1 + M / q ≤ 2 * M / q := by
        rw [le_div_iff₀ hqpos, add_mul, div_mul_cancel₀ _ hqpos.ne']
        linarith
      calc P ≤ X * (2 * M / q * M) / K := by rw [hP]; gcongr
        _ = 2 * X * M ^ 2 / (q * K) := by field_simp
        _ ≤ 2 * X * (2 * L * K / X) ^ 2 / (q * K) := by gcongr
        _ = 8 * L ^ 2 * (K / (q * X)) := by field_simp; try ring
        _ ≤ 8 * L ^ 2 * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; exact hKqX
        _ = 8 * L ^ 2 := by ring
  -- `P V / max(M, q) ≤ L A / 2`
  have hfrac : (1 + M / q) / max M q ≤ 2 / q := by
    rcases le_total M q with h | h
    · rw [max_eq_right h, div_le_div_iff_of_pos_right hqpos]
      have : M / q ≤ 1 := (div_le_one hqpos).2 h
      linarith
    · rw [max_eq_left h, add_div, div_div, one_div]
      have h1 : M⁻¹ ≤ q⁻¹ := inv_anti₀ hqpos h
      have h2 : M / (q * M) = q⁻¹ := by field_simp
      rw [h2]
      have : 2 / q = q⁻¹ + q⁻¹ := by ring
      linarith
  have hPu : P * (V / max M q) ≤ L * A / 2 := by
    have hmax : 0 < max M q := lt_of_lt_of_le hqpos (le_max_right _ _)
    have e : P * (V / max M q) = X * L * E / Real.sqrt (E * H) * ((1 + M / q) / max M q) := by
      rw [hP, hVdef]
      field_simp
    rw [e]
    calc X * L * E / Real.sqrt (E * H) * ((1 + M / q) / max M q)
        ≤ X * L * E / Real.sqrt (E * H) * (2 / q) := by gcongr
      _ = L * (X / (d * Real.sqrt (E * H))) / 2 := by rw [hq]; field_simp; ring
      _ ≤ L * A / 2 := by
          rw [hA]; gcongr
  -- `P V / max(1, q/M) ≤ 2 L³ B`
  have hu2 : V / max 1 (q / M) ≤ L * B / 4 := by
    have hqM : 0 < q / M := by positivity
    calc V / max 1 (q / M) ≤ V / (q / M) :=
          div_le_div_of_nonneg_left hV0 hqM (le_max_right _ _)
      _ = L * K / (4 * d * Real.sqrt (E * H)) := by
          rw [hVdef, hq]; field_simp; try ring
      _ ≤ L * K / (4 * d * Real.sqrt H) := by gcongr
      _ = L * B / 4 := by rw [hB]; field_simp
  -- `T₀`
  set T := X * K ^ (-(1 / 2 : ℝ)) * Real.sqrt ((1 + M / q) * M) with hT
  have hT0 : 0 ≤ T := by positivity
  have hTsq : T ^ 2 = X * P := by
    have hK : K ^ (-(1 / 2 : ℝ)) = (Real.sqrt K)⁻¹ := by
      rw [Real.rpow_neg hKpos.le, Real.sqrt_eq_rpow]
    rw [hT, hK, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hKpos.le,
      Real.sq_sqrt (by positivity), hP]
    field_simp
  clear_value T
  have hsX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hXpos.le
  constructor
  · -- first bound
    have hu : 0 ≤ V / max M q := by positivity
    refine mul_rpow_le_of_endpoints hT0 (by positivity) (by linarith) (by linarith) hθ0 hθ ?_ ?_
    · rw [← pow_le_pow_iff_left₀ hT0 (by positivity) two_ne_zero, hTsq, mul_pow, mul_pow, hsX]
      calc X * P ≤ X * (36 * L ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hXpos.le
        _ = 6 ^ 2 * L ^ 2 * X := by ring
    · rw [hTsq, mul_pow, mul_pow, hsX]
      have h1 : P * (1 + V / max M q) ≤ 36 * L ^ 2 * (1 + A) := by
        calc P * (1 + V / max M q) = P + P * (V / max M q) := by ring
          _ ≤ 8 * L ^ 2 + L * A / 2 := add_le_add hPle hPu
          _ ≤ 36 * L ^ 2 * (1 + A) := by
              have h1 := mul_le_mul_of_nonneg_right hLL hA0
              have h2 : 0 ≤ L * A := by positivity
              have h3 : 0 ≤ L ^ 2 := by positivity
              linarith
      calc X * P * (1 + V / max M q) = X * (P * (1 + V / max M q)) := by ring
        _ ≤ X * (36 * L ^ 2 * (1 + A)) := mul_le_mul_of_nonneg_left h1 hXpos.le
        _ = 6 ^ 2 * L ^ 2 * X * (1 + A) := by ring
  · -- second bound
    have hu : 0 ≤ V / max 1 (q / M) := by positivity
    have hL24 : L ^ 2 ≤ (L ^ 2) ^ 2 := le_self_pow₀ (one_le_pow₀ hL1) two_ne_zero
    refine mul_rpow_le_of_endpoints hT0 (by positivity) (by linarith) (by linarith) hθ0 hθ ?_ ?_
    · rw [← pow_le_pow_iff_left₀ hT0 (by positivity) two_ne_zero, hTsq, mul_pow, mul_pow, hsX]
      calc X * P ≤ X * (36 * (L ^ 2) ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hXpos.le
        _ = 6 ^ 2 * (L ^ 2) ^ 2 * X := by ring
    · rw [hTsq, mul_pow, mul_pow, hsX]
      have h1 : P * (V / max 1 (q / M)) ≤ 8 * L ^ 2 * (L * B / 4) :=
        mul_le_mul hPle hu2 hu (by positivity)
      have hL3 : L ^ 3 ≤ (L ^ 2) ^ 2 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by norm_num)
      have h2 : P * (1 + V / max 1 (q / M)) ≤ 36 * (L ^ 2) ^ 2 * (1 + B) := by
        calc P * (1 + V / max 1 (q / M)) = P + P * (V / max 1 (q / M)) := by ring
          _ ≤ 8 * L ^ 2 + 8 * L ^ 2 * (L * B / 4) := add_le_add hPle h1
          _ = 8 * L ^ 2 + 2 * L ^ 3 * B := by ring
          _ ≤ 36 * (L ^ 2) ^ 2 * (1 + B) := by
              have h1 := mul_le_mul_of_nonneg_right hL3 hB0
              have h2 : 0 ≤ L ^ 3 * B := by positivity
              linarith
      calc X * P * (1 + V / max 1 (q / M)) = X * (P * (1 + V / max 1 (q / M))) := by ring
        _ ≤ X * (36 * (L ^ 2) ^ 2 * (1 + B)) := mul_le_mul_of_nonneg_left h2 hXpos.le
        _ = 6 ^ 2 * (L ^ 2) ^ 2 * X * (1 + B) := by ring

end Triples
