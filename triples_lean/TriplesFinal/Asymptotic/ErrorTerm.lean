import TriplesFinal.Asymptotic.ErrorBound

/-!
# Lemma 7.3: the error term

`ℰ_d ≪ x^(1/4+θ/2+ε) d^(3/4-3θ/2)` (with Theorem 6.1(a)), respectively
`ℰ_d ≪ x^(1/4+θ/2+ε) d^(3/4-θ)` (with Theorem 6.1(b)), uniformly for good primes `d ≤ x^(1/4)`
and `x ≥ x₀(a, b, ε)` (here `x₀ = 33⁴`).

Proof. By `abs_Ed_le_of_typeI` (`ErrorBound.lean`), which carries out the dyadic decomposition,
the separation of variables and the application of the Type I estimate, it suffices to bound the
Type I factor `G = (qXH)^η X^(1/2) H^(1/4) (1 + X/(dH^(1/2)))^θ` (resp. with `dK` in place of
`X`) for `1/2 ≤ K ≤ k₊`, and the number `≪ log x ≪ x^(ε/4)` of dyadic `K`. With `η = ε/16`,
`E ≤ 8`, `d²/2^(v+1) ≤ H ≤ d²`, `X² ≤ dx` and `d ≤ x^(1/4)`:
`(qXH)^η ≤ 32^η x^(ε/4)`, `X^(1/2) ≤ (dx)^(1/4)`, `H^(1/4) ≤ d^(1/2)`, and
`1 + X/(dH^(1/2)) ≪ x^(1/2) d^(-3/2)` (resp. `1 + K/H^(1/2) ≪ x^(1/2) d^(-1)`, as `K ≤ 2√x`)
(`ErrorTermBounds.typeI_factor_a`, `typeI_factor_b`).

Paper: §7.3, Lemma 7.3.
-/

namespace Triples

namespace ErrorTermBounds

/-- `X^(1/2) ≤ d^(1/4) x^(1/4)` from `X² ≤ dx`. -/
theorem rpow_half_le {X d x : ℝ} (hX : 0 ≤ X) (hd : 0 ≤ d) (hx : 0 ≤ x) (h : X ^ 2 ≤ d * x) :
    X ^ (1 / 2 : ℝ) ≤ d ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
  have h1 : X ^ (1 / 2 : ℝ) = (X ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
  rw [h1, ← Real.mul_rpow hd hx]
  exact Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- `H^(1/4) ≤ d^(1/2)` from `H ≤ d²`. -/
theorem rpow_quarter_le {H d : ℝ} (hH : 0 ≤ H) (hd : 0 ≤ d) (h : H ≤ d ^ 2) :
    H ^ (1 / 4 : ℝ) ≤ d ^ (1 / 2 : ℝ) := by
  calc H ^ (1 / 4 : ℝ) ≤ (d ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hH h (by norm_num)
    _ = d ^ (1 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hd]; norm_num

/-- `(a y)^θ = a^θ y^θ` and `(x^(1/2) d^(-s))^θ = x^(θ/2) d^(-sθ)`. -/
theorem rpow_triple {a x d s θ : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hd : 0 ≤ d) :
    (a * (x ^ (1 / 2 : ℝ) * d ^ (-s))) ^ θ = a ^ θ * (x ^ (θ / 2) * d ^ (-(s * θ))) := by
  rw [Real.mul_rpow ha (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hx, ← Real.rpow_mul hd]
  congr 3 <;> ring

/-- The bound for the Type I factor with `(1 + X/(dH^(1/2)))^θ`. -/
theorem typeI_factor_a {E X H d x V θ η : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 8) (hX0 : 0 < X)
    (hd1 : 1 ≤ d) (hdx : d ≤ x) (hd3 : d ^ 3 ≤ x) (hX : X ^ 2 ≤ d * x) (hH0 : 0 < H)
    (hHd : H ≤ d ^ 2) (hV : 1 ≤ V) (hHl : d ^ 2 / V ^ 2 ≤ H) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (4 * E * d * X * H) ^ η * X ^ (1 / 2 : ℝ) * H ^ (1 / 4 : ℝ) *
        (1 + X / (d * Real.sqrt H)) ^ θ ≤
      32 ^ η * (1 + V) ^ θ *
        (x ^ (4 * η + 1 / 4 + θ / 2) * d ^ (3 / 4 - 3 * θ / 2)) := by
  have hx1 : 1 ≤ x := le_trans hd1 hdx
  have hx0 : 0 < x := by linarith
  have hd0 : 0 < d := by linarith
  -- `X ≤ x`
  have hXx : X ≤ x := by
    have : X ^ 2 ≤ x ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hX0.le hx0.le two_ne_zero).1 this
  -- (a)
  have ha : (4 * E * d * X * H) ^ η ≤ 32 ^ η * x ^ (4 * η) := by
    have h1 : 4 * E * d * X * H ≤ 32 * x ^ 4 := by
      have hH2 : H ≤ x ^ 2 := hHd.trans (by nlinarith)
      have h2 : E * d ≤ 8 * x := by nlinarith
      have h3 : E * d * X ≤ 8 * x * x := by nlinarith
      have h4 : E * d * X * H ≤ 8 * x * x * x ^ 2 := by
        apply mul_le_mul h3 hH2 hH0.le (by positivity)
      nlinarith
    calc (4 * E * d * X * H) ^ η ≤ (32 * x ^ 4) ^ η :=
          Real.rpow_le_rpow (by positivity) h1 hη
      _ = 32 ^ η * x ^ (4 * η) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]
          norm_num
  -- (b), (c)
  have hb := rpow_half_le hX0.le hd0.le hx0.le hX
  have hc := rpow_quarter_le hH0.le hd0.le hHd
  -- (d)
  have hsqH : d / V ≤ Real.sqrt H := by
    rw [show d / V = Real.sqrt ((d / V) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_pow]; exact hHl
  have hXs : X ≤ d ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hd0.le hx0.le, ← Real.sqrt_eq_rpow]
    rw [show X = Real.sqrt (X ^ 2) by rw [Real.sqrt_sq hX0.le]]
    exact Real.sqrt_le_sqrt hX
  have hd32 : d ^ (1 / 2 : ℝ) / (d * (d / V)) = V * d ^ (-(3 / 2 : ℝ)) := by
    have : d ^ (-(3 / 2 : ℝ)) = d ^ (1 / 2 : ℝ) / d ^ (2 : ℝ) := by
      rw [show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub hd0]
    rw [this, Real.rpow_two]
    field_simp
  have hq : X / (d * Real.sqrt H) ≤ V * (x ^ (1 / 2 : ℝ) * d ^ (-(3 / 2 : ℝ))) := by
    have hpos : 0 < d * (d / V) := by positivity
    calc X / (d * Real.sqrt H) ≤ X / (d * (d / V)) := by
          apply div_le_div_of_nonneg_left hX0.le hpos
          exact mul_le_mul_of_nonneg_left hsqH hd0.le
      _ ≤ d ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) / (d * (d / V)) :=
          div_le_div_of_nonneg_right hXs hpos.le
      _ = V * (x ^ (1 / 2 : ℝ) * d ^ (-(3 / 2 : ℝ))) := by
          rw [mul_comm (d ^ (1 / 2 : ℝ)), mul_div_assoc, hd32]; ring
  have hone : 1 ≤ x ^ (1 / 2 : ℝ) * d ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_neg hd0.le, ← div_eq_mul_inv, one_le_div (by positivity)]
    have h1 : d ^ (3 / 2 : ℝ) = (d ^ 3) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd0.le]; norm_num
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hd3 (by norm_num)
  have hd' : (1 + X / (d * Real.sqrt H)) ^ θ ≤
      (1 + V) ^ θ * (x ^ (θ / 2) * d ^ (-(3 / 2 * θ))) := by
    rw [← rpow_triple (by linarith) hx0.le hd0.le]
    apply Real.rpow_le_rpow (by positivity) _ hθ
    nlinarith
  -- combine
  have hx4 : x ^ (4 * η) * (x ^ (1 / 4 : ℝ) * x ^ (θ / 2)) = x ^ (4 * η + 1 / 4 + θ / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have hd4 : d ^ (1 / 4 : ℝ) * d ^ (1 / 2 : ℝ) * d ^ (-(3 / 2 * θ)) =
      d ^ (3 / 4 - 3 * θ / 2) := by
    rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; ring_nf
  calc (4 * E * d * X * H) ^ η * X ^ (1 / 2 : ℝ) * H ^ (1 / 4 : ℝ) *
        (1 + X / (d * Real.sqrt H)) ^ θ
      ≤ (32 ^ η * x ^ (4 * η)) * (d ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) * d ^ (1 / 2 : ℝ) *
          ((1 + V) ^ θ * (x ^ (θ / 2) * d ^ (-(3 / 2 * θ)))) := by
        gcongr
    _ = 32 ^ η * (1 + V) ^ θ * ((x ^ (4 * η) * (x ^ (1 / 4 : ℝ) * x ^ (θ / 2))) *
          (d ^ (1 / 4 : ℝ) * d ^ (1 / 2 : ℝ) * d ^ (-(3 / 2 * θ)))) := by ring
    _ = _ := by rw [hx4, hd4]

/-- The bound for the Type I factor with `(1 + K/(dH^(1/2)))^θ`, `K = dK₀`, `K₀ ≤ 2√x`. -/
theorem typeI_factor_b {E X H d x V θ η K : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ 8) (hX0 : 0 < X)
    (hd1 : 1 ≤ d) (hdx : d ≤ x) (hd2 : d ^ 2 ≤ x) (hX : X ^ 2 ≤ d * x) (hH0 : 0 < H)
    (hHd : H ≤ d ^ 2) (hV : 1 ≤ V) (hHl : d ^ 2 / V ^ 2 ≤ H) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hK0 : 0 ≤ K) (hK : K ≤ 2 * Real.sqrt x) :
    (4 * E * d * X * H) ^ η * X ^ (1 / 2 : ℝ) * H ^ (1 / 4 : ℝ) *
        (1 + d * K / (d * Real.sqrt H)) ^ θ ≤
      32 ^ η * (1 + 2 * V) ^ θ * (x ^ (4 * η + 1 / 4 + θ / 2) * d ^ (3 / 4 - θ)) := by
  have hx1 : 1 ≤ x := le_trans hd1 hdx
  have hx0 : 0 < x := by linarith
  have hd0 : 0 < d := by linarith
  have hXx : X ≤ x := by
    have : X ^ 2 ≤ x ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hX0.le hx0.le two_ne_zero).1 this
  have ha : (4 * E * d * X * H) ^ η ≤ 32 ^ η * x ^ (4 * η) := by
    have h1 : 4 * E * d * X * H ≤ 32 * x ^ 4 := by
      have hH2 : H ≤ x ^ 2 := hHd.trans (by nlinarith)
      have h2 : E * d ≤ 8 * x := by nlinarith
      have h3 : E * d * X ≤ 8 * x * x := by nlinarith
      have h4 : E * d * X * H ≤ 8 * x * x * x ^ 2 := by
        apply mul_le_mul h3 hH2 hH0.le (by positivity)
      nlinarith
    calc (4 * E * d * X * H) ^ η ≤ (32 * x ^ 4) ^ η :=
          Real.rpow_le_rpow (by positivity) h1 hη
      _ = 32 ^ η * x ^ (4 * η) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]
          norm_num
  have hb := rpow_half_le hX0.le hd0.le hx0.le hX
  have hc := rpow_quarter_le hH0.le hd0.le hHd
  have hsqH : d / V ≤ Real.sqrt H := by
    rw [show d / V = Real.sqrt ((d / V) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_pow]; exact hHl
  have hq : d * K / (d * Real.sqrt H) ≤ 2 * V * (x ^ (1 / 2 : ℝ) * d ^ (-(1 : ℝ))) := by
    have hsH : 0 < Real.sqrt H := Real.sqrt_pos.2 hH0
    rw [mul_div_mul_left _ _ hd0.ne']
    calc K / Real.sqrt H ≤ K / (d / V) :=
          div_le_div_of_nonneg_left hK0 (by positivity) hsqH
      _ ≤ 2 * Real.sqrt x / (d / V) := div_le_div_of_nonneg_right hK (by positivity)
      _ = 2 * V * (x ^ (1 / 2 : ℝ) * d ^ (-(1 : ℝ))) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_neg_one]
          field_simp
  have hone : 1 ≤ x ^ (1 / 2 : ℝ) * d ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, one_le_div hd0, ← Real.sqrt_eq_rpow]
    rw [show d = Real.sqrt (d ^ 2) by rw [Real.sqrt_sq hd0.le]]
    exact Real.sqrt_le_sqrt hd2
  have hd' : (1 + d * K / (d * Real.sqrt H)) ^ θ ≤
      (1 + 2 * V) ^ θ * (x ^ (θ / 2) * d ^ (-(1 * θ))) := by
    rw [← rpow_triple (by linarith) hx0.le hd0.le]
    apply Real.rpow_le_rpow (by positivity) _ hθ
    nlinarith
  have hx4 : x ^ (4 * η) * (x ^ (1 / 4 : ℝ) * x ^ (θ / 2)) = x ^ (4 * η + 1 / 4 + θ / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
  have hd4 : d ^ (1 / 4 : ℝ) * d ^ (1 / 2 : ℝ) * d ^ (-(1 * θ)) = d ^ (3 / 4 - θ) := by
    rw [← Real.rpow_add hd0, ← Real.rpow_add hd0]; ring_nf
  calc (4 * E * d * X * H) ^ η * X ^ (1 / 2 : ℝ) * H ^ (1 / 4 : ℝ) *
        (1 + d * K / (d * Real.sqrt H)) ^ θ
      ≤ (32 ^ η * x ^ (4 * η)) * (d ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) * d ^ (1 / 2 : ℝ) *
          ((1 + 2 * V) ^ θ * (x ^ (θ / 2) * d ^ (-(1 * θ)))) := by
        gcongr
    _ = 32 ^ η * (1 + 2 * V) ^ θ * ((x ^ (4 * η) * (x ^ (1 / 4 : ℝ) * x ^ (θ / 2))) *
          (d ^ (1 / 4 : ℝ) * d ^ (1 / 2 : ℝ) * d ^ (-(1 * θ)))) := by ring
    _ = _ := by rw [hx4, hd4]

/-- `#{-1 ≤ i ≤ ⌈log₂ x⌉ + 2} ≤ C(δ) x^δ`. -/
theorem card_dyIdx_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ((PatternData.dyIdx x).card : ℝ) ≤ C * x ^ δ := by
  refine ⟨5 + 1 / (δ * Real.log 2), by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcard : ((PatternData.dyIdx x).card : ℝ) ≤ Real.logb 2 x + 5 := by
    unfold PatternData.dyIdx
    rw [Int.card_Icc]
    have h0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
    have h1 : ⌈Real.logb 2 x⌉ < Real.logb 2 x + 1 := Int.ceil_lt_add_one _
    have h2 : (0 : ℤ) ≤ ⌈Real.logb 2 x⌉ := Int.ceil_nonneg h0
    have h3 : ((⌈Real.logb 2 x⌉ + 2 + 1 - -1).toNat : ℝ) = (⌈Real.logb 2 x⌉ : ℝ) + 4 := by
      rw [show ⌈Real.logb 2 x⌉ + 2 + 1 - -1 = ⌈Real.logb 2 x⌉ + 4 by ring]
      have : (0 : ℤ) ≤ ⌈Real.logb 2 x⌉ + 4 := by omega
      rw [show ((⌈Real.logb 2 x⌉ + 4).toNat : ℝ) = (((⌈Real.logb 2 x⌉ + 4).toNat : ℤ) : ℝ) by
        norm_cast, Int.toNat_of_nonneg this]
      push_cast; ring
    rw [h3]
    linarith
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have hxδ : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have hlogb : Real.logb 2 x ≤ x ^ δ / (δ * Real.log 2) := by
    rw [Real.logb, div_le_div_iff₀ hlog2 (by positivity)]
    calc Real.log x * (δ * Real.log 2) = (Real.log x * δ) * Real.log 2 := by ring
      _ ≤ x ^ δ * Real.log 2 := by
          gcongr
          rwa [le_div_iff₀ hδ] at hlog
  calc ((PatternData.dyIdx x).card : ℝ) ≤ Real.logb 2 x + 5 := hcard
    _ ≤ x ^ δ / (δ * Real.log 2) + 5 * x ^ δ := by linarith
    _ = (5 + 1 / (δ * Real.log 2)) * x ^ δ := by field_simp; ring

end ErrorTermBounds

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- For `x ≥ 33⁴` and `0 ≤ d ≤ x^(1/4)`: `1 ≤ x`, `33d ≤ x`, `d³ ≤ x`, `d ≤ x`, `d² ≤ x`. -/
theorem range_facts {x : ℝ} (hx : 33 ^ 4 ≤ x) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : d ≤ x ^ (1 / 4 : ℝ)) :
    1 ≤ x ∧ 33 * d ≤ x ∧ d ^ 3 ≤ x ∧ d ≤ x ∧ d ^ 2 ≤ x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  set y := x ^ (1 / 4 : ℝ) with hy
  have hy4 : y ^ 4 = x := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hy33 : 33 ≤ y := by
    have h := Real.rpow_le_rpow (by norm_num) hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h33 : ((33 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = 33 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h33] at h
    exact h
  have hy1 : 1 ≤ y := by linarith
  have hdy : d ≤ y := hd
  refine ⟨by nlinarith, ?_, ?_, ?_, ?_⟩
  · rw [← hy4]
    have : 33 ≤ y ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hy1 2]
    nlinarith
  · rw [← hy4]
    calc d ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hd0 hdy 3
      _ ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  · rw [← hy4]
    calc d ≤ y := hdy
      _ = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)
  · rw [← hy4]
    calc d ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hd0 hdy 2
      _ ≤ y ^ 4 := pow_le_pow_right₀ hy1 (by norm_num)

variable {P}

/-- The parameters of the Type I bound for a good prime. -/
theorem IsGood.typeI_params {d : ℕ} (hd : P.IsGood d) {x : ℝ} (hx : 33 * (d : ℝ) ≤ x) :
    0 ≤ (P.Enat : ℝ) ∧ (P.Enat : ℝ) ≤ 8 ∧ 0 < P.Xpar d x ∧ P.Xpar d x ^ 2 ≤ d * x ∧
      0 < (P.Hnat d : ℝ) ∧ (P.Hnat d : ℝ) ≤ (d : ℝ) ^ 2 ∧
      1 ≤ Real.sqrt (2 ^ (P.v + 1)) ∧
      (d : ℝ) ^ 2 / Real.sqrt (2 ^ (P.v + 1)) ^ 2 ≤ (P.Hnat d : ℝ) := by
  obtain ⟨hX0, -, -, -, hXd⟩ := hd.Xpar_spec hx
  obtain ⟨hH1, hH2⟩ := hd.H_bounds
  have hHpos : (0 : ℝ) < P.H d := by exact_mod_cast hd.H_pos
  have h2v : (4 : ℝ) ≤ 2 ^ P.v := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ P.v := pow_le_pow_right₀ (by norm_num) P.hv
  rw [P.Enat_real, hd.Hnat_real]
  refine ⟨P.E_real_pos.le, ?_, hX0, hXd, hHpos, ?_, ?_, ?_⟩
  · rcases P.E_real_eq with h | h <;> linarith
  · calc (P.H d : ℝ) ≤ 2 * (d : ℝ) ^ 2 / 2 ^ P.v := hH2
      _ ≤ 2 * (d : ℝ) ^ 2 / 4 := by gcongr
      _ ≤ (d : ℝ) ^ 2 := by nlinarith [sq_nonneg (d : ℝ)]
  · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
  · rw [Real.sq_sqrt (by positivity)]
    exact hH1

variable (P)

/-- **Lemma 7.3**, with Theorem 6.1(a). -/
theorem error_term_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesis θ) (F : Cutoff) (W : HyperbolaWeight)
    {ε : ℝ} (hε : 0 < ε) (_hε' : ε < 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Ed F W d x| ≤ C * (x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - 3 * θ / 2)) := by
  set η : ℝ := ε / 16 with hηdef
  have hη : 0 < η := by positivity
  set G : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ := fun E H d X _ =>
    (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
      (1 + X / (d * Real.sqrt H)) ^ θ with hG
  have hT : ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ → ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤ C * Δ ^ c * G E H d X K := by
    obtain ⟨c, hc⟩ := typeI_a hθ0 hθ hB hSC hS hη
    refine ⟨c, fun Cν => ?_⟩
    obtain ⟨C, hC⟩ := hc Cν
    exact ⟨C, fun E H d κ Δ X K ψ₁ ψ₂ h =>
      (hC E H d κ Δ X K ψ₁ ψ₂ h).trans (le_of_eq (by simp only [hG]; ring))⟩
  obtain ⟨C₀, hC₀, hmain⟩ := P.abs_Ed_le_of_typeI F W G hT
  obtain ⟨C₂, hC₂, hcard⟩ := ErrorTermBounds.card_dyIdx_le (δ := ε / 4) (by positivity)
  set V : ℝ := Real.sqrt (2 ^ (P.v + 1)) with hV
  set C₁ : ℝ := 32 ^ η * (1 + V) ^ θ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨C₀ * C₂ * C₁, 33 ^ 4, fun x hx d hd hdx => ?_⟩
  obtain ⟨hx1, h33, hd3, hdx', -⟩ := range_facts hx (d.cast_nonneg) hdx
  have hx0 : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  set B : ℝ := C₁ * (x ^ (4 * η + 1 / 4 + θ / 2) * (d : ℝ) ^ (3 / 4 - 3 * θ / 2)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hE0, hE8, hX0, hXd, hH0, hHd, hV1, hHl⟩ := hd.typeI_params h33
  have hGB : ∀ K : ℝ, 1 / 2 ≤ K → K ≤ P.kplus x →
      0 ≤ G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ∧
        G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ≤ B := by
    intro K _ _
    simp only [hG]
    push_cast
    constructor
    · positivity
    · exact ErrorTermBounds.typeI_factor_a hE0 hE8 hX0 hd1 hdx' hd3 hXd hH0 hHd hV1 hHl hθ0
        hη.le
  have h := hmain d hd x h33 hx1 B hB0 hGB
  have hc := hcard x hx1
  have hexp : x ^ (ε / 4) * x ^ (4 * η + 1 / 4 + θ / 2) ≤ x ^ (1 / 4 + θ / 2 + ε) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [hηdef]; linarith
  calc |P.Ed F W d x| ≤ C₀ * ((dyIdx x).card : ℝ) * B := h
    _ ≤ C₀ * (C₂ * x ^ (ε / 4)) * B := by gcongr
    _ = C₀ * C₂ * C₁ * ((x ^ (ε / 4) * x ^ (4 * η + 1 / 4 + θ / 2)) *
          (d : ℝ) ^ (3 / 4 - 3 * θ / 2)) := by rw [hBdef]; ring
    _ ≤ C₀ * C₂ * C₁ * (x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - 3 * θ / 2)) := by
        gcongr

/-- **Lemma 7.3**, with Theorem 6.1(b). -/
theorem error_term_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) (hS : SpectralHypothesisDI θ) (F : Cutoff) (W : HyperbolaWeight)
    {ε : ℝ} (hε : 0 < ε) (_hε' : ε < 1 / 100) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ d : ℕ, P.IsGood d → (d : ℝ) ≤ x ^ (1 / 4 : ℝ) →
      |P.Ed F W d x| ≤ C * (x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - θ)) := by
  set η : ℝ := ε / 16 with hηdef
  have hη : 0 < η := by positivity
  set G : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ := fun E H d X K =>
    (((4 * E * d : ℕ) : ℝ) * X * H) ^ η * X ^ (1 / 2 : ℝ) * (H : ℝ) ^ (1 / 4 : ℝ) *
      (1 + K / (d * Real.sqrt H)) ^ θ with hG
  have hT : ∃ c : ℝ, ∀ Cν : ℕ → ℝ, ∃ C : ℝ, ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ),
      HypH Cν E H d κ Δ X K ψ₁ ψ₂ → ‖Xi E H d κ X K ψ₁ ψ₂‖ ≤ C * Δ ^ c * G E H d X K := by
    obtain ⟨c, hc⟩ := typeI_b hθ0 hθ hB hSC hS hη
    refine ⟨c, fun Cν => ?_⟩
    obtain ⟨C, hC⟩ := hc Cν
    exact ⟨C, fun E H d κ Δ X K ψ₁ ψ₂ h =>
      (hC E H d κ Δ X K ψ₁ ψ₂ h).trans (le_of_eq (by simp only [hG]; ring))⟩
  obtain ⟨C₀, hC₀, hmain⟩ := P.abs_Ed_le_of_typeI F W G hT
  obtain ⟨C₂, hC₂, hcard⟩ := ErrorTermBounds.card_dyIdx_le (δ := ε / 4) (by positivity)
  set V : ℝ := Real.sqrt (2 ^ (P.v + 1)) with hV
  set C₁ : ℝ := 32 ^ η * (1 + 2 * V) ^ θ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨C₀ * C₂ * C₁, 33 ^ 4, fun x hx d hd hdx => ?_⟩
  obtain ⟨hx1, h33, -, hdx', hd2⟩ := range_facts hx (d.cast_nonneg) hdx
  have hx0 : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  set B : ℝ := C₁ * (x ^ (4 * η + 1 / 4 + θ / 2) * (d : ℝ) ^ (3 / 4 - θ)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨hE0, hE8, hX0, hXd, hH0, hHd, hV1, hHl⟩ := hd.typeI_params h33
  have hGB : ∀ K : ℝ, 1 / 2 ≤ K → K ≤ P.kplus x →
      0 ≤ G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ∧
        G P.Enat (P.Hnat d) d (P.Xpar d x) (d * K) ≤ B := by
    intro K hK1 hKk
    have hK0 : 0 ≤ K := by linarith
    have hK2 : K ≤ 2 * Real.sqrt x := hKk.trans (P.kplus_le x)
    simp only [hG]
    push_cast
    constructor
    · positivity
    · exact ErrorTermBounds.typeI_factor_b hE0 hE8 hX0 hd1 hdx' hd2 hXd hH0 hHd hV1 hHl hθ0
        hη.le hK0 hK2
  have h := hmain d hd x h33 hx1 B hB0 hGB
  have hc := hcard x hx1
  have hexp : x ^ (ε / 4) * x ^ (4 * η + 1 / 4 + θ / 2) ≤ x ^ (1 / 4 + θ / 2 + ε) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    rw [hηdef]; linarith
  calc |P.Ed F W d x| ≤ C₀ * ((dyIdx x).card : ℝ) * B := h
    _ ≤ C₀ * (C₂ * x ^ (ε / 4)) * B := by gcongr
    _ = C₀ * C₂ * C₁ * ((x ^ (ε / 4) * x ^ (4 * η + 1 / 4 + θ / 2)) *
          (d : ℝ) ^ (3 / 4 - θ)) := by rw [hBdef]; ring
    _ ≤ C₀ * C₂ * C₁ * (x ^ (1 / 4 + θ / 2 + ε) * (d : ℝ) ^ (3 / 4 - θ)) := by
        gcongr

end PatternData

end Triples
