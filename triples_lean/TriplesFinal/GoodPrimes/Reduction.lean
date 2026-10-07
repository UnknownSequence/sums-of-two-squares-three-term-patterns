import TriplesFinal.GoodPrimes.Sigma

/-!
# Proposition 4.2: from `Σ_d(x)` to `S_{a,b}(x)`

Let `𝒟` be a finite set of good primes, let `F` take values in `[0, 1]` and vanish outside
`[1/2, 1]`, and let `x ≥ 2(b + 1)`. Then
`∑_{d ∈ 𝒟} Σ_d(x) ≤ ∑_{n ∈ 𝒮_{a,b}(x)} r(T) r(P(P + B))`, where `P = n + p₀` and `T = P + A`
(so `{n, n + a, n + b} = {P, P + B, T}`). With the divisor bound this gives
`∑_{d ∈ 𝒟} Σ_d(x) ≪_ε S_{a,b}(x) x^ε` (see `reduction_rpow` in `Main`).

Paper: §4, Proposition 4.2.
-/

namespace Triples

namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- The multiplicity weight `r(T) r(P(P + B))` with `P = n + p₀`, `T = P + A`. -/
noncomputable def multWeight (n : ℤ) : ℕ :=
  r (n + P.p₀ + P.A) * r ((n + P.p₀) * (n + P.p₀ + P.B))

/-- The range of `ℓ` used to write `Σ_d(x)` as a finite sum. -/
noncomputable def ellSet (d : ℕ) (x : ℝ) : Finset ℤ :=
  (Finset.Icc (-((d * ⌈x⌉₊ : ℕ) : ℤ)) ((d * ⌈x⌉₊ : ℕ) : ℤ)).filter
    (fun ℓ => (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d)

variable {P}

/-- `|ℓ| ≤ ℓ² < d T_d(ℓ)`. -/
theorem IsGood.abs_lt {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ} (hℓ : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) :
    |ℓ| < d * P.T d ℓ := by
  obtain ⟨h1, -⟩ := hd.T_spec hℓ
  have hm := P.m_pos hd.d₁_lt
  have hj : 1 ≤ P.j := by have := P.hv; unfold j jOf; omega
  have h4 : (4 : ℤ) ≤ 2 ^ P.j * 2 ^ P.j := by
    have : (2 : ℤ) ≤ 2 ^ P.j := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ P.j := pow_le_pow_right₀ (by norm_num) hj
    nlinarith
  have hsq : |ℓ| ≤ ℓ ^ 2 := by
    rcases eq_or_ne ℓ 0 with rfl | h
    · simp
    · have := Int.one_le_abs h
      nlinarith [abs_mul_abs_self ℓ, sq_abs ℓ]
  have : 4 * ℓ ^ 2 < 4 * (d * P.T d ℓ) := by
    have e : 4 * (d * P.T d ℓ) = (2 ^ P.j * 2 ^ P.j) * ℓ ^ 2 + P.m d := by
      rw [← mul_assoc, h1]; ring
    rw [e]
    nlinarith [sq_nonneg ℓ]
  linarith

/-- `Σ_d(x)` as a finite sum, for weights `F` vanishing on `(1, ∞)`. -/
theorem IsGood.Sigma_eq_sum {d : ℕ} (hd : P.IsGood d) (F : ℝ → ℝ)
    (hF : ∀ t, F t ≠ 0 → t ≤ 1) {x : ℝ} (hx : 0 < x) :
    P.Sigma F d x = ∑ ℓ ∈ P.ellSet d x, (r (P.T d ℓ) : ℝ) * F ((P.T d ℓ : ℝ) / x) := by
  unfold Sigma ellSet
  rw [Finset.sum_filter]
  simp only [finsum_eq_if]
  apply finsum_eq_sum_of_support_subset
  intro ℓ hℓ
  rw [Function.mem_support] at hℓ
  split_ifs at hℓ with hdvd
  · have hF' : F ((P.T d ℓ : ℝ) / x) ≠ 0 := right_ne_zero_of_mul hℓ
    have hTx : (P.T d ℓ : ℝ) ≤ x := by
      have := hF _ hF'
      rwa [div_le_one hx] at this
    have habs := hd.abs_lt hdvd
    have hd0 : (0 : ℤ) ≤ d := by positivity
    have hT : (d : ℝ) * (P.T d ℓ : ℝ) ≤ (d : ℝ) * ⌈x⌉₊ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hTx.trans (Nat.le_ceil x)
    have hT' : (d : ℤ) * P.T d ℓ ≤ ((d * ⌈x⌉₊ : ℕ) : ℤ) := by
      have : ((d : ℤ) * P.T d ℓ : ℝ) ≤ ((d * ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; exact hT
      exact_mod_cast this
    simp only [Finset.coe_Icc, Set.mem_Icc]
    constructor <;> linarith [abs_le.1 (le_of_lt (habs.trans_le hT'))]
  · exact absurd rfl hℓ

/-- If `d ∣ Eℓ² + H_d` and `T_d(ℓ) ≤ x`, then `ℓ` lies in the range of `ellSet d x`. -/
theorem IsGood.mem_ellSet {d : ℕ} (hd : P.IsGood d) {ℓ : ℤ}
    (hdvd : (d : ℤ) ∣ P.E * ℓ ^ 2 + P.H d) {x : ℝ} (hTx : (P.T d ℓ : ℝ) ≤ x) :
    ℓ ∈ P.ellSet d x := by
  unfold ellSet
  rw [Finset.mem_filter]
  refine ⟨?_, hdvd⟩
  have habs := hd.abs_lt hdvd
  have hT : (d : ℝ) * (P.T d ℓ : ℝ) ≤ (d : ℝ) * ⌈x⌉₊ := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hTx.trans (Nat.le_ceil x)
  have hT' : (d : ℤ) * P.T d ℓ ≤ ((d * ⌈x⌉₊ : ℕ) : ℤ) := by
    have : ((d : ℤ) * P.T d ℓ : ℝ) ≤ ((d * ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; exact hT
    exact_mod_cast this
  rw [Finset.mem_Icc]
  constructor <;> linarith [abs_le.1 (le_of_lt (habs.trans_le hT'))]

/-- **Proposition 4.2.** Let `𝒟` be a finite set of good primes, let `0 ≤ F ≤ 1` vanish outside
`[1/2, 1]`, and let `x ≥ 2(b + 1)`. Then
`∑_{d ∈ 𝒟} Σ_d(x) ≤ ∑_{n ∈ 𝒮_{a,b}(x)} r(n + p₀ + A) r((n + p₀)(n + p₀ + B))`. -/
theorem reduction {F : ℝ → ℝ} (_hF0 : ∀ t, 0 ≤ F t) (hF1 : ∀ t, F t ≤ 1)
    (hFs : ∀ t, F t ≠ 0 → 1 / 2 ≤ t ∧ t ≤ 1) (D : Finset ℕ) (hD : ∀ d ∈ D, P.IsGood d)
    {x : ℝ} (hx : 2 * ((b : ℝ) + 1) ≤ x) :
    ∑ d ∈ D, P.Sigma F d x ≤ ∑ n ∈ (SSet_finite a b x).toFinset, (P.multWeight n : ℝ) := by
  classical
  have hx0 : 0 < x := by have : (0 : ℝ) ≤ b := by positivity
                         linarith
  -- write everything as one finite sum over pairs `(d, ℓ)`
  have h1 : ∑ d ∈ D, P.Sigma F d x =
      ∑ p ∈ D.sigma (fun d => P.ellSet d x), (r (P.T p.1 p.2) : ℝ) * F ((P.T p.1 p.2 : ℝ) / x) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hdD
    exact (hD d hdD).Sigma_eq_sum F (fun t ht => (hFs t ht).2) hx0
  rw [h1]
  set g : (Σ _ : ℕ, ℤ) → ℝ := fun p => (r (P.T p.1 p.2) : ℝ) * F ((P.T p.1 p.2 : ℝ) / x) with hg
  set Z := D.sigma (fun d => P.ellSet d x) with hZ
  -- the map `(d, ℓ) ↦ n = T_d(ℓ) - A - p₀`
  set Φ : (Σ _ : ℕ, ℤ) → ℕ := fun p => (P.T p.1 p.2 - P.A - P.p₀).toNat with hΦ
  set SF := (SSet_finite a b x).toFinset with hSF
  -- facts about the pairs with a non-zero term
  have key : ∀ p ∈ Z.filter (fun p => g p ≠ 0),
      Φ p ∈ SF ∧ P.T p.1 p.2 = (Φ p : ℤ) + P.p₀ + P.A ∧ g p ≤ r (P.T p.1 p.2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpZ, hgp⟩ := hp
    rw [hZ, Finset.mem_sigma] at hpZ
    obtain ⟨hdD, hℓ⟩ := hpZ
    have hd := hD p.1 hdD
    have hdvd : (p.1 : ℤ) ∣ P.E * p.2 ^ 2 + P.H p.1 := (Finset.mem_filter.1 hℓ).2
    have hr : (r (P.T p.1 p.2) : ℝ) ≠ 0 := left_ne_zero_of_mul hgp
    have hF' : F ((P.T p.1 p.2 : ℝ) / x) ≠ 0 := right_ne_zero_of_mul hgp
    obtain ⟨hlo, hhi⟩ := hFs _ hF'
    rw [le_div_iff₀ hx0] at hlo
    rw [div_le_one hx0] at hhi
    -- `T ∈ 𝒮` since `r(T) ≠ 0`
    have hTS : IsSumTwoSq (P.T p.1 p.2) := by
      by_contra hns
      apply hr
      have : {q : ℤ × ℤ | q.1 ^ 2 + q.2 ^ 2 = P.T p.1 p.2} = ∅ := by
        ext q
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hq
        exact hns ⟨q.1, q.2, hq.symm⟩
      simp [r, this]
    -- `n = T - A - p₀ ≥ 1` and `{n, n + a, n + b} = {P, P + B, T}`
    set T := P.T p.1 p.2 with hTdef
    set n : ℤ := T - P.A - P.p₀ with hndef
    have htr := P.triple n
    have hTmem : n + P.p₀ + P.A ∈ ({n, n + a, n + b} : Finset ℤ) := by
      rw [← htr]; simp
    have hnmem : n ∈ ({n + P.p₀, n + P.p₀ + P.B, n + P.p₀ + P.A} : Finset ℤ) := by
      rw [htr]; simp
    have hamem : n + a ∈ ({n + P.p₀, n + P.p₀ + P.B, n + P.p₀ + P.A} : Finset ℤ) := by
      rw [htr]; simp
    have hbmem : n + b ∈ ({n + P.p₀, n + P.p₀ + P.B, n + P.p₀ + P.A} : Finset ℤ) := by
      rw [htr]; simp
    have hPmem : n + P.p₀ ∈ ({n, n + a, n + b} : Finset ℤ) := by
      rw [← htr]; simp
    have hnT : n + P.p₀ + P.A = T := by rw [hndef]; ring
    have ha0 : (0 : ℤ) < a := by exact_mod_cast P.ha
    have hab : (a : ℤ) < b := by exact_mod_cast P.hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at hTmem hPmem
    have hTx : (T : ℝ) ≤ x := hhi
    have hTx2 : x / 2 ≤ (T : ℝ) := by linarith
    -- `T - b ≤ n ≤ T`
    have hn1 : 1 ≤ n := by
      have hnb : T ≤ n + b := by
        rcases hTmem with h | h | h <;> rw [hnT] at h <;> omega
      have : (x / 2 : ℝ) ≤ (n : ℝ) + b := by
        have : (T : ℝ) ≤ (n : ℝ) + b := by exact_mod_cast hnb
        linarith
      have : (b : ℝ) + 1 ≤ (n : ℝ) + b := by linarith
      have : (1 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hnT' : n ≤ T := by
      rcases hTmem with h | h | h <;> rw [hnT] at h <;> omega
    -- the three numbers are sums of two squares
    have hPpos : 1 ≤ T - P.A := by
      have hPn : n ≤ n + P.p₀ := by rcases hPmem with h | h | h <;> omega
      have : n + P.p₀ = T - P.A := by rw [hndef]; ring
      omega
    obtain ⟨hP, hPB⟩ := hd.split hdvd hPpos
    have hS : ∀ m ∈ ({n + P.p₀, n + P.p₀ + P.B, n + P.p₀ + P.A} : Finset ℤ), IsSumTwoSq m := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · have : n + P.p₀ = T - P.A := by rw [hndef]; ring
        rw [this]; exact hP
      · have : n + P.p₀ + P.B = T - P.A + P.B := by rw [hndef]; ring
        rw [this]; exact hPB
      · rw [hnT]; exact hTS
    have hΦn : (Φ p : ℤ) = n := by
      simp only [hΦ]; rw [Int.toNat_of_nonneg (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hSF, Set.Finite.mem_toFinset]
      have hnx : (n : ℝ) ≤ x := by
        have : (n : ℝ) ≤ T := by exact_mod_cast hnT'
        linarith
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · omega
      · have : ((Φ p : ℤ) : ℝ) ≤ x := by rw [hΦn]; exact hnx
        exact_mod_cast this
      · rw [hΦn]; exact hS n hnmem
      · rw [hΦn]; exact hS _ hamem
      · rw [hΦn]; exact hS _ hbmem
    · rw [hΦn, hnT]
    · have := hF1 ((T : ℝ) / x)
      have hr0 : (0 : ℝ) ≤ r T := by positivity
      calc g p = (r T : ℝ) * F ((T : ℝ) / x) := rfl
        _ ≤ (r T : ℝ) * 1 := by gcongr
        _ = r T := by ring
  -- reduce to the pairs with a non-zero term and sum over fibres of `Φ`
  rw [← Finset.sum_filter_ne_zero]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := SF) (fun p hp => (key p hp).1)]
  apply Finset.sum_le_sum
  intro n hn
  -- the fibre over `n` injects into `multSet B A T_n`
  set Tn : ℤ := (n : ℤ) + P.p₀ + P.A with hTn
  have hfib : ∀ p ∈ (Z.filter (fun p => g p ≠ 0)).filter (fun p => Φ p = n),
      g p ≤ r Tn ∧ ((p.1 : ℤ), (2 : ℤ) ^ P.j * p.2) ∈ (multSet_finite P.B P.A Tn).toFinset := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp1, hpn⟩ := hp
    obtain ⟨-, hT, hgp⟩ := key p hp1
    rw [hpn] at hT
    refine ⟨by rw [hTn, ← hT]; exact hgp, ?_⟩
    rw [Set.Finite.mem_toFinset]
    rw [Finset.mem_filter, hZ, Finset.mem_sigma] at hp1
    obtain ⟨⟨hdD, hℓ⟩, -⟩ := hp1
    have hd := hD p.1 hdD
    have hdvd : (p.1 : ℤ) ∣ P.E * p.2 ^ 2 + P.H p.1 := (Finset.mem_filter.1 hℓ).2
    obtain ⟨h4, -⟩ := hd.T_spec hdvd
    show (1 : ℤ) ≤ (p.1 : ℤ) ∧
      4 * (p.1 : ℤ) * Tn = ((2 : ℤ) ^ P.j * p.2) ^ 2 + mVal P.B P.A (p.1 : ℤ)
    refine ⟨by exact_mod_cast hd.prime.one_lt.le, ?_⟩
    rw [hTn, ← hT]
    exact h4
  have hinj : Set.InjOn (fun p : (Σ _ : ℕ, ℤ) => ((p.1 : ℤ), (2 : ℤ) ^ P.j * p.2))
      ((Z.filter (fun p => g p ≠ 0)).filter (fun p => Φ p = n) : Set (Σ _ : ℕ, ℤ)) := by
    rintro ⟨d, ℓ⟩ - ⟨d', ℓ'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hd : d = d' := by exact_mod_cast h1
    have hℓ : ℓ = ℓ' := mul_left_cancel₀ (by positivity) h2
    subst hd; subst hℓ; rfl
  have hcard := Finset.card_le_card_of_injOn _ (fun p hp => (hfib p hp).2) hinj
  have hmult : (multSet_finite P.B P.A Tn).toFinset.card ≤ r ((Tn - P.A) * (Tn - P.A + P.B)) := by
    rw [← Set.ncard_eq_toFinset_card _ (multSet_finite P.B P.A Tn)]
    exact mult_bound P.B P.A Tn
  calc ∑ p ∈ (Z.filter (fun p => g p ≠ 0)).filter (fun p => Φ p = n), g p
      ≤ ∑ p ∈ (Z.filter (fun p => g p ≠ 0)).filter (fun p => Φ p = n), (r Tn : ℝ) :=
        Finset.sum_le_sum (fun p hp => (hfib p hp).1)
    _ = ((Z.filter (fun p => g p ≠ 0)).filter (fun p => Φ p = n)).card * (r Tn : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r ((Tn - P.A) * (Tn - P.A + P.B)) : ℝ) * r Tn := by
        gcongr
        exact_mod_cast le_trans hcard hmult
    _ = P.multWeight n := by
        simp only [multWeight, hTn]
        push_cast
        have e1 : (n : ℤ) + P.p₀ + P.A - P.A = n + P.p₀ := by ring
        rw [e1]; ring

end PatternData

end Triples
