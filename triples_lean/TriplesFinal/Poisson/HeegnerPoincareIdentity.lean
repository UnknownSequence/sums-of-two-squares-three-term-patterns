import TriplesFinal.Poisson.Unfolding

/-!
# Lemma 9.2: the Heegner–Poincaré identities (9.2) and (9.3)

Under (H), with `Γ = Γ₀(q)`, `q = 4Ed`, and the Heegner points `z_1, …, z_I` of the
representatives of the `Γ`-orbits on `Q^κ`:
`∑_{μ ≡ κd (4d)} g(√N/(Eμ)) S(h; μ) = ∑_{i=1}^{I} P_{g,h}(z_i)` (equation (9.2)), and
`W_h = ∑_i P_h(z_i)` with `P_h = P_{g_h,h}` (equation (9.3)).

By Lemma 8.2(a), `(μ, ν) ↦ ((Eν² + H)/μ, Eν; Eν, Eμ)` is a bijection from the pairs with
`0 ≤ ν < μ`, `μ ≡ κd (mod 4d)`, `μ ∣ Eν² + H` onto the reduced elements of `Q^κ`, and
`G(z(𝔤)) = g(√N/(Eμ)) e(hν/μ)` (`sum_fund_Qkappa`). Together with the unfolding identity
(`Poisson/Unfolding.lean`) this gives (9.2). As the paper remarks, the proof of (9.2) uses
neither the smoothness of `g` nor the remaining conditions of (H) (`heegner_poincare_core`).

Paper: §9.2, Lemma 9.2.
-/

namespace Triples

open scoped MatrixGroups
open CongruenceSubgroup UpperHalfPlane SymMat
open scoped ContDiff

namespace SymMat

section Kappa

variable {E H d κ : ℕ}

theorem mem_pairSet_of_nat {μ ν : ℕ} (hμ1 : 1 ≤ μ) (hμκ : μ % (4 * d) = κ * d % (4 * d))
    (hdvd : (μ : ℤ) ∣ (E : ℤ) * (ν : ℤ) ^ 2 + H) :
    ((μ : ℤ), (ν : ℤ)) ∈ pairSet (E : ℤ) H d κ := by
  refine ⟨show (1 : ℤ) ≤ μ by exact_mod_cast hμ1, ?_, hdvd⟩
  have : ((μ % (4 * d) : ℕ) : ℤ) = ((κ * d % (4 * d) : ℕ) : ℤ) := by rw [hμκ]
  push_cast at this
  exact this

theorem nat_of_mem_pairSet {μ ℓ : ℤ} (hp : (μ, ℓ) ∈ pairSet (E : ℤ) H d κ) :
    1 ≤ μ.toNat ∧ μ.toNat % (4 * d) = κ * d % (4 * d) ∧ ((μ.toNat : ℕ) : ℤ) = μ := by
  obtain ⟨hμ1, hμκ, -⟩ := hp
  have hμ : ((μ.toNat : ℕ) : ℤ) = μ := Int.toNat_of_nonneg (by omega)
  refine ⟨by omega, ?_, hμ⟩
  have h1 : ((μ.toNat % (4 * d) : ℕ) : ℤ) = ((κ * d % (4 * d) : ℕ) : ℤ) := by
    push_cast
    rw [hμ]
    exact hμκ
  exact_mod_cast h1

/-- `G` at the Heegner point of `(μ, ν)`: `G(z(𝔤)) = G(√N/(Eμ)) e(hν/μ)`. -/
theorem Gfun_zpt_ofPair (hE : 0 < E) (hH : 0 < H) {μ ν : ℕ} (hμ1 : 1 ≤ μ)
    (hmem : ofPair (E : ℤ) H ((μ : ℤ), (ν : ℤ)) ∈ QN ((E : ℤ) * H)) (G : ℝ → ℂ) (h : ℤ) :
    Gfun G h (zpt (ofPair (E : ℤ) H ((μ : ℤ), (ν : ℤ)))) =
      G (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * eC ((h : ℝ) * ν / μ) := by
  rw [Gfun_zpt (by positivity) hmem, eC]
  simp only [ofPair]
  have hE' : (E : ℝ) ≠ 0 := by positivity
  have hμ' : (μ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    have hE'' : (E : ℂ) ≠ 0 := by exact_mod_cast hE'
    have hμ'' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ'
    push_cast
    field_simp

/-- The sum of `G(z(𝔤))` over the `Γ_∞`-reduced `𝔤 ∈ Q^κ` is the left-hand side of (9.2). -/
theorem sum_fund_Qkappa (hE : 0 < E) (hH : 0 < H) {G : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hG : ∀ y, G y ≠ 0 → a ≤ y) (h : ℤ) :
    ∑ᶠ s ∈ fund (Qkappa (E : ℤ) H d κ), Gfun G h (zpt s) =
      ∑ᶠ (μ : ℕ) (_ : 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d)),
        G (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * weylSum E H h μ := by
  classical
  have hN : (0 : ℤ) < (E : ℤ) * H := by positivity
  have hQ : Qkappa (E : ℤ) H d κ ⊆ QN ((E : ℤ) * H) := fun s hs => hs.1
  have hbij := ofPair_bijOn (E := (E : ℤ)) (H := (H : ℤ)) (d := d) (κ := κ)
    (by exact_mod_cast hE) (by exact_mod_cast hH)
  set S := {s | s ∈ fund (Qkappa (E : ℤ) H d κ) ∧ G (Real.sqrt ((E : ℤ) * H : ℤ) / s.c) ≠ 0}
    with hSdef
  have hSfin : S.Finite := fund_support_finite hQ ha hG
  have hGfun : ∀ s ∈ fund (Qkappa (E : ℤ) H d κ), Gfun G h (zpt s) ≠ 0 → s ∈ S := by
    intro s hs hne
    refine ⟨hs, fun h0 => hne ?_⟩
    rw [Gfun_zpt hN (hQ hs.1), h0, zero_mul]
  rw [finsum_mem_eq_sum_of_subset _ (t := hSfin.toFinset)]
  rotate_left
  · intro s ⟨hs, hne⟩
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hGfun s hs hne
  · intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    exact hs.1
  -- every `s ∈ S` comes from a pair `(μ, ℓ)` with `0 ≤ ℓ < μ`
  have hS_pair : ∀ s ∈ S, ∃ μ ℓ : ℤ, (μ, ℓ) ∈ pairSet (E : ℤ) H d κ ∧ 0 ≤ ℓ ∧ ℓ < μ ∧
      s = ofPair (E : ℤ) H (μ, ℓ) := by
    intro s hs
    obtain ⟨⟨μ, ℓ⟩, hp, rfl⟩ := hbij.surjOn hs.1.1
    have hE0 : (0 : ℤ) < E := by exact_mod_cast hE
    obtain ⟨-, hb0, hbc⟩ := hs.1
    simp only [ofPair] at hb0 hbc
    refine ⟨μ, ℓ, hp, ?_, ?_, rfl⟩
    · exact nonneg_of_mul_nonneg_right (by linarith) hE0
    · exact lt_of_mul_lt_mul_left hbc hE0.le
  set μOf : SymMat → ℕ := fun s => (s.c / E).toNat with hμOf
  set νOf : SymMat → ℕ := fun s => (s.b / E).toNat with hνOf
  have hE0 : (E : ℤ) ≠ 0 := by exact_mod_cast hE.ne'
  have hμOf_pair : ∀ μ ℓ : ℤ, μOf (ofPair (E : ℤ) H (μ, ℓ)) = μ.toNat := by
    intro μ ℓ
    simp only [hμOf, ofPair, Int.mul_ediv_cancel_left _ hE0]
  have hνOf_pair : ∀ μ ℓ : ℤ, νOf (ofPair (E : ℤ) H (μ, ℓ)) = ℓ.toNat := by
    intro μ ℓ
    simp only [hνOf, ofPair, Int.mul_ediv_cancel_left _ hE0]
  set Mfin := hSfin.toFinset.image μOf with hMfin
  set R : ℕ → Finset ℕ :=
    fun μ => (Finset.range μ).filter (fun ν : ℕ => (μ : ℤ) ∣ (E : ℤ) * (ν : ℤ) ^ 2 + H) with hR
  -- `μ ∈ Mfin` gives `μ ≥ 1`, the congruence, and `G(√N/(Eμ)) ≠ 0`
  have hMfin_mem : ∀ μ ∈ Mfin, 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d) ∧
      G (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) ≠ 0 := by
    intro μ hμ
    rw [hMfin, Finset.mem_image] at hμ
    obtain ⟨s, hs, rfl⟩ := hμ
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨μ', ℓ, hp, -, -, rfl⟩ := hS_pair s hs
    obtain ⟨h1, h2, h3⟩ := nat_of_mem_pairSet hp
    rw [hμOf_pair]
    refine ⟨h1, h2, ?_⟩
    have := hs.2
    simp only [ofPair] at this
    convert this using 2
    have h3' : ((μ'.toNat : ℕ) : ℝ) = (μ' : ℝ) := by exact_mod_cast h3
    push_cast
    rw [h3']
  change _ = ∑ᶠ μ ∈ {μ : ℕ | 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d)},
    G (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * weylSum E H h μ
  rw [finsum_mem_eq_sum_of_subset _ (t := Mfin)]
  rotate_left
  · -- the support of the left-hand side is in `Mfin`
    intro μ ⟨⟨hμ1, hμκ⟩, hne⟩
    rw [Finset.mem_coe, hMfin, Finset.mem_image]
    have hne' : G (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) ≠ 0 ∧ weylSum E H h μ ≠ 0 := by
      constructor
      · intro h0; apply hne; dsimp only; rw [h0, zero_mul]
      · intro h0; apply hne; dsimp only; rw [h0, mul_zero]
    obtain ⟨ν, hν⟩ : ∃ ν, ν ∈ R μ := by
      by_contra hno
      push Not at hno
      apply hne'.2
      unfold weylSum
      rw [Finset.sum_eq_zero]
      intro ν hν
      exact absurd hν (hno ν)
    rw [hR, Finset.mem_filter, Finset.mem_range] at hν
    have hp := mem_pairSet_of_nat (E := E) (H := H) hμ1 hμκ hν.2
    refine ⟨ofPair (E : ℤ) H ((μ : ℤ), (ν : ℤ)), ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      refine ⟨⟨hbij.mapsTo hp, ?_, ?_⟩, ?_⟩
      · simp only [ofPair]; positivity
      · simp only [ofPair]
        have : (ν : ℤ) < μ := by exact_mod_cast hν.1
        exact mul_lt_mul_of_pos_left this (by exact_mod_cast hE)
      · simp only [ofPair]
        convert hne'.1 using 2
        push_cast; rfl
    · rw [hμOf_pair]; simp
  · intro μ hμ
    obtain ⟨h1, h2, -⟩ := hMfin_mem μ hμ
    exact ⟨h1, h2⟩
  -- expand the Weyl sums and match the pairs `(μ, ν)` with `S`
  simp only [weylSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' (fun s => (⟨μOf s, νOf s⟩ : Σ _ : ℕ, ℕ))
    (fun p => ofPair (E : ℤ) H ((p.1 : ℤ), (p.2 : ℤ)))
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_image_of_mem _ (by rw [Set.Finite.mem_toFinset]; exact hs), ?_⟩
    obtain ⟨μ, ℓ, hp, hℓ0, hℓμ, rfl⟩ := hS_pair s hs
    rw [hμOf_pair, hνOf_pair]
    dsimp only
    rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨-, -, h3⟩ := nat_of_mem_pairSet hp
    have hℓ : ((ℓ.toNat : ℕ) : ℤ) = ℓ := Int.toNat_of_nonneg hℓ0
    refine ⟨by omega, ?_⟩
    rw [h3, hℓ]
    exact hp.2.2
  · intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hμ, hν⟩ := hp
    obtain ⟨hμ1, hμκ, hG0⟩ := hMfin_mem p.1 hμ
    rw [Finset.mem_filter, Finset.mem_range] at hν
    rw [Set.Finite.mem_toFinset]
    refine ⟨⟨hbij.mapsTo (mem_pairSet_of_nat hμ1 hμκ hν.2), ?_, ?_⟩, ?_⟩
    · simp only [ofPair]; positivity
    · simp only [ofPair]
      have : (p.2 : ℤ) < p.1 := by exact_mod_cast hν.1
      exact mul_lt_mul_of_pos_left this (by exact_mod_cast hE)
    · simp only [ofPair]
      convert hG0 using 2
      push_cast; rfl
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨μ, ℓ, hp, hℓ0, -, rfl⟩ := hS_pair s hs
    obtain ⟨-, -, h3⟩ := nat_of_mem_pairSet hp
    simp only [hμOf_pair, hνOf_pair]
    rw [h3, Int.toNat_of_nonneg hℓ0]
  · intro p hp
    rw [hμOf_pair, hνOf_pair]
    simp
  · intro s hs
    rw [Set.Finite.mem_toFinset] at hs
    obtain ⟨μ, ℓ, hp, hℓ0, -, rfl⟩ := hS_pair s hs
    obtain ⟨hμ1, -, h3⟩ := nat_of_mem_pairSet hp
    rw [hμOf_pair, hνOf_pair]
    have hmem := hbij.mapsTo hp
    have e : ofPair (E : ℤ) H (((μ.toNat : ℕ) : ℤ), ((ℓ.toNat : ℕ) : ℤ)) = ofPair (E : ℤ) H (μ, ℓ) := by
      rw [h3, Int.toNat_of_nonneg hℓ0]
    rw [← e] at hmem ⊢
    exact Gfun_zpt_ofPair hE hH hμ1 hmem.1 G h

end Kappa

/-- **Lemma 9.2**, equation (9.2), for any `g` vanishing on `(0, a)` with `a > 0` (the proof uses
neither the smoothness of `g` nor the remaining conditions of (H)). -/
theorem heegner_poincare_core {E H d κ : ℕ} {q : ℕ} (hq : q = 4 * E * d) (hE : 0 < E)
    (hH : 0 < H) (hNsq : ¬ ∃ s : ℤ, (E * H : ℤ) = s ^ 2)
    (hN3 : ¬ ∃ s : ℤ, (E * H : ℤ) = 3 * s ^ 2) {Λ : Set SymMat}
    (hΛ : IsOrbitReps ((E : ℤ) * H) Λ) {T : Set SL(2, ℤ)} (hT : IsCosetReps q T)
    {g : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hg : ∀ y, g y ≠ 0 → a ≤ y) (h : ℤ) :
    (∑ᶠ (μ : ℕ) (_ : 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d)),
        g (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * weylSum E H h μ) =
      ∑ᶠ g' ∈ heegnerReps Λ T (Qkappa E H d κ), poincare q g h (zpt g') := by
  have hN : (0 : ℤ) < (E : ℤ) * H := by positivity
  have hinv : ∀ γ ∈ Gamma0 q, ∀ g' ∈ Qkappa (E : ℤ) H d κ, act γ g' ∈ Qkappa (E : ℤ) H d κ :=
    fun γ hγ g' hg' => Qkappa_invariant (by exact_mod_cast hE) (by exact_mod_cast hH)
      (by rw [hq]; push_cast; ring) hγ hg'
  rw [sum_poincare_eq hN hNsq hN3 (fun s hs => hs.1) hinv hΛ hT ha hg h,
    sum_fund_Qkappa hE hH ha hg h]

end SymMat

open SymMat

/-- **Lemma 9.2**, equation (9.2). -/
theorem heegner_poincare {E H d κ : ℕ} {q : ℕ} (hq : q = 4 * E * d) (hE : E = 4 ∨ E = 8)
    (hH : 1 ≤ H) (_hHodd : H % 2 = 1) (_hd : d.Prime) (_hd3 : 3 ≤ d) (_hdH : ¬ d ∣ H)
    (hNsq : ¬ ∃ s : ℤ, (E * H : ℤ) = s ^ 2) (hN3 : ¬ ∃ s : ℤ, (E * H : ℤ) = 3 * s ^ 2)
    (_hκ : κ = 1 ∨ κ = 3) {Λ : Set SymMat} (hΛ : IsOrbitReps ((E : ℤ) * H) Λ) {T : Set SL(2, ℤ)}
    (hT : IsCosetReps q T) {g : ℝ → ℂ} (_hg : ContDiff ℝ ∞ g)
    (hgs : ∃ a b : ℝ, 0 < a ∧ ∀ y, g y ≠ 0 → a ≤ y ∧ y ≤ b) (h : ℤ) :
    (∑ᶠ (μ : ℕ) (_ : 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d)),
        g (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * weylSum E H h μ) =
      ∑ᶠ g' ∈ heegnerReps Λ T (Qkappa E H d κ), poincare q g h (zpt g') := by
  obtain ⟨a, b, ha, hgs'⟩ := hgs
  have hE0 : 0 < E := by rcases hE with rfl | rfl <;> norm_num
  exact heegner_poincare_core hq hE0 hH hNsq hN3 hΛ hT ha (fun y hy => (hgs' y hy).1) h

/-- The value `g_h(√N/(Eμ)) = ψ₁(μ/K) (X/μ) ψ̂₂(hX/μ)`. -/
theorem gh_apply {E H : ℕ} (hE : 0 < E) (hH : 0 < H) {X K : ℝ} (hK : 0 < K) (ψ₁ ψ₂ : ℝ → ℂ)
    (h : ℤ) {μ : ℕ} (hμ : 1 ≤ μ) :
    gh E H X K ψ₁ ψ₂ h (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) =
      ψ₁ ((μ : ℝ) / K) * ((X / μ : ℝ) : ℂ) * fourier ψ₂ ((h : ℝ) * X / μ) := by
  have hs : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hE' : (E : ℝ) ≠ 0 := by positivity
  have hμ' : (μ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs' := hs.ne'
  have hK' := hK.ne'
  have e1 : Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ))) =
      μ / K := by field_simp
  have e2 : E * X * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) / Real.sqrt ((E * H : ℕ) : ℝ) =
      X / μ := by field_simp
  have e3 : E * h * X * (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) / Real.sqrt ((E * H : ℕ) : ℝ) =
      h * X / μ := by field_simp
  unfold gh
  rw [e1, e2, e3]

/-- **Lemma 9.2**, the case `g = g_h`: `W_h = ∑_i P_h(z_i)` for `h ≥ 1`. -/
theorem Wh_eq_sum_poincare {Cν : ℕ → ℝ} {E H d κ : ℕ} {Δ X K : ℝ} {ψ₁ ψ₂ : ℝ → ℂ}
    (hH : HypH Cν E H d κ Δ X K ψ₁ ψ₂) {Λ : Set SymMat} (hΛ : IsOrbitReps ((E : ℤ) * H) Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps (4 * E * d) T) {h : ℤ} (_hh : 1 ≤ h) :
    Wh E H d κ X K ψ₁ ψ₂ h =
      ∑ᶠ g' ∈ heegnerReps Λ T (Qkappa E H d κ),
        poincare (4 * E * d) (gh E H X K ψ₁ ψ₂ h) h (zpt g') := by
  have hE0 : 0 < E := by rcases hH.hE with h | h <;> rw [h] <;> norm_num
  have hH0 : 0 < H := hH.hH
  have hK : 0 < K := lt_of_lt_of_le one_pos hH.hK1
  have hs : 0 < Real.sqrt ((E * H : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hNsq : ¬ ∃ s : ℤ, (E * H : ℤ) = s ^ 2 := by
    rintro ⟨s, hs⟩
    apply hH.hNsq
    refine ⟨s.natAbs, ?_⟩
    have : ((E * H : ℕ) : ℤ) = ((s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact hs
    exact_mod_cast this
  have hN3 : ¬ ∃ s : ℤ, (E * H : ℤ) = 3 * s ^ 2 := by
    rintro ⟨s, hs⟩
    apply hH.hN3
    refine ⟨s.natAbs, ?_⟩
    have : ((E * H : ℕ) : ℤ) = ((3 * s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact hs
    exact_mod_cast this
  -- `g_h` vanishes on `(0, √N/(2EK))`
  set a := Real.sqrt ((E * H : ℕ) : ℝ) / (2 * E * K) with ha_def
  have ha : 0 < a := by positivity
  have hgs : ∀ y, gh E H X K ψ₁ ψ₂ h y ≠ 0 → a ≤ y := by
    intro y hy
    have h1 : ψ₁ (Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y)) ≠ 0 := by
      intro h0; apply hy; unfold gh; rw [h0, zero_mul, zero_mul]
    obtain ⟨hlo, hhi⟩ := hH.supp₁ _ h1
    have hy0 : 0 < y := by
      by_contra hy0
      push Not at hy0
      have : Real.sqrt ((E * H : ℕ) : ℝ) / (E * K * y) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hs.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) hy0)
      linarith
    rw [ha_def, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hhi
    linarith
  rw [← heegner_poincare_core rfl hE0 hH0 hNsq hN3 hΛ hT ha hgs h]
  unfold Wh
  symm
  change ∑ᶠ μ ∈ {μ : ℕ | 1 ≤ μ ∧ μ % (4 * d) = κ * d % (4 * d)},
    gh E H X K ψ₁ ψ₂ h (Real.sqrt ((E * H : ℕ) : ℝ) / (E * μ)) * weylSum E H h μ = _
  rw [finsum_mem_eq_sum_of_subset _ (t := moduli d κ K)]
  · apply Finset.sum_congr rfl
    intro μ hμ
    simp only [moduli, Finset.mem_filter, Finset.mem_Icc] at hμ
    rw [gh_apply hE0 hH0 hK ψ₁ ψ₂ h hμ.1.1]
  · intro μ ⟨⟨hμ1, hμκ⟩, hne⟩
    simp only [Finset.mem_coe, moduli, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hμ1, ?_⟩, hμκ⟩
    have hψ : ψ₁ ((μ : ℝ) / K) ≠ 0 := by
      intro h0; apply hne; dsimp only
      rw [gh_apply hE0 hH0 hK ψ₁ ψ₂ h hμ1, h0, zero_mul, zero_mul, zero_mul]
    have := (hH.supp₁ _ hψ).2
    rw [div_le_iff₀ hK] at this
    exact Nat.le_floor (by linarith)
  · intro μ hμ
    simp only [Finset.mem_coe, moduli, Finset.mem_filter, Finset.mem_Icc] at hμ
    exact ⟨hμ.1.1, hμ.2⟩

end Triples
