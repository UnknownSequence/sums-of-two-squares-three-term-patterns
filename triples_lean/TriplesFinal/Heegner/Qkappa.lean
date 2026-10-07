import TriplesFinal.Heegner.Orbits

/-!
# Lemma 8.2: the sets `Q^κ`

Under (H) put `N = EH`, `q = 4Ed` and
`Q^κ = {𝔤 ∈ Q_N : 𝔟 ≡ 0 (mod E), 𝔠 ≡ κEd (mod 4Ed)}`.
(a) `(μ, ℓ) ↦ ((Eℓ² + H)/μ, Eℓ; Eℓ, Eμ)` is a bijection from the pairs with `μ ≥ 1`,
`μ ≡ κd (mod 4d)`, `μ ∣ Eℓ² + H` onto `Q^κ`.
(b) `Q^κ` is invariant under `Γ₀(q)`.

Paper: §8.2, Lemma 8.2.
-/

namespace Triples

open scoped MatrixGroups

namespace SymMat

open CongruenceSubgroup

/-- `Q^κ = {𝔤 ∈ Q_{EH} : 𝔟 ≡ 0 (mod E), 𝔠 ≡ κEd (mod 4Ed)}`. -/
def Qkappa (E H d κ : ℤ) : Set SymMat :=
  {g | g ∈ QN (E * H) ∧ g.b ≡ 0 [ZMOD E] ∧ g.c ≡ κ * E * d [ZMOD 4 * E * d]}

/-- The pairs `(μ, ℓ)` with `μ ≥ 1`, `μ ≡ κd (mod 4d)` and `μ ∣ Eℓ² + H`. -/
def pairSet (E H d κ : ℤ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ p.1 ≡ κ * d [ZMOD 4 * d] ∧ p.1 ∣ E * p.2 ^ 2 + H}

/-- The matrix `((Eℓ² + H)/μ, Eℓ; Eℓ, Eμ)` attached to `(μ, ℓ)`. -/
def ofPair (E H : ℤ) (p : ℤ × ℤ) : SymMat := ⟨(E * p.2 ^ 2 + H) / p.1, E * p.2, E * p.1⟩

/-- **Lemma 8.2(a).** `ofPair` is a bijection from `pairSet` onto `Q^κ`. -/
theorem ofPair_bijOn {E H d κ : ℤ} (hE : 0 < E) (hH : 0 < H) :
    Set.BijOn (ofPair E H) (pairSet E H d κ) (Qkappa E H d κ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- maps to
    rintro ⟨μ, ℓ⟩ ⟨hμ, hμκ, hdvd⟩
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < E * ℓ ^ 2 + H := by positivity
    have hk0 : 0 < k := by
      rw [hk] at hpos
      exact pos_of_mul_pos_right hpos (by omega)
    have hdiv : (E * ℓ ^ 2 + H) / μ = k := by
      rw [hk]; exact Int.mul_ediv_cancel_left _ (by omega)
    simp only [ofPair, Qkappa, QN, Set.mem_ofPred_eq, det, hdiv]
    refine ⟨⟨hk0, mul_pos hE (by omega), ?_⟩, ?_, ?_⟩
    · linear_combination E * hk.symm
    · exact Int.modEq_zero_iff_dvd.2 (dvd_mul_right E ℓ)
    · have h := hμκ.mul_left' (c := E)
      have e1 : E * (4 * d) = 4 * E * d := by ring
      have e2 : E * (κ * d) = κ * E * d := by ring
      rwa [e1, e2] at h
  · -- injective
    rintro ⟨μ, ℓ⟩ - ⟨μ', ℓ'⟩ - h
    simp only [ofPair, SymMat.mk.injEq] at h
    obtain ⟨-, h2, h3⟩ := h
    have hℓ : ℓ = ℓ' := mul_left_cancel₀ hE.ne' h2
    have hμ : μ = μ' := mul_left_cancel₀ hE.ne' h3
    rw [hℓ, hμ]
  · -- surjective
    rintro g ⟨⟨ha, hc, hdet⟩, hb, hcκ⟩
    obtain ⟨ℓ, hℓ⟩ := Int.modEq_zero_iff_dvd.1 hb
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.1 hcκ
    -- `𝔠 = Eμ` with `μ = κd - 4dt`
    set μ := κ * d - 4 * d * t with hμdef
    have hcμ : g.c = E * μ := by rw [hμdef]; linear_combination -ht
    have hμ1 : 1 ≤ μ := by
      have h0 : 0 < E * μ := by rw [← hcμ]; exact hc
      have := pos_of_mul_pos_right h0 hE.le
      omega
    have haμ : g.a * μ = E * ℓ ^ 2 + H := by
      simp only [det] at hdet
      rw [hcμ, hℓ] at hdet
      have : E * (g.a * μ - (E * ℓ ^ 2 + H)) = 0 := by linear_combination hdet
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hE.ne'
      · linarith
    refine ⟨(μ, ℓ), ⟨hμ1, ?_, ⟨g.a, by rw [← haμ]; ring⟩⟩, ?_⟩
    · exact Int.modEq_iff_dvd.2 ⟨t, by rw [hμdef]; ring⟩
    · refine SymMat.ext ?_ ?_ ?_
      · show (E * ℓ ^ 2 + H) / μ = g.a
        rw [← haμ]; exact Int.mul_ediv_cancel _ (by omega)
      · show E * ℓ = g.b
        rw [hℓ]
      · show E * μ = g.c
        rw [hcμ]

/-- **Lemma 8.2(b).** For `q = 4Ed`, `Q^κ` is invariant under `Γ₀(q)`. -/
theorem Qkappa_invariant {E H d κ : ℤ} (hE : 0 < E) (hH : 0 < H) {q : ℕ}
    (hq : (q : ℤ) = 4 * E * d) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 q) {g : SymMat}
    (hg : g ∈ Qkappa E H d κ) : act γ g ∈ Qkappa E H d κ := by
  obtain ⟨hgQ, hb, hc⟩ := hg
  have hr : (q : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.1 hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  rw [hq] at hr
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  -- `E ∣ 𝔟`, `Ed ∣ 𝔠`, `E ∣ γ₃`
  have hEb : E ∣ g.b := Int.modEq_zero_iff_dvd.1 hb
  have hEdc : E * d ∣ g.c := by
    have h1 : 4 * E * d ∣ κ * E * d - g.c := Int.modEq_iff_dvd.1 hc
    have h2 : E * d ∣ κ * E * d - g.c := dvd_trans ⟨4, by ring⟩ h1
    have h3 : E * d ∣ κ * E * d := ⟨κ, by ring⟩
    have := dvd_sub h3 h2
    simpa using this
  have hEc : E ∣ g.c := dvd_trans (dvd_mul_right E d) hEdc
  have hEr : E ∣ γ 1 0 := dvd_trans ⟨4 * d, by ring⟩ hr
  -- `γ₄` is odd, so `4 ∣ γ₄² - 1`
  have h4 : (4 : ℤ) ∣ γ 1 1 ^ 2 - 1 := by
    have h2r : (2 : ℤ) ∣ γ 1 0 := dvd_trans ⟨2 * E * d, by ring⟩ hr
    obtain ⟨r', hr'⟩ := h2r
    have hodd : Odd (γ 0 0 * γ 1 1) := ⟨γ 0 1 * r', by rw [hr'] at hdet; linear_combination hdet⟩
    obtain ⟨k, hk⟩ := (Int.odd_mul.1 hodd).2
    exact ⟨k * (k + 1), by rw [hk]; ring⟩
  simp only [Qkappa, Set.mem_ofPred_eq]
  refine ⟨act_mem_QN (by positivity) γ.det_coe hgQ, ?_, ?_⟩
  · -- the off-diagonal entry is `≡ 0 (mod E)`
    apply Int.modEq_zero_iff_dvd.2
    simp only [act]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hEr _) _
    · exact Dvd.dvd.mul_left hEb _
    · exact Dvd.dvd.mul_left hEc _
  · -- the lower right entry is `≡ 𝔠 ≡ κEd (mod 4Ed)`
    refine Int.ModEq.trans ?_ hc
    apply Int.modEq_iff_dvd.2
    simp only [act]
    obtain ⟨r, hr⟩ := hr
    obtain ⟨m, hm⟩ := h4
    obtain ⟨n, hn⟩ := hEdc
    exact ⟨-(r ^ 2 * (4 * E * d) * g.a + 2 * r * γ 1 1 * g.b + m * n), by
      rw [hr]; linear_combination (-g.c) * hm - 4 * m * hn⟩

end SymMat

end Triples
