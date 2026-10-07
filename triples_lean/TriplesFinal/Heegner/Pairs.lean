import TriplesFinal.Heegner.HeegnerPoint
import TriplesFinal.Heegner.Cosets
import TriplesFinal.Assumptions.Defs
import TriplesFinal.Basic.DivisorBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Lemma 8.4: the number of Heegner points and the pair count `𝒫`

Let `Λ_N` be a set of *reduced* representatives (`|2𝔟| ≤ 𝔠 ≤ 𝔞`) of the `SL₂(ℤ)`-orbits on
`Q_N`, `𝒯_q` a set of representatives of `Γ₀(q) \ SL₂(ℤ)`, and `𝔤₁, …, 𝔤_I` the matrices
`τ ⋄ ζ ∈ Q^κ` (`ζ ∈ Λ_N`, `τ ∈ 𝒯_q`), with Heegner points `z_i = z(𝔤_i)`. Then
`I ≤ 96 #Λ_N ≪_η N^(1/2+η)` and
`𝒫 = ∑_{i,i'} #{γ ∈ Γ₀(q) : u(z_i, γ z_{i'}) ≤ 1}
   ≤ 192 ∑_{ζ ∈ Λ_N} #{𝔴 ∈ Q_N : u(z(𝔴), z(ζ)) ≤ 1} ≪_η N^(1+η)`.

The counting in the formalization uses, instead of the bound for `ϱ_N(𝔠)`, the divisor bound:
a reduced `ζ ∈ Λ_N` has `𝔟² ≤ N`, a matrix `𝔴` with `u(z(𝔴), z(ζ)) ≤ 1` has `𝔟_𝔴² ≤ 72N`, and
`𝔴 ↦ (𝔟, 𝔠)` is injective with `𝔠 ∣ N + 𝔟²`, so both counts are at most
`∑_{|𝔟| ≪ √N} τ(N + 𝔟²) ≪ N^(1/2+ε)` (`bcSet`, `card_bcSet_le_rpow`).

Paper: §8.3, Lemma 8.4.
-/

namespace Triples

open scoped MatrixGroups

namespace SymMat

open CongruenceSubgroup UpperHalfPlane

/-- `𝔤` is reduced: `|2𝔟| ≤ 𝔠 ≤ 𝔞`. -/
def IsReduced (g : SymMat) : Prop := |2 * g.b| ≤ g.c ∧ g.c ≤ g.a

/-- The Heegner representatives `{τ ⋄ ζ : ζ ∈ Λ, τ ∈ 𝒯, τ ⋄ ζ ∈ 𝒬}`. -/
def heegnerReps (Λ : Set SymMat) (T : Set SL(2, ℤ)) (Q : Set SymMat) : Set SymMat :=
  {g | g ∈ Q ∧ ∃ ζ ∈ Λ, ∃ τ ∈ T, g = act τ ζ}

/-- The pair count `𝒫 = ∑_{i,i'} #{γ ∈ Γ₀(q) : u(z_i, γ z_{i'}) ≤ 1}`. -/
noncomputable def pairCount (q : ℕ) (R : Set SymMat) : ℕ :=
  ∑ᶠ (g ∈ R) (g' ∈ R),
    {γ : Gamma0 q | pointPair (zpt g) ((γ : SL(2, ℤ)) • zpt g') ≤ 1}.ncard

/-- The number of `𝔴 ∈ Q_N` with `u(z(𝔴), z(ζ)) ≤ 1`. -/
noncomputable def nearCount (N : ℤ) (ζ : SymMat) : ℕ :=
  {w : SymMat | w ∈ QN N ∧ pointPair (zpt w) (zpt ζ) ≤ 1}.ncard

/-- `u(z, w) = (cosh d(z, w) - 1)/2`. -/
theorem pointPair_eq_cosh (z w : ℍ) : pointPair z w = (Real.cosh (dist z w) - 1) / 2 := by
  rw [UpperHalfPlane.cosh_dist, pointPair, Complex.dist_eq]
  have h1 : 0 < z.im := z.im_pos
  have h2 : 0 < w.im := w.im_pos
  field_simp
  ring

theorem pointPair_comm (z w : ℍ) : pointPair z w = pointPair w z := by
  rw [pointPair_eq_cosh, pointPair_eq_cosh, dist_comm]

/-- The action of `SL₂(ℤ)` on `ℍ` factors through `SL₂(ℝ)`. -/
theorem smul_eq_map (γ : SL(2, ℤ)) (z : ℍ) :
    γ • z = (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- `u(γ z, γ w) = u(z, w)` for `γ ∈ SL₂(ℤ)`. -/
theorem pointPair_smul (γ : SL(2, ℤ)) (z w : ℍ) : pointPair (γ • z) (γ • w) = pointPair z w := by
  rw [pointPair_eq_cosh, pointPair_eq_cosh, smul_eq_map, smul_eq_map, dist_smul]

/-- `u(z(𝔴), z(ζ)) · 4N 𝔠_𝔴 𝔠_ζ = (𝔟_𝔴 𝔠_ζ - 𝔟_ζ 𝔠_𝔴)² + N (𝔠_ζ - 𝔠_𝔴)²`. -/
theorem pointPair_zpt {N : ℤ} (hN : 0 < N) {w ζ : SymMat} (hw : w ∈ QN N) (hζ : ζ ∈ QN N) :
    pointPair (zpt w) (zpt ζ) * (4 * N * w.c * ζ.c) =
      ((w.b * ζ.c - ζ.b * w.c : ℤ) : ℝ) ^ 2 + (N : ℝ) * ((ζ.c - w.c : ℤ) : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set s := Real.sqrt N with hs
  have hs2 : s ^ 2 = N := Real.sq_sqrt hNr.le
  have hspos : 0 < s := Real.sqrt_pos.2 hNr
  have hcw : (0 : ℝ) < w.c := by exact_mod_cast hw.2.1
  have hcζ : (0 : ℝ) < ζ.c := by exact_mod_cast hζ.2.1
  have e1 : (zpt w : ℂ) = (((w.b : ℝ) / w.c : ℝ) : ℂ) + ((s / w.c : ℝ) : ℂ) * Complex.I := by
    rw [coe_zpt_of_mem hN hw]
    push_cast
    field_simp
    ring
  have e2 : (zpt ζ : ℂ) = (((ζ.b : ℝ) / ζ.c : ℝ) : ℂ) + ((s / ζ.c : ℝ) : ℂ) * Complex.I := by
    rw [coe_zpt_of_mem hN hζ]
    push_cast
    field_simp
    ring
  have hiw : (zpt w).im = s / w.c := by
    rw [← UpperHalfPlane.coe_im, e1]; simp
  have hiζ : (zpt ζ).im = s / ζ.c := by
    rw [← UpperHalfPlane.coe_im, e2]; simp
  have hnorm : ‖(zpt w : ℂ) - zpt ζ‖ ^ 2 =
      ((w.b : ℝ) / w.c - ζ.b / ζ.c) ^ 2 + (s / w.c - s / ζ.c) ^ 2 := by
    rw [e1, e2, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  unfold pointPair
  rw [hnorm, hiw, hiζ]
  push_cast
  field_simp
  rw [hs2]
  ring

/-- A reduced matrix of `Q_N` has `3𝔠² ≤ 4N` and `𝔟² ≤ N`. -/
theorem reduced_bounds {N : ℤ} {ζ : SymMat} (hζ : ζ ∈ QN N) (hr : IsReduced ζ) :
    3 * ζ.c ^ 2 ≤ 4 * N ∧ ζ.b ^ 2 ≤ N ∧ 4 * ζ.b ^ 2 ≤ ζ.c ^ 2 := by
  obtain ⟨ha, hc, hdet⟩ := hζ
  obtain ⟨hb, hca⟩ := hr
  simp only [det] at hdet
  have h4 : 4 * ζ.b ^ 2 ≤ ζ.c ^ 2 := by
    have := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    nlinarith [sq_abs (2 * ζ.b)]
  have hcc : ζ.c ^ 2 ≤ ζ.a * ζ.c := by nlinarith
  refine ⟨by nlinarith, by nlinarith, h4⟩

/-- If `u(z(𝔴), z(ζ)) ≤ 1` with `ζ` reduced, then `𝔟_𝔴² ≤ 72 N`. -/
theorem near_b_sq_le {N : ℤ} (hN : 0 < N) {w ζ : SymMat} (hw : w ∈ QN N) (hζ : ζ ∈ QN N)
    (hr : IsReduced ζ) (hu : pointPair (zpt w) (zpt ζ) ≤ 1) : w.b ^ 2 ≤ 72 * N := by
  have hid := pointPair_zpt hN hw hζ
  have hcw := hw.2.1
  have hcζ := hζ.2.1
  have hpos : (0 : ℝ) < 4 * N * w.c * ζ.c := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < w.c := by exact_mod_cast hcw
    have : (0 : ℝ) < ζ.c := by exact_mod_cast hcζ
    positivity
  have hR : ((w.b * ζ.c - ζ.b * w.c : ℤ) : ℝ) ^ 2 + (N : ℝ) * ((ζ.c - w.c : ℤ) : ℝ) ^ 2 ≤
      4 * N * w.c * ζ.c := by
    rw [← hid]
    calc pointPair (zpt w) (zpt ζ) * (4 * N * w.c * ζ.c) ≤ 1 * (4 * N * w.c * ζ.c) :=
          mul_le_mul_of_nonneg_right hu hpos.le
      _ = 4 * N * w.c * ζ.c := one_mul _
  have hZ : (w.b * ζ.c - ζ.b * w.c) ^ 2 + N * (ζ.c - w.c) ^ 2 ≤ 4 * N * w.c * ζ.c := by
    exact_mod_cast hR
  obtain ⟨h3c, -, h4b⟩ := reduced_bounds hζ hr
  set b := ζ.b
  set c := ζ.c
  set b' := w.b
  set c' := w.c
  -- `c' < 6c`
  have h1 : (c - c') ^ 2 ≤ 4 * c * c' := by
    have hD := sq_nonneg (b' * c - b * c')
    have : N * (c - c') ^ 2 ≤ N * (4 * c * c') := by nlinarith
    exact le_of_mul_le_mul_left this hN
  have hc6 : c' < 6 * c := by nlinarith
  -- `D² ≤ 24 N c²`
  have hD2 : (b' * c - b * c') ^ 2 ≤ 24 * N * c ^ 2 := by
    have h0 : 0 ≤ N * (c - c') ^ 2 := by positivity
    have : 4 * N * c' * c ≤ 24 * N * c ^ 2 := by
      have : c' * c ≤ 6 * c * c := by nlinarith
      nlinarith
    nlinarith
  -- `(b c')² ≤ 9 c⁴`
  have hbc : (b * c') ^ 2 ≤ 9 * c ^ 4 := by
    have h1' : (b * c') ^ 2 = b ^ 2 * c' ^ 2 := by ring
    have h2' : c' ^ 2 ≤ 36 * c ^ 2 := by nlinarith
    have h3' : b ^ 2 * c' ^ 2 ≤ b ^ 2 * (36 * c ^ 2) := mul_le_mul_of_nonneg_left h2' (sq_nonneg b)
    nlinarith
  -- `(b' c)² ≤ 2 D² + 2 (b c')² ≤ 72 N c²`
  have hsq : (b' * c) ^ 2 ≤ 2 * (b' * c - b * c') ^ 2 + 2 * (b * c') ^ 2 := by
    nlinarith [sq_nonneg (b' * c - b * c' - b * c')]
  have hfin : b' ^ 2 * c ^ 2 ≤ 72 * N * c ^ 2 := by
    have : 18 * c ^ 4 ≤ 24 * N * c ^ 2 := by
      have := mul_le_mul_of_nonneg_left h3c (by positivity : (0 : ℤ) ≤ 6 * c ^ 2)
      nlinarith
    nlinarith
  have hc2 : 0 < c ^ 2 := by positivity
  nlinarith

/-- The pairs `(b, c)` with `|b| ≤ B`, `c ≥ 1` and `c ∣ N + b²`. -/
def bcSet (N B : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-B) B).biUnion fun b =>
    ((N + b ^ 2).natAbs.divisors).image fun c : ℕ => (b, (c : ℤ))

theorem mem_bcSet {N B b c : ℤ} (hN : 0 < N) (hb : |b| ≤ B) (hc : 0 < c)
    (hdvd : c ∣ N + b ^ 2) : (b, c) ∈ bcSet N B := by
  simp only [bcSet, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Nat.mem_divisors]
  refine ⟨b, abs_le.1 hb, c.natAbs, ⟨Int.natAbs_dvd_natAbs.2 hdvd, ?_⟩, ?_⟩
  · have : 0 < N + b ^ 2 := by positivity
    omega
  · simp [Int.natAbs_of_nonneg hc.le]

/-- `#{(b, c)} ≤ (2B + 1) · max τ`. -/
theorem card_bcSet_le {N B : ℤ} (hN : 0 < N) (hB : 0 ≤ B) {Cτ ε : ℝ} (hε : 0 < ε)
    (hCτ : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cτ * (n : ℝ) ^ ε) :
    ((bcSet N B).card : ℝ) ≤ (2 * B + 1) * (Cτ * ((N + B ^ 2 : ℤ) : ℝ) ^ ε) := by
  have hC0 : 0 ≤ Cτ := by
    have := hCτ 1 le_rfl
    simp at this
    linarith
  calc ((bcSet N B).card : ℝ)
      ≤ ∑ b ∈ Finset.Icc (-B) B, (((N + b ^ 2).natAbs.divisors).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le).trans
          (Finset.sum_le_sum fun b _ => Finset.card_image_le)
    _ ≤ ∑ b ∈ Finset.Icc (-B) B, Cτ * ((N + B ^ 2 : ℤ) : ℝ) ^ ε := by
        apply Finset.sum_le_sum
        intro b hb
        rw [Finset.mem_Icc] at hb
        have hpos : 0 < N + b ^ 2 := by positivity
        have h1 := hCτ (N + b ^ 2).natAbs (by omega)
        refine h1.trans ?_
        gcongr
        have : (((N + b ^ 2).natAbs : ℕ) : ℝ) = ((N + b ^ 2 : ℤ) : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
        rw [this]
        have hbB : b ^ 2 ≤ B ^ 2 := by nlinarith
        exact_mod_cast (by linarith : N + b ^ 2 ≤ N + B ^ 2)
    _ = (2 * B + 1) * (Cτ * ((N + B ^ 2 : ℤ) : ℝ) ^ ε) := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
        congr 1
        have h : ((B + 1 - -B).toNat : ℤ) = 2 * B + 1 := by
          rw [Int.toNat_of_nonneg (by linarith)]; ring
        exact_mod_cast h

/-- The bound `#{(b, c)} ≪ N^(1/2+ε)` for `B² ≤ K N`. -/
theorem card_bcSet_le_rpow {N B : ℤ} (hN : 0 < N) (hB : 0 ≤ B) {K : ℝ} (hK : 1 ≤ K)
    (hBK : ((B : ℝ)) ^ 2 ≤ K * N) {Cτ ε : ℝ} (hε : 0 < ε)
    (hCτ : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cτ * (n : ℝ) ^ ε) :
    ((bcSet N B).card : ℝ) ≤
      (2 * Real.sqrt K + 1) * Cτ * (1 + K) ^ ε * (N : ℝ) ^ (1 / 2 + ε) := by
  have hC0 : 0 ≤ Cτ := by
    have := hCτ 1 le_rfl
    simp at this
    linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB0 : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have h1 := card_bcSet_le hN hB hε hCτ
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have hBs : (B : ℝ) ≤ Real.sqrt K * Real.sqrt N := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.le_sqrt_of_sq_le hBK
  have h2 : 2 * (B : ℝ) + 1 ≤ (2 * Real.sqrt K + 1) * Real.sqrt N := by
    have : 1 ≤ Real.sqrt N := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hNr
    nlinarith [Real.sqrt_nonneg K]
  have h3 : ((N + B ^ 2 : ℤ) : ℝ) ≤ (1 + K) * N := by push_cast; nlinarith
  have h4 : ((N + B ^ 2 : ℤ) : ℝ) ^ ε ≤ (1 + K) ^ ε * (N : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by push_cast; positivity) h3 hε.le
  have h5 : (N : ℝ) ^ (1 / 2 + ε) = Real.sqrt N * (N : ℝ) ^ ε := by
    rw [Real.rpow_add (by linarith), Real.sqrt_eq_rpow]
  calc ((bcSet N B).card : ℝ) ≤ (2 * B + 1) * (Cτ * ((N + B ^ 2 : ℤ) : ℝ) ^ ε) := h1
    _ ≤ ((2 * Real.sqrt K + 1) * Real.sqrt N) * (Cτ * ((1 + K) ^ ε * (N : ℝ) ^ ε)) := by
        gcongr
    _ = (2 * Real.sqrt K + 1) * Cτ * (1 + K) ^ ε * (N : ℝ) ^ (1 / 2 + ε) := by
        rw [h5]; ring

/-- `𝔴 ↦ (𝔟, 𝔠)` is injective on `Q_N`. -/
theorem bc_injOn (N : ℤ) : Set.InjOn (fun w : SymMat => (w.b, w.c)) (QN N) := by
  intro w hw w' hw' h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hb, hc⟩ := h
  have h1 : w.a * w.c = w'.a * w'.c := by
    have e1 : w.a * w.c - w.b ^ 2 = N := hw.2.2
    have e2 : w'.a * w'.c - w'.b ^ 2 = N := hw'.2.2
    rw [hb] at e1
    linarith
  rw [hc] at h1
  have ha : w.a = w'.a := mul_right_cancel₀ hw'.2.1.ne' h1
  exact SymMat.ext ha hb hc

/-- A set of matrices of `Q_N` with `𝔟² ≤ K N` is finite, of size at most `#bcSet`. -/
theorem finite_ncard_le_of_b_sq {N : ℤ} (hN : 0 < N) {K : ℕ} {S : Set SymMat} (hS : S ⊆ QN N)
    (hb : ∀ w ∈ S, w.b ^ 2 ≤ K * N) :
    S.Finite ∧ S.ncard ≤ (bcSet N (Nat.sqrt (K * N).natAbs)).card := by
  have hmaps : ∀ w ∈ S, (fun w : SymMat => (w.b, w.c)) w ∈
      ((bcSet N (Nat.sqrt (K * N).natAbs) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro w hw
    have hwQ := hS hw
    rw [Finset.mem_coe]
    apply mem_bcSet hN _ hwQ.2.1
    · have : w.a * w.c - w.b ^ 2 = N := hwQ.2.2
      exact ⟨w.a, by linarith⟩
    · -- `|𝔟| ≤ ⌊√(KN)⌋`
      have h1 : w.b.natAbs * w.b.natAbs ≤ (K * N).natAbs := by
        have h2 : ((w.b.natAbs * w.b.natAbs : ℕ) : ℤ) = w.b ^ 2 := by
          push_cast; rw [abs_mul_abs_self]; ring
        have h3 : (((K * N).natAbs : ℕ) : ℤ) = K * N :=
          Int.natAbs_of_nonneg (by positivity)
        have := hb w hw
        omega
      have h4 := Nat.le_sqrt.2 h1
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h4
  have hinj : Set.InjOn (fun w : SymMat => (w.b, w.c)) S := (bc_injOn N).mono hS
  exact ⟨Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _),
    by simpa using Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)⟩

/-- The square of `⌊√(KN)⌋` is at most `KN`. -/
theorem sqrt_sq_le (K : ℕ) {N : ℤ} (hN : 0 < N) :
    (((Nat.sqrt (K * N).natAbs : ℕ) : ℤ) : ℝ) ^ 2 ≤ (K : ℝ) * N := by
  have h1 := Nat.sqrt_le' (K * N).natAbs
  have h2 : (((K * N).natAbs : ℕ) : ℤ) = K * N := Int.natAbs_of_nonneg (by positivity)
  have h3 : ((Nat.sqrt (K * N).natAbs ^ 2 : ℕ) : ℤ) ≤ K * N := by
    rw [← h2]; exact_mod_cast h1
  have h4 : (((Nat.sqrt (K * N).natAbs : ℕ) : ℤ) : ℝ) ^ 2 ≤ ((K * N : ℤ) : ℝ) := by
    exact_mod_cast h3
  simpa using h4

/-- A bit distinguishing `γ` from `-γ`. -/
def sgnBit (γ : SL(2, ℤ)) : Bool := decide (0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ 0 < γ 1 1))

theorem sgnBit_neg (γ : SL(2, ℤ)) : sgnBit (-γ) = !sgnBit γ := by
  have hdet := det_SL2 γ
  have hd : γ 1 0 = 0 → γ 1 1 ≠ 0 := by
    intro h0 h1; rw [h0, h1] at hdet; simp at hdet
  have key : (0 < -γ 1 0 ∨ (-γ 1 0 = 0 ∧ 0 < -γ 1 1)) ↔
      ¬ (0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ 0 < γ 1 1)) := by
    constructor
    · rintro (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩) <;> omega
    · intro h
      push Not at h
      rcases lt_trichotomy (γ 1 0) 0 with h0 | h0 | h0
      · left; omega
      · right
        have h1 := hd h0
        have h2 := h.2 h0
        omega
      · exact absurd h0 (by omega)
  simp only [sgnBit, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ← decide_not]
  exact decide_eq_decide.2 key

/-- **The reduction to `SL₂(ℤ)`** in the proof of Lemma 8.4: for `𝔤 = τ ⋄ ζ`,
`∑_{𝔤' ∈ R} #{γ ∈ Γ₀(q) : u(z(𝔤), γ z(𝔤')) ≤ 1} ≤ 2 #{𝔴 ∈ Q_N : u(z(𝔴), z(ζ)) ≤ 1}`. -/
theorem inner_le {N : ℤ} (hN : 0 < N) (hsq : ¬ ∃ s : ℤ, N = s ^ 2)
    (h3 : ¬ ∃ s : ℤ, N = 3 * s ^ 2) {q : ℕ} {Λ : Set SymMat} (hΛ : IsOrbitReps N Λ)
    {T : Set SL(2, ℤ)} (hT : IsCosetReps q T) {Q : Set SymMat} (hQ : Q ⊆ QN N)
    (hRfin : (heegnerReps Λ T Q).Finite) {ζ : SymMat} (hζ : ζ ∈ Λ) (τ : SL(2, ℤ))
    (hnear : {w : SymMat | w ∈ QN N ∧ pointPair (zpt w) (zpt ζ) ≤ 1}.Finite) :
    (∑ᶠ g' ∈ heegnerReps Λ T Q,
      {γ : Gamma0 q | pointPair (zpt (act τ ζ)) ((γ : SL(2, ℤ)) • zpt g') ≤ 1}.ncard) ≤
      2 * nearCount N ζ := by
  classical
  set R := heegnerReps Λ T Q with hR
  set g := act τ ζ with hg
  set D : Set (SymMat × Gamma0 q) :=
    {p | p.1 ∈ R ∧ pointPair (zpt g) ((p.2 : SL(2, ℤ)) • zpt p.1) ≤ 1} with hD
  set near := {w : SymMat | w ∈ QN N ∧ pointPair (zpt w) (zpt ζ) ≤ 1} with hnearDef
  set Φ : SymMat × Gamma0 q → SymMat × Bool :=
    fun p => (act ((τ⁻¹ * (p.2 : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) p.1,
      sgnBit p.2) with hΦ
  have hζQ : ζ ∈ QN N := hΛ.1 hζ
  -- `Φ` maps into `near × Bool`
  have hmaps : Set.MapsTo Φ D (near ×ˢ (Set.univ : Set Bool)) := by
    rintro ⟨g', γ⟩ ⟨hg'R, hu⟩
    have hg'Q : g' ∈ QN N := hQ hg'R.1
    refine ⟨⟨act_mem_QN hN (τ⁻¹ * (γ : SL(2, ℤ)) : SL(2, ℤ)).det_coe hg'Q, ?_⟩, Set.mem_univ _⟩
    show pointPair (zpt (act ((τ⁻¹ * (γ : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g'))
      (zpt ζ) ≤ 1
    rw [zpt_act hN hg'Q, mul_smul, ← pointPair_smul τ, smul_inv_smul, pointPair_comm]
    rw [hg, zpt_act hN hζQ] at hu
    exact hu
  -- `Φ` is injective on `D`
  have hinj : Set.InjOn Φ D := by
    rintro ⟨g₁, γ₁⟩ ⟨hg₁R, -⟩ ⟨g₂, γ₂⟩ ⟨hg₂R, -⟩ heq
    simp only [hΦ, Prod.mk.injEq] at heq
    obtain ⟨hact, hsgn⟩ := heq
    have hg₂ : g₂ = act (((γ₂ : SL(2, ℤ))⁻¹ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) g₁ := by
      have h := congrArg
        (act (((γ₂ : SL(2, ℤ))⁻¹ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) hact
      rw [← act_coe_mul, ← act_coe_mul] at h
      have e1 : ((γ₂ : SL(2, ℤ))⁻¹ * τ) * (τ⁻¹ * (γ₁ : SL(2, ℤ))) = (γ₂ : SL(2, ℤ))⁻¹ * γ₁ := by
        group
      have e2 : ((γ₂ : SL(2, ℤ))⁻¹ * τ) * (τ⁻¹ * (γ₂ : SL(2, ℤ))) = 1 := by group
      rw [e1, e2, act_coe_one] at h
      exact h.symm
    obtain ⟨-, ζ₁, hζ₁, τ₁, hτ₁, rfl⟩ := hg₁R
    obtain ⟨-, ζ₂, hζ₂, τ₂, hτ₂, rfl⟩ := hg₂R
    have hγmem : (γ₂ : SL(2, ℤ))⁻¹ * γ₁ ∈ Gamma0 q := mul_mem (inv_mem γ₂.2) γ₁.2
    obtain ⟨hζeq, hτeq⟩ := orbit_reps_unique hN hsq h3 hΛ hT hζ₁ hζ₂ hτ₁ hτ₂ hγmem hg₂
    rw [hζeq, hτeq] at hg₂ ⊢
    -- `τ₁⁻¹ γ₂⁻¹ γ₁ τ₁` fixes `ζ₁`
    have hfix : act ((τ₁⁻¹ * ((γ₂ : SL(2, ℤ))⁻¹ * γ₁) * τ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        ζ₁ = ζ₁ := by
      rw [act_coe_mul, act_coe_mul, ← hg₂, act_coe_inv_act]
    have hpm := stabiliser_SL hN hsq h3 (hΛ.1 hζ₁) hfix
    have hγ : (γ₁ : SL(2, ℤ)) = γ₂ ∨ (γ₁ : SL(2, ℤ)) = -γ₂ := by
      rcases hpm with h | h
      · left
        have : (γ₂ : SL(2, ℤ))⁻¹ * γ₁ = 1 := by
          have := congrArg (fun x => τ₁ * x * τ₁⁻¹) h
          simpa [mul_assoc] using this
        have := congrArg (fun x => (γ₂ : SL(2, ℤ)) * x) this
        simpa [← mul_assoc] using this
      · right
        have : (γ₂ : SL(2, ℤ))⁻¹ * γ₁ = -1 := by
          have := congrArg (fun x => τ₁ * x * τ₁⁻¹) h
          simpa [mul_assoc] using this
        have := congrArg (fun x => (γ₂ : SL(2, ℤ)) * x) this
        simpa [← mul_assoc] using this
    rcases hγ with h | h
    · exact Prod.ext rfl (Subtype.ext h)
    · exfalso
      rw [h, sgnBit_neg] at hsgn
      cases hb : sgnBit (γ₂ : SL(2, ℤ)) <;> simp [hb] at hsgn
  have hDfin : D.Finite := Set.Finite.of_injOn hmaps hinj (hnear.prod Set.finite_univ)
  have hcard : D.ncard ≤ 2 * nearCount N ζ := by
    have := Set.ncard_le_ncard_of_injOn Φ hmaps hinj (hnear.prod Set.finite_univ)
    rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    simp only [nearCount]
    linarith
  -- the sum over `𝔤'` is `#D`
  have hsum : (∑ᶠ g' ∈ R, {γ : Gamma0 q | pointPair (zpt g) ((γ : SL(2, ℤ)) • zpt g') ≤ 1}.ncard)
      = D.ncard := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, Set.ncard_eq_toFinset_card D hDfin]
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := hRfin.toFinset)]
    · apply Finset.sum_congr rfl
      intro g' hg'
      rw [Set.Finite.mem_toFinset] at hg'
      rw [← Set.ncard_coe_finset, Finset.coe_filter, ← Set.ncard_image_of_injective _
        (Prod.mk_right_injective g')]
      congr 1
      ext ⟨g'', γ⟩
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Prod.mk.injEq]
      constructor
      · rintro ⟨γ', hγ', rfl, rfl⟩
        exact ⟨⟨hg', hγ'⟩, rfl⟩
      · rintro ⟨⟨-, hu⟩, rfl⟩
        exact ⟨γ, hu, rfl, rfl⟩
    · intro p hp
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hp ⊢
      exact hp.1
  rw [hsum]
  exact hcard

/-- `#{𝔴 ∈ Q_N : u(z(𝔴), z(ζ)) ≤ 1} ≪ N^(1/2+ε)` for reduced `ζ`. -/
theorem nearSet_finite_card {N : ℤ} (hN : 0 < N) {ζ : SymMat} (hζ : ζ ∈ QN N)
    (hr : IsReduced ζ) :
    {w : SymMat | w ∈ QN N ∧ pointPair (zpt w) (zpt ζ) ≤ 1}.Finite ∧
      nearCount N ζ ≤ (bcSet N (Nat.sqrt ((72 : ℕ) * N).natAbs)).card := by
  have h := finite_ncard_le_of_b_sq hN (K := 72)
    (S := {w : SymMat | w ∈ QN N ∧ pointPair (zpt w) (zpt ζ) ≤ 1}) (fun w hw => hw.1)
    (fun w hw => by have := near_b_sq_le hN hw.1 hζ hr hw.2; push_cast; linarith)
  exact ⟨h.1, h.2⟩

/-- **Lemma 8.4.** For every `η > 0` there is `C` such that, under (H) (with `N = EH`, `q = 4Ed`),
for reduced orbit representatives `Λ` and coset representatives `𝒯`:
`I ≤ 96 #Λ`, `#Λ ≤ C N^(1/2+η)`, `𝒫 ≤ 192 ∑_{ζ ∈ Λ} #{𝔴 : u(z(𝔴), z(ζ)) ≤ 1}`, and
`𝒫 ≤ C N^(1+η)`. -/
theorem pair_count {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (E H d κ : ℤ) (q : ℕ), (E = 4 ∨ E = 8) → 0 < H → H % 2 = 1 → Prime d → 3 ≤ d →
      ¬ d ∣ H → (¬ ∃ s : ℤ, E * H = s ^ 2) → (¬ ∃ s : ℤ, E * H = 3 * s ^ 2) →
      (κ = 1 ∨ κ = 3) → (q : ℤ) = 4 * E * d →
      ∀ (Λ : Set SymMat) (T : Set SL(2, ℤ)), IsOrbitReps (E * H) Λ → (∀ ζ ∈ Λ, IsReduced ζ) →
        IsCosetReps q T →
        ((heegnerReps Λ T (Qkappa E H d κ)).ncard ≤ 96 * Λ.ncard ∧
          (Λ.ncard : ℝ) ≤ C * ((E * H : ℤ) : ℝ) ^ (1 / 2 + η) ∧
          pairCount q (heegnerReps Λ T (Qkappa E H d κ)) ≤
            192 * ∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ ∧
          (pairCount q (heegnerReps Λ T (Qkappa E H d κ)) : ℝ) ≤
            C * ((E * H : ℤ) : ℝ) ^ (1 + η)) := by
  classical
  set ε := η / 2 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨Cτ, hCτ, hτd⟩ := card_divisors_le_rpow hε
  set C₁ := (2 * Real.sqrt ((1 : ℕ) : ℝ) + 1) * Cτ * (1 + ((1 : ℕ) : ℝ)) ^ ε with hC₁
  set C₂ := (2 * Real.sqrt ((72 : ℕ) : ℝ) + 1) * Cτ * (1 + ((72 : ℕ) : ℝ)) ^ ε with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨max C₁ (192 * C₁ * C₂), ?_⟩
  intro E H d κ q hE hH hHodd hd hd3 hdH hsq h3 hκ hq Λ T hΛ hred hT
  have hN : 0 < E * H := by rcases hE with rfl | rfl <;> positivity
  have hNr : (1 : ℝ) ≤ ((E * H : ℤ) : ℝ) := by exact_mod_cast hN
  have hd0 : 0 < d := by linarith
  have hd2 : d ≠ 2 := by omega
  have hQ : Qkappa E H d κ ⊆ {g | g ∈ QN (E * H) ∧ d ∣ g.c} := by
    rintro g ⟨hgQ, -, hgc⟩
    refine ⟨hgQ, ?_⟩
    have h1 : 4 * E * d ∣ κ * E * d - g.c := Int.ModEq.dvd hgc
    have h2 : d ∣ κ * E * d - g.c := (dvd_mul_left d (4 * E)).trans h1
    have h4 : d ∣ κ * E * d := dvd_mul_left d (κ * E)
    have := dvd_sub h4 h2
    simpa using this
  have hQN : Qkappa E H d κ ⊆ QN (E * H) := fun g hg => (hQ hg).1
  -- `Λ` is finite and `#Λ ≪ N^(1/2+ε)`
  obtain ⟨hΛfin, hΛcard⟩ := finite_ncard_le_of_b_sq hN (K := 1) hΛ.1
    (fun ζ hζ => by have := (reduced_bounds (hΛ.1 hζ) (hred ζ hζ)).2.1; push_cast; linarith)
  have hΛreal : (Λ.ncard : ℝ) ≤ C₁ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := by
    have h1 := card_bcSet_le_rpow hN (by positivity) (K := ((1 : ℕ) : ℝ)) (by simp)
      (sqrt_sq_le 1 hN) hε hτd
    calc (Λ.ncard : ℝ) ≤ (bcSet (E * H) (Nat.sqrt (((1 : ℕ) : ℤ) * (E * H)).natAbs)).card := by
          exact_mod_cast hΛcard
      _ ≤ C₁ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := h1
  -- the near sets
  have hnear : ∀ ζ ∈ Λ, {w : SymMat | w ∈ QN (E * H) ∧ pointPair (zpt w) (zpt ζ) ≤ 1}.Finite ∧
      (nearCount (E * H) ζ : ℝ) ≤ C₂ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := by
    intro ζ hζ
    obtain ⟨hfin, hcard⟩ := nearSet_finite_card hN (hΛ.1 hζ) (hred ζ hζ)
    refine ⟨hfin, ?_⟩
    have h1 := card_bcSet_le_rpow hN (by positivity) (K := ((72 : ℕ) : ℝ)) (by norm_num)
      (sqrt_sq_le 72 hN) hε hτd
    calc (nearCount (E * H) ζ : ℝ)
        ≤ (bcSet (E * H) (Nat.sqrt (((72 : ℕ) : ℤ) * (E * H)).natAbs)).card := by
          exact_mod_cast hcard
      _ ≤ C₂ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := h1
  -- the cosets
  have hTζ : ∀ ζ ∈ Λ, {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}.Finite ∧
      {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}.ncard ≤ 96 := by
    intro ζ hζ
    obtain ⟨hfin, hcard⟩ := coset_count_aux hE hd hd0 hd2 hdH hq hT hQ (hΛ.1 hζ)
    refine ⟨hfin, ?_⟩
    have : (12 : ℤ) * E ≤ 96 := by rcases hE with rfl | rfl <;> norm_num
    omega
  set R := heegnerReps Λ T (Qkappa E H d κ) with hR
  have hRsub : R ⊆ ⋃ ζ ∈ Λ, (fun τ : SL(2, ℤ) => act τ ζ) ''
      {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ} := by
    rintro g ⟨hgQ, ζ, hζ, τ, hτ, rfl⟩
    exact Set.mem_biUnion hζ ⟨τ, ⟨hτ, hgQ⟩, rfl⟩
  have hUfin : (⋃ ζ ∈ Λ, (fun τ : SL(2, ℤ) => act τ ζ) ''
      {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}).Finite :=
    hΛfin.biUnion fun ζ hζ => (hTζ ζ hζ).1.image _
  have hRfin : R.Finite := hUfin.subset hRsub
  -- (i) `I ≤ 96 #Λ`
  have hI : R.ncard ≤ 96 * Λ.ncard := by
    calc R.ncard ≤ (⋃ ζ ∈ Λ, (fun τ : SL(2, ℤ) => act τ ζ) ''
          {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}).ncard := Set.ncard_le_ncard hRsub hUfin
      _ ≤ ∑ᶠ ζ ∈ Λ, ((fun τ : SL(2, ℤ) => act τ ζ) ''
          {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}).ncard := hΛfin.ncard_biUnion_le _
      _ ≤ ∑ᶠ ζ ∈ Λ, 96 := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hΛfin, finsum_mem_eq_finite_toFinset_sum _ hΛfin]
          apply Finset.sum_le_sum
          intro ζ hζ
          rw [Set.Finite.mem_toFinset] at hζ
          exact (Set.ncard_image_le (hTζ ζ hζ).1).trans (hTζ ζ hζ).2
      _ = 96 * Λ.ncard := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hΛfin, Finset.sum_const, smul_eq_mul,
            Set.ncard_eq_toFinset_card Λ hΛfin, mul_comm]
  -- (iii) `𝒫 ≤ 192 ∑_ζ #near(ζ)`
  have hrep : ∀ g ∈ R, ∃ ζ ∈ Λ, ∃ τ ∈ T, g = act τ ζ := fun g hg => hg.2
  choose! ζf hζf τf hτf hgf using hrep
  have hinner : ∀ g ∈ R, (∑ᶠ g' ∈ R,
      {γ : Gamma0 q | pointPair (zpt g) ((γ : SL(2, ℤ)) • zpt g') ≤ 1}.ncard) ≤
        2 * nearCount (E * H) (ζf g) := by
    intro g hg
    have := inner_le hN hsq h3 hΛ hT hQN hRfin (hζf g hg) (τf g) (hnear (ζf g) (hζf g hg)).1
    rwa [← hgf g hg] at this
  have hP : pairCount q R ≤ 192 * ∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ := by
    unfold pairCount
    calc (∑ᶠ (g ∈ R) (g' ∈ R),
          {γ : Gamma0 q | pointPair (zpt g) ((γ : SL(2, ℤ)) • zpt g') ≤ 1}.ncard)
        ≤ ∑ᶠ g ∈ R, 2 * nearCount (E * H) (ζf g) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, finsum_mem_eq_finite_toFinset_sum _ hRfin]
          apply Finset.sum_le_sum
          intro g hg
          rw [Set.Finite.mem_toFinset] at hg
          exact hinner g hg
      _ ≤ 192 * ∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hRfin, finsum_mem_eq_finite_toFinset_sum _ hΛfin,
            Finset.mul_sum]
          -- group the `𝔤` according to `ζ(𝔤)`
          rw [← Finset.sum_fiberwise_of_maps_to (g := ζf) (t := hΛfin.toFinset)
            (fun g hg => by
              rw [Set.Finite.mem_toFinset] at hg ⊢; exact hζf g hg)]
          apply Finset.sum_le_sum
          intro ζ hζ
          rw [Set.Finite.mem_toFinset] at hζ
          have hfib : (hRfin.toFinset.filter (fun g => ζf g = ζ)).card ≤ 96 := by
            have hle : (hRfin.toFinset.filter (fun g => ζf g = ζ)).card ≤
                {τ | τ ∈ T ∧ act τ ζ ∈ Qkappa E H d κ}.ncard := by
              rw [← Set.ncard_coe_finset]
              apply Set.ncard_le_ncard_of_injOn τf _ _ (hTζ ζ hζ).1
              · intro g hg
                rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hg
                refine ⟨hτf g hg.1, ?_⟩
                have := hg.1.1
                rwa [hgf g hg.1, hg.2] at this
              · intro g₁ hg₁ g₂ hg₂ h12
                rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hg₁ hg₂
                rw [hgf g₁ hg₁.1, hgf g₂ hg₂.1, hg₁.2, hg₂.2, h12]
            exact hle.trans (hTζ ζ hζ).2
          calc ∑ g ∈ hRfin.toFinset with ζf g = ζ, 2 * nearCount (E * H) (ζf g)
              = ∑ g ∈ hRfin.toFinset with ζf g = ζ, 2 * nearCount (E * H) ζ :=
                Finset.sum_congr rfl fun g hg => by rw [(Finset.mem_filter.1 hg).2]
            _ = (hRfin.toFinset.filter (fun g => ζf g = ζ)).card * (2 * nearCount (E * H) ζ) := by
                rw [Finset.sum_const, smul_eq_mul]
            _ ≤ 96 * (2 * nearCount (E * H) ζ) := Nat.mul_le_mul_right _ hfib
            _ = 192 * nearCount (E * H) ζ := by ring
  refine ⟨hI, ?_, hP, ?_⟩
  · -- (ii)
    calc (Λ.ncard : ℝ) ≤ C₁ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := hΛreal
      _ ≤ max C₁ (192 * C₁ * C₂) * ((E * H : ℤ) : ℝ) ^ (1 / 2 + η) := by
          gcongr
          · exact le_max_left _ _
          · linarith
  · -- (iv)
    have hsum : ((∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ : ℕ) : ℝ) ≤
        Λ.ncard * (C₂ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hΛfin, Set.ncard_eq_toFinset_card Λ hΛfin,
        Nat.cast_sum, ← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro ζ hζ
      rw [Set.Finite.mem_toFinset] at hζ
      exact (hnear ζ hζ).2
    have hNpow : ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) =
        ((E * H : ℤ) : ℝ) ^ (1 + η) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; rw [hεdef]; ring
    have hpow0 : 0 ≤ ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε) := by positivity
    calc (pairCount q R : ℝ) ≤ 192 * ((∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ : ℕ) : ℝ) := by
          exact_mod_cast hP
      _ ≤ 192 * (Λ.ncard * (C₂ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε))) := by gcongr
      _ ≤ 192 * ((C₁ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε)) *
            (C₂ * ((E * H : ℤ) : ℝ) ^ (1 / 2 + ε))) := by gcongr
      _ = 192 * C₁ * C₂ * ((E * H : ℤ) : ℝ) ^ (1 + η) := by rw [← hNpow]; ring
      _ ≤ max C₁ (192 * C₁ * C₂) * ((E * H : ℤ) : ℝ) ^ (1 + η) := by
          gcongr; exact le_max_right _ _

end SymMat

end Triples
