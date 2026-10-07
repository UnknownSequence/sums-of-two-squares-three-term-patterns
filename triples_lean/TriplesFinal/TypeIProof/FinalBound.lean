import TriplesFinal.TypeIProof.FinalAux
import TriplesFinal.TypeIProof.BlockJ0Total
import TriplesFinal.TypeIProof.BlockJ0DI
import TriplesFinal.TypeIProof.DiscreteFamily
import TriplesFinal.Heegner.Reduction

/-!
# The bound for `Ξ_M` with explicit constants

For a set-up `S` (data satisfying (H), `η` and a frequency `M ∈ 𝓜`), the per-`M` bound
`|Ξ_M| ≤ 2K (X/K) Y^(-1/2) L⁹ Q^(6η) 𝔈 √W √𝒫` (`Setup.XiM_le`) is combined with

* the exceptional sums: Lemma 10.5 for part (a) (`exc_a`), Lemma 10.3 for part (b) (`exc_b`);
* the pair count `𝒫 ≪ N^(1+η)` (Lemma 8.4), through reduced orbit representatives;
* the analytic inputs of Lemma 11.3 (`MhBound`, `MhDerivBound`) at `k = 6` and at a `k` with
  `η(k - 3) ≥ 1`, so that the tail constant is `≪ L³` (`tail_const`).

The constant of the spectral side depends on the set-up only through `η` and `C₀ = |C_0|`
(`Kspec_eq`), so it is uniform in the data.

Paper: §12.
-/

namespace Triples

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups ContDiff
open SymMat

/-- The conclusion of `Mh_bound` (Lemma 11.3) for the constant `C`. -/
def MhBound (Cν : ℕ → ℝ) (k : ℕ) (η C : ℝ) : Prop :=
  ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
    ∀ h : ℝ, 0 < h → h * X / K ≤ 4 * (((4 * E * d : ℕ) : ℝ) * X) ^ η →
      (∀ s ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖iteratedDeriv k (fun s => w1 ψ₁ s * ah ψ₂ X K h s) s‖ ≤ C * Lpar E d Δ X η ^ k) ∧
      (∀ w : ℂ, w.re ≤ 0 →
        ‖Mh ψ₁ ψ₂ X K h w‖ ≤ C * Lpar E d Δ X η ^ k * (1 + ‖w‖) ^ (-(k : ℝ)))

/-- The conclusion of `Mh_deriv_bound'` (Lemma 11.3) for the constant `C`. -/
def MhDerivBound (Cν : ℕ → ℝ) (η C : ℝ) : Prop :=
  ∀ (E H d κ : ℕ) (Δ X K : ℝ) (ψ₁ ψ₂ : ℝ → ℂ), HypH Cν E H d κ Δ X K ψ₁ ψ₂ →
    ∀ h : ℝ, 0 < h → h * X / K ≤ 4 * (((4 * E * d : ℕ) : ℝ) * X) ^ η →
      ∀ w : ℂ, w.re = 0 → DifferentiableAt ℝ (fun h' => Mh ψ₁ ψ₂ X K h' w) h ∧
        ‖deriv (fun h' => Mh ψ₁ ψ₂ X K h' w) h‖ ≤ C * X / K

/-- The conclusion of `pair_count` (Lemma 8.4) for the constant `C`. -/
def PairCountBound (η C : ℝ) : Prop :=
  ∀ (E H d κ : ℤ) (q : ℕ), (E = 4 ∨ E = 8) → 0 < H → H % 2 = 1 → Prime d → 3 ≤ d →
    ¬ d ∣ H → (¬ ∃ s : ℤ, E * H = s ^ 2) → (¬ ∃ s : ℤ, E * H = 3 * s ^ 2) →
    (κ = 1 ∨ κ = 3) → (q : ℤ) = 4 * E * d →
    ∀ (Λ : Set SymMat) (T : Set SL(2, ℤ)), IsOrbitReps (E * H) Λ → (∀ ζ ∈ Λ, IsReduced ζ) →
      IsCosetReps q T →
      ((heegnerReps Λ T (Qkappa E H d κ)).ncard ≤ 96 * Λ.ncard ∧
        (Λ.ncard : ℝ) ≤ C * ((E * H : ℤ) : ℝ) ^ (1 / 2 + η) ∧
        pairCount q (heegnerReps Λ T (Qkappa E H d κ)) ≤
          192 * ∑ᶠ ζ ∈ Λ, nearCount (E * H) ζ ∧
        (pairCount q (heegnerReps Λ T (Qkappa E H d κ)) : ℝ) ≤
          C * ((E * H : ℤ) : ℝ) ^ (1 + η))

theorem SpecFam.ExcB_mono {F : SpecFam} {q η C C' : ℝ} (hq : 0 < q) (h : F.ExcB q η C)
    (hC : C ≤ C') : F.ExcB q η C' := by
  intro M hM Y hY1 hY2 a ha
  refine (h M hM Y hY1 hY2 a ha).trans ?_
  have hM0 : 0 < M := by linarith
  have h1 : 0 ≤ (q * M) ^ η := Real.rpow_nonneg (mul_pos hq hM0).le _
  have h2 : 0 ≤ 1 + M / q := by have := div_pos hM0 hq; linarith
  have h3 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : 0 ≤ (q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2 :=
    mul_nonneg (mul_nonneg h1 h2) h3
  calc C * (q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2
      = C * ((q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2) := by ring
    _ ≤ C' * ((q * M) ^ η * (1 + M / q) * ∑ n ∈ Finset.Icc 1 ⌊2 * M⌋₊, ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hC h4
    _ = _ := by ring

namespace Setup

/-- The constant `Kspec` as a function of `C_0`, `η` and the other constants. -/
noncomputable def KspecF (Cν : ℕ → ℝ) (η : ℝ) (Cls : ℝ → ℝ) (KE Cψ Cd C6' CGt Ckt : ℝ) : ℝ :=
  Real.sqrt (2 * (36 * |Cν 0| ^ 2 / η ^ 2 * (24 * Real.cosh Real.pi * Cls η * |Cν 0| ^ 2 + KE) +
      24 * Real.cosh Real.pi * Cls η * (32 * |Cν 0| ^ 2 / Real.pi) ^ 2 *
        ((Nat.ceil (4 / η)).factorial : ℝ))) * Real.sqrt (256 / Real.pi) +
    Real.sqrt (3 * (2 * (21 * ((2 * |Cν 0| ^ 2) ^ 2 + ((Cψ + 1) * (2 * |Cν 0| ^ 2) + 2 * Cd) ^ 2) *
      Cls η) + c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls η * 6 * (2 * Real.pi) ^ 3 * C6' ^ 2)) *
      Real.sqrt (256 / Real.pi) +
    Real.sqrt (3 * (2 * (84 * Cls η * Ckt ^ 2) +
      c₂ * c₅ / (4 * Real.pi ^ 2) * CGt ^ 2 * Cls η * 12 * (2 * Real.pi) ^ 3 * C6' ^ 2) *
        (1024 / Real.pi)) * (1 - Real.sqrt (1 / 2))⁻¹

theorem KspecF_nonneg (Cν : ℕ → ℝ) (η : ℝ) (Cls : ℝ → ℝ) (KE Cψ Cd C6' CGt Ckt : ℝ) :
    0 ≤ KspecF Cν η Cls KE Cψ Cd C6' CGt Ckt := by
  unfold KspecF
  have h : 0 ≤ (1 - Real.sqrt (1 / 2))⁻¹ := by
    have := sqrt_half_lt_one; rw [inv_nonneg]; linarith
  exact add_nonneg (add_nonneg (by positivity) (by positivity))
    (mul_nonneg (Real.sqrt_nonneg _) h)

variable {Cν : ℕ → ℝ} (S : Setup Cν) (ψ₀ : DyadicPartition)

/-- `Kspec` depends on the set-up only through `η` and `C₀`. -/
theorem Kspec_eq (Cls : ℝ → ℝ) (KE Cψ Cd C6' CGt Ckt : ℝ) :
    S.Kspec Cls KE Cψ Cd C6' CGt Ckt = KspecF Cν S.η Cls KE Cψ Cd C6' CGt Ckt := rfl

theorem Kspec_nonneg (Cls : ℝ → ℝ) (KE Cψ Cd C6' CGt Ckt : ℝ) :
    0 ≤ S.Kspec Cls KE Cψ Cd C6' CGt Ckt := by
  rw [S.Kspec_eq]; exact KspecF_nonneg _ _ _ _ _ _ _ _ _

/-! ### The analytic inputs at the set-up -/

theorem hMd_of {Cd : ℝ} (hCd : MhDerivBound Cν S.η Cd) :
    ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ max Cd 0 * S.X / S.K := by
  intro h hh1 hh2 w hw
  obtain ⟨hdiff, hle⟩ := hCd S.E S.H S.d S.κ S.Δ S.X S.K S.ψ₁ S.ψ₂ S.hyp h
    (by linarith [S.M_pos]) (S.hXK_le hh2) w hw
  refine ⟨hdiff, hle.trans ?_⟩
  have := S.X_pos; have := S.K_pos
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem hMk_of {k : ℕ} {Ck : ℝ} (hCk : MhBound Cν k S.η Ck) :
    (∀ h ∈ S.Hs, ∀ ξ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤
      max Ck 0 * S.L ^ k * (1 + |ξ|) ^ (-(k : ℝ))) ∧
    (∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤
      max Ck 0 * S.L ^ k * (1 + |τ|) ^ (-(k : ℝ))) := by
  have key : ∀ h ∈ S.Hs, ∀ w : ℂ, w.re ≤ 0 →
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h w‖ ≤ max Ck 0 * S.L ^ k * (1 + |w.im|) ^ (-(k : ℝ)) := by
    intro h hh w hw
    obtain ⟨hh1, hh2⟩ := S.le_of_mem_Hs hh
    have hpos : (0 : ℝ) < h := by exact_mod_cast hh1
    have := (hCk S.E S.H S.d S.κ S.Δ S.X S.K S.ψ₁ S.ψ₂ S.hyp h hpos (S.hXK_le hh2)).2 w hw
    refine this.trans ?_
    have hL := S.L_pos
    have h1 : (1 + |w.im|) ^ (-(k : ℝ)) ≥ (1 + ‖w‖) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [Complex.abs_im_le_norm w])
        (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have h2 : 0 ≤ (1 + ‖w‖) ^ (-(k : ℝ)) := by positivity
    calc Ck * Lpar S.E S.d S.Δ S.X S.η ^ k * (1 + ‖w‖) ^ (-(k : ℝ))
        ≤ max Ck 0 * S.L ^ k * (1 + ‖w‖) ^ (-(k : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ h2
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Ck 0 * S.L ^ k * (1 + |w.im|) ^ (-(k : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_max_right _ _) (by positivity))
  refine ⟨fun h hh ξ => ?_, fun h hh τ => ?_⟩
  · have := key h hh (-3 / 2 + I * ξ) (by norm_num)
    simpa using this
  · have := key h hh (I * τ) (by simp)
    simpa using this

/-- The tail constant: `C L^k T₁^(-(k-3)) Q ≤ C L³` when `η(k - 3) ≥ 1`. -/
theorem tail_const {k : ℕ} (hk : 1 ≤ S.η * ((k : ℝ) - 3)) {C : ℝ} (hC : 0 ≤ C) :
    C * S.L ^ k * S.T₁ ^ (-((k : ℝ) - 3)) * S.Q ≤ C * S.L ^ 3 := by
  have hL := S.L_pos
  have hx := S.Qη_pos
  have hQ := S.Q_pos
  rw [S.T₁_eq, Real.mul_rpow hx.le hL.le]
  have e1 : S.L ^ k * S.L ^ (-((k : ℝ) - 3)) = S.L ^ 3 := by
    rw [← Real.rpow_natCast S.L k, ← Real.rpow_add hL,
      show (k : ℝ) + -((k : ℝ) - 3) = ((3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have e2 : (S.Q ^ S.η) ^ (-((k : ℝ) - 3)) * S.Q = S.Q ^ (1 - S.η * ((k : ℝ) - 3)) := by
    rw [← Real.rpow_mul hQ.le, ← Real.rpow_add_one hQ.ne']
    congr 1; ring
  have h3 : S.Q ^ (1 - S.η * ((k : ℝ) - 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos S.one_le_Q (by linarith)
  calc C * S.L ^ k * ((S.Q ^ S.η) ^ (-((k : ℝ) - 3)) * S.L ^ (-((k : ℝ) - 3))) * S.Q
      = C * (S.L ^ k * S.L ^ (-((k : ℝ) - 3))) * ((S.Q ^ S.η) ^ (-((k : ℝ) - 3)) * S.Q) := by
        ring
    _ = C * S.L ^ 3 * S.Q ^ (1 - S.η * ((k : ℝ) - 3)) := by rw [e1, e2]
    _ ≤ C * S.L ^ 3 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C * S.L ^ 3 := mul_one _

/-- The pair count bound of Lemma 8.4 at the set-up. -/
theorem hCP_of {C : ℝ} (hC : PairCountBound S.η C) {q : ℕ} (hq : q = 4 * S.E * S.d) :
    ∀ (Λ : Set SymMat) (T : Set SL(2, ℤ)), IsOrbitReps ((S.E : ℤ) * S.H) Λ →
      (∀ ζ ∈ Λ, IsReduced ζ) → IsCosetReps q T →
      (pairCount q (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) : ℝ) ≤
        max C 0 * S.N ^ (1 + S.η) := by
  intro Λ T hΛ hred hT
  have hsq : ¬ ∃ s : ℤ, (S.E : ℤ) * S.H = s ^ 2 := by
    rintro ⟨s, hs⟩
    apply S.hyp.hNsq
    refine ⟨s.natAbs, ?_⟩
    have : ((S.E * S.H : ℕ) : ℤ) = ((s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact hs
    exact_mod_cast this
  have h3 : ¬ ∃ s : ℤ, (S.E : ℤ) * S.H = 3 * s ^ 2 := by
    rintro ⟨s, hs⟩
    apply S.hyp.hN3
    refine ⟨s.natAbs, ?_⟩
    have : ((S.E * S.H : ℕ) : ℤ) = ((3 * s.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact hs
    exact_mod_cast this
  have h := (hC S.E S.H S.d S.κ q
    (by have := S.hyp.hE; omega)
    (by have := S.hyp.hH; omega)
    (by have := S.hyp.hHodd; omega)
    (Nat.prime_iff_prime_int.mp S.hyp.hd)
    (by have := S.hyp.hd3; omega)
    (by exact_mod_cast S.hyp.hdH)
    hsq h3 (by have := S.hyp.hκ; omega) (by rw [hq]; push_cast; ring) Λ T hΛ hred hT).2.2.2
  have eN : (((S.E : ℤ) * S.H : ℤ) : ℝ) = S.N := by unfold Setup.N; push_cast; ring
  rw [eN] at h
  refine h.trans ?_
  have := S.N_pos
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-! ### The exceptional sums -/

/-- **The exceptional sums in part (a)** (Lemma 10.5 with `Y = V`). -/
theorem exc_a {θ : ℝ} (hθ0 : 0 ≤ θ) {q : ℕ} (D : SpectralData q) (hq : (q : ℝ) = S.q)
    {C' : ℝ} (hA : ∀ {n : ℕ} (z : Fin n → ℍ), (D.discFam z).ExcA q θ S.η C')
    {CG : ℝ} (hCG : 0 < CG)
    (hG : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∀ k ≤ 3, ∀ y,
      ‖iteratedDeriv k (S.Gfun ψ₀ s σ) y‖ ≤ CG * S.L ^ k) :
    1 ≤ (1 + S.V / max S.M S.q) ^ θ ∧
    0 ≤ max C' 0 * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η *
      ((1 + S.V / max S.M S.q) ^ θ) ^ 2 * S.W ∧
    max C' 0 * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η *
        ((1 + S.V / max S.M S.q) ^ θ) ^ 2 * S.W ≤
      max C' 0 * CG ^ 2 * 2 *
        (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * ((1 + S.V / max S.M S.q) ^ θ) ^ 2 * S.W) ∧
    ∀ {n : ℕ} (z : Fin n → ℍ), ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ,
      ∫ x in (D.discFam z).exc, S.V ^ (2 * ((D.discFam z).t x).im) *
        ‖S.Ssum ψ₀ ((D.discFam z).ρ x) s σ‖ ^ 2 ∂(D.discFam z).ν ≤
      max C' 0 * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η *
        ((1 + S.V / max S.M S.q) ^ θ) ^ 2 * S.W := by
  have hV := S.V_pos
  have hM := S.M_pos
  have hq0 := S.q_pos
  have hmax : 0 < max S.M S.q := lt_max_of_lt_left hM
  have hb : 1 ≤ 1 + S.V / max S.M S.q := by
    have : 0 ≤ S.V / max S.M S.q := by positivity
    linarith
  set 𝔈 := (1 + S.V / max S.M S.q) ^ θ with h𝔈def
  have h𝔈 : 1 ≤ 𝔈 := Real.one_le_rpow hb hθ0
  have hL := S.L_pos
  have hW := S.W_pos
  set C0 := max C' 0 with hC0def
  have hC0 : 0 ≤ C0 := le_max_right _ _
  refine ⟨h𝔈, by positivity, ?_, ?_⟩
  · have h2 := S.qM_rpow_le
    have hx := S.Qη_pos
    calc C0 * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * 𝔈 ^ 2 * S.W
        = (C0 * CG ^ 2 * S.L ^ 3 * 𝔈 ^ 2 * S.W) * (S.q * S.M) ^ S.η := by ring
      _ ≤ (C0 * CG ^ 2 * S.L ^ 3 * 𝔈 ^ 2 * S.W) * (2 * (S.Q ^ S.η) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · intro n z s hs σ
    have hA' : (D.discFam z).ExcA S.q θ S.η C' := by rw [← hq]; exact hA z
    refine (S.J0_exc ψ₀ (D.discFam z) hA' hCG hG s hs σ).trans ?_
    have e : (1 + S.V / max S.M S.q) ^ (2 * θ) = 𝔈 ^ 2 := by
      rw [h𝔈def, mul_comm, Real.rpow_mul (by linarith), Real.rpow_two]
    rw [e]
    have e1 : C' * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * 𝔈 ^ 2 * (1 + S.M / S.q) * S.M =
        C' * (CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * 𝔈 ^ 2 * S.W) := by
      unfold Setup.W; ring
    have e2 : C0 * CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * 𝔈 ^ 2 * S.W =
        C0 * (CG ^ 2 * S.L ^ 3 * (S.q * S.M) ^ S.η * 𝔈 ^ 2 * S.W) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **The exceptional sums in part (b)** (Lemma 10.3). -/
theorem exc_b {θ : ℝ} (hθ0 : 0 ≤ θ) {q : ℕ} (D : SpectralData q) (hq : (q : ℝ) = S.q)
    (hEB : D.ExceptionalBound θ) {C : ℝ} (hC : 0 ≤ C)
    (hBd : ∀ {n : ℕ} (z : Fin n → ℍ), (D.discFam z).ExcB q S.η C) :
    1 ≤ (1 + S.V / max 1 (S.q / S.M)) ^ θ ∧
    0 ≤ ((1 + S.V / max 1 (S.q / S.M)) ^ θ) ^ 2 *
      (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2)) ∧
    ((1 + S.V / max 1 (S.q / S.M)) ^ θ) ^ 2 *
        (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2)) ≤
      16 * C * S.C₀ ^ 2 *
        (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * ((1 + S.V / max 1 (S.q / S.M)) ^ θ) ^ 2 * S.W) ∧
    ∀ {n : ℕ} (z : Fin n → ℍ), ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ,
      ∫ x in (D.discFam z).exc, S.V ^ (2 * ((D.discFam z).t x).im) *
        ‖S.Ssum ψ₀ ((D.discFam z).ρ x) s σ‖ ^ 2 ∂(D.discFam z).ν ≤
      ((1 + S.V / max 1 (S.q / S.M)) ^ θ) ^ 2 *
        (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2)) := by
  have hV := S.V_pos
  have hM := S.M_pos
  have hq0 := S.q_pos
  have hmax : 0 < max 1 (S.q / S.M) := lt_max_of_lt_left one_pos
  have hb : 1 ≤ 1 + S.V / max 1 (S.q / S.M) := by
    have : 0 ≤ S.V / max 1 (S.q / S.M) := by positivity
    linarith
  set 𝔈 := (1 + S.V / max 1 (S.q / S.M)) ^ θ with h𝔈def
  have h𝔈 : 1 ≤ 𝔈 := Real.one_le_rpow hb hθ0
  have hL := S.L_pos
  have hW := S.W_pos
  have hC₀ := S.C₀_nonneg
  refine ⟨h𝔈, by positivity, ?_, ?_⟩
  · have h2 := S.qM_rpow_le
    have hL3 : 1 ≤ S.L ^ 3 := one_le_pow₀ S.one_le_L
    have hx := S.Qη_pos
    calc 𝔈 ^ 2 * (C * (S.q * S.M) ^ S.η * (1 + S.M / S.q) * (2 * S.M * (2 * S.C₀) ^ 2))
        = (8 * C * S.C₀ ^ 2 * 𝔈 ^ 2 * S.W) * (S.q * S.M) ^ S.η := by unfold Setup.W; ring
      _ ≤ (8 * C * S.C₀ ^ 2 * 𝔈 ^ 2 * S.W) * (2 * (S.Q ^ S.η) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * C * S.C₀ ^ 2 * (1 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W) := by ring
      _ ≤ 16 * C * S.C₀ ^ 2 * (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W) := by gcongr
  · intro n z s hs σ
    have hB' : (D.discFam z).ExcB S.q S.η C := by rw [← hq]; exact hBd z
    refine (S.J0_exc_DI ψ₀ (D.discFam z) hC (D.discFam_ExcBound z hEB) hB' s hs σ).trans ?_
    have e : (1 + S.V / max 1 (S.q / S.M)) ^ (2 * θ) = 𝔈 ^ 2 := by
      rw [h𝔈def, mul_comm, Real.rpow_mul (by linarith), Real.rpow_two]
    rw [e]

/-! ### The bound for `Ξ_M` with the pair count -/

set_option maxHeartbeats 1000000 in
/-- **The bound for `Ξ_M`** with the Heegner representatives built from reduced orbit
representatives and coset representatives, and the pair count bounded by Lemma 8.4. -/
theorem XiM_le_pair {q : ℕ} (D : SpectralData q) (hq : q = 4 * S.E * S.d)
    (hB : BesselAssumptions) (hSC : SelbergConvolution) (hPE : D.PoincareExpansion)
    (hPT : D.PreTrace) (hEC : D.EisensteinContinuous) {Cls : ℝ → ℝ} (hDI2 : D.LargeSieveDI2 Cls)
    {Eexc KE 𝔈 : ℝ} (hKE : 0 ≤ KE) (h𝔈 : 1 ≤ 𝔈) (hE0 : 0 ≤ Eexc)
    (hEle : Eexc ≤ KE * (S.L ^ 3 * (S.Q ^ S.η) ^ 3 * 𝔈 ^ 2 * S.W))
    (hE : ∀ {n : ℕ} (z : Fin n → ℍ), ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ,
      ∫ x in (D.discFam z).exc, S.V ^ (2 * ((D.discFam z).t x).im) *
        ‖S.Ssum ψ₀ ((D.discFam z).ρ x) s σ‖ ^ 2 ∂(D.discFam z).ν ≤ Eexc)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ) {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hMd : ∀ h : ℝ, S.M ≤ h → h ≤ 2 * S.M → ∀ w : ℂ, w.re = 0 →
      DifferentiableAt ℝ (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h ∧
        ‖deriv (fun h' => Mh S.ψ₁ S.ψ₂ S.X S.K h' w) h‖ ≤ Cd * S.X / S.K)
    {C6' : ℝ} (hC6' : 0 ≤ C6')
    (hM6 : ∀ h ∈ S.Hs, ∀ ξ : ℝ,
      ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤ C6' * S.L ^ 6 * (1 + |ξ|) ^ (-(6 : ℝ)))
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k Ck Ckt : ℝ} (hk : 3 ≤ k) (hCk : 0 ≤ Ck)
    (hMk : ∀ h ∈ S.Hs, ∀ τ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (I * τ)‖ ≤ Ck * (1 + |τ|) ^ (-k))
    (hCk0 : 0 ≤ Ck * S.T₁ ^ (-(k - 3))) (hCkt : Ck * S.T₁ ^ (-(k - 3)) * S.Q ≤ Ckt * S.L ^ 3)
    {CP : ℝ} (hCP : ∀ (Λ : Set SymMat) (T : Set SL(2, ℤ)), IsOrbitReps ((S.E : ℤ) * S.H) Λ →
      (∀ ζ ∈ Λ, IsReduced ζ) → IsCosetReps q T →
      (pairCount q (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) : ℝ) ≤ CP * S.N ^ (1 + S.η)) :
    ‖XiM ψ₀ S.E S.H S.d S.κ S.X S.K S.ψ₁ S.ψ₂ S.M‖ ≤
      2 * (S.Kspec Cls KE Cψ Cd C6' CGt Ckt * (S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈) *
        Real.sqrt S.W * Real.sqrt (CP * S.N ^ (1 + S.η))) := by
  have hN : (0 : ℤ) < (S.E : ℤ) * S.H := by
    have := S.E_pos; have := S.hyp.hH; positivity
  obtain ⟨Λ, hΛ, hred⟩ := exists_reduced_orbitReps hN
  obtain ⟨T, hT⟩ := exists_cosetReps q
  have hd2 : (S.d : ℤ) ≠ 2 := by have := S.hyp.hd3; omega
  have hRfin : (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)).Finite :=
    heegnerReps_finite (E := (S.E : ℤ)) (H := S.H) (d := S.d) (κ := S.κ)
      (by rcases S.hyp.hE with h | h <;> rw [h] <;> norm_num) (by exact_mod_cast S.hyp.hH)
      (Nat.prime_iff_prime_int.mp S.hyp.hd) (by exact_mod_cast S.hyp.hd.pos) hd2
      (by exact_mod_cast S.hyp.hdH) (by rw [hq]; push_cast; ring) hΛ hT
  have hUj : ∀ j, D.Uj (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) j =
      ∑ i, D.u j ((fun i : Fin hRfin.toFinset.card =>
        zpt (hRfin.toFinset.equivFin.symm i : SymMat)) i) :=
    fun j => finsum_mem_eq_sum_enum hRfin _
  have hUs : ∀ 𝔰 r, D.Us (heegnerReps Λ T (Qkappa S.E S.H S.d S.κ)) 𝔰 r =
      ∑ i, D.Eis 𝔰 r ((fun i : Fin hRfin.toFinset.card =>
        zpt (hRfin.toFinset.equivFin.symm i : SymMat)) i) :=
    fun 𝔰 r => finsum_mem_eq_sum_enum hRfin _
  have h := S.XiM_le ψ₀ D hq hB hSC hPE hPT hEC hDI2 hΛ hT
    (fun i : Fin hRfin.toFinset.card => zpt (hRfin.toFinset.equivFin.symm i : SymMat)) hUj hUs
    hKE h𝔈 hE0 hEle (hE _) hCψ hψ hCd hMd hC6' hM6 hGt hk hCk hMk hCk0 hCkt
  rw [← pairCount_eq_pairCountPts hRfin] at h
  refine h.trans ?_
  have hP := hCP Λ T hΛ hred hT
  have hK := S.Kspec_nonneg Cls KE Cψ Cd C6' CGt Ckt
  have h𝔈0 : 0 ≤ 𝔈 := by linarith
  have hZ : 0 ≤ S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈 := by
    have := S.Bk_pos; have := S.L_pos; have := S.Qη_pos
    exact mul_nonneg (by positivity) h𝔈0
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hP)
    (mul_nonneg (mul_nonneg hK hZ) (Real.sqrt_nonneg _))

/-! ### The optimisation in `M` -/

/-- `V = (qX)^η E K / (M √(EH))`. -/
theorem V_eq' : S.V = (4 * (S.E : ℝ) * S.d * S.X) ^ S.η * S.E * S.K /
    (S.M * Real.sqrt ((S.E : ℝ) * S.H)) := by
  have eQ : S.Q = 4 * (S.E : ℝ) * S.d * S.X := by unfold Setup.Q; rw [S.q_eq]
  rw [S.V_eq, S.Y_eq, eQ]
  unfold Setup.N
  push_cast
  have hM := S.M_pos.ne'
  have hE : (S.E : ℝ) ≠ 0 := by have := S.E_ge; positivity
  have hK := S.K_pos.ne'
  have hs : Real.sqrt ((S.E : ℝ) * S.H) ≠ 0 := by
    have := S.E_ge; have := S.H_ge
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp

/-- Lemma 12.1 for part (a) at the set-up. -/
theorem Mopt_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    S.X * S.K ^ (-(1 / 2 : ℝ)) * Real.sqrt S.W * (1 + S.V / max S.M S.q) ^ θ ≤
      6 * S.Q ^ S.η * Real.sqrt S.X * (1 + S.X / (S.d * Real.sqrt S.H)) ^ θ := by
  have hE1 : (1 : ℝ) ≤ S.E := by linarith [S.E_ge]
  have hd1 : (1 : ℝ) ≤ S.d := by linarith [S.d_ge]
  have hX : Real.sqrt ((S.E : ℝ) * S.H) ≤ S.X := by
    have := S.hyp.hX; push_cast at this; exact this
  have hKq : S.K ≤ 4 * (S.E : ℝ) * S.d * S.X := by
    have := S.hyp.hKq; push_cast at this; exact this
  have hM2 : S.M ≤ 2 * ((4 * (S.E : ℝ) * S.d * S.X) ^ S.η * S.K / S.X) := by
    have := S.hM2; unfold h₀ at this; push_cast at this; exact this
  have h := (M_optimisation hE1 S.H_ge hd1 hX S.K_ge hKq S.hη hθ0 hθ.le S.hM1 hM2).1
  have eQ : S.Q = 4 * (S.E : ℝ) * S.d * S.X := by unfold Setup.Q; rw [S.q_eq]
  have eW : S.W = (1 + S.M / (4 * (S.E : ℝ) * S.d)) * S.M := by unfold Setup.W; rw [S.q_eq]
  rw [S.V_eq', eW, eQ, S.q_eq]
  exact h

/-- Lemma 12.1 for part (b) at the set-up. -/
theorem Mopt_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) :
    S.X * S.K ^ (-(1 / 2 : ℝ)) * Real.sqrt S.W * (1 + S.V / max 1 (S.q / S.M)) ^ θ ≤
      6 * (S.Q ^ S.η) ^ 2 * Real.sqrt S.X * (1 + S.K / (S.d * Real.sqrt S.H)) ^ θ := by
  have hE1 : (1 : ℝ) ≤ S.E := by linarith [S.E_ge]
  have hd1 : (1 : ℝ) ≤ S.d := by linarith [S.d_ge]
  have hX : Real.sqrt ((S.E : ℝ) * S.H) ≤ S.X := by
    have := S.hyp.hX; push_cast at this; exact this
  have hKq : S.K ≤ 4 * (S.E : ℝ) * S.d * S.X := by
    have := S.hyp.hKq; push_cast at this; exact this
  have hM2 : S.M ≤ 2 * ((4 * (S.E : ℝ) * S.d * S.X) ^ S.η * S.K / S.X) := by
    have := S.hM2; unfold h₀ at this; push_cast at this; exact this
  have h := (M_optimisation hE1 S.H_ge hd1 hX S.K_ge hKq S.hη hθ0 hθ.le S.hM1 hM2).2
  have eQ : S.Q = 4 * (S.E : ℝ) * S.d * S.X := by unfold Setup.Q; rw [S.q_eq]
  have eW : S.W = (1 + S.M / (4 * (S.E : ℝ) * S.d)) * S.M := by unfold Setup.W; rw [S.q_eq]
  rw [S.V_eq', eW, ← S.Qη2, eQ, S.q_eq]
  exact h

/-- Combining the bound for `Ξ_M` with `(X/K) Y^(-1/2) = E^(1/2) N^(-1/4) X K^(-1/2)` and the
optimisation in `M`. -/
theorem clean_common {K0 CP 𝔈 R : ℝ} (hK0 : 0 ≤ K0) (hCP : 0 ≤ CP)
    (hR : S.X * S.K ^ (-(1 / 2 : ℝ)) * Real.sqrt S.W * 𝔈 ≤ R) :
    2 * (K0 * (S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈) * Real.sqrt S.W *
        Real.sqrt (CP * S.N ^ (1 + S.η))) ≤
      2 * K0 * Real.sqrt CP * Real.sqrt S.E * S.L ^ 9 * (S.Q ^ S.η) ^ 6 *
        S.N ^ (1 / 4 + S.η / 2) * R := by
  have hN := S.N_pos
  have hsq : Real.sqrt (CP * S.N ^ (1 + S.η)) = Real.sqrt CP * S.N ^ ((1 + S.η) / 2) := by
    rw [Real.sqrt_mul hCP, Real.sqrt_eq_rpow (S.N ^ (1 + S.η)), ← Real.rpow_mul hN.le,
      show (1 + S.η) * (1 / 2 : ℝ) = (1 + S.η) / 2 by ring]
  have hNN : S.N ^ (-(1 / 4 : ℝ)) * S.N ^ ((1 + S.η) / 2) = S.N ^ (1 / 4 + S.η / 2) := by
    rw [← Real.rpow_add hN]; congr 1; ring
  have e : 2 * (K0 * (S.Bk * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * 𝔈) * Real.sqrt S.W *
        Real.sqrt (CP * S.N ^ (1 + S.η))) =
      2 * K0 * Real.sqrt CP * Real.sqrt S.E * S.L ^ 9 * (S.Q ^ S.η) ^ 6 *
        (S.N ^ (-(1 / 4 : ℝ)) * S.N ^ ((1 + S.η) / 2)) *
        (S.X * S.K ^ (-(1 / 2 : ℝ)) * Real.sqrt S.W * 𝔈) := by
    rw [hsq, S.Bk_eq]; ring
  rw [e, hNN]
  apply mul_le_mul_of_nonneg_left hR
  have := S.L_pos; have := S.Qη_pos
  positivity

/-- The constants in terms of `Δ`, `Q^η` and `H`: `E^(1/2) ≤ 3`, `L ≤ 9ΔQ^η`, `N ≤ 8H`. -/
theorem to_raw {K0 CP A : ℝ} (hK0 : 0 ≤ K0) (hA : 0 ≤ A) :
    2 * K0 * Real.sqrt CP * Real.sqrt S.E * S.L ^ 9 * (S.Q ^ S.η) ^ 6 * S.N ^ (1 / 4 + S.η / 2) *
        (6 * (S.Q ^ S.η) ^ 2 * Real.sqrt S.X * A) ≤
      12 * K0 * Real.sqrt CP * 3 * 9 ^ 9 * 8 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 17 *
        (S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2) * Real.sqrt S.X * A := by
  have hL := S.L_pos
  have hx := S.Qη_pos
  have hN := S.N_pos
  have hH : (0 : ℝ) < S.H := by linarith [S.H_ge]
  have hΔ : 0 ≤ S.Δ := by linarith [S.Δ_ge]
  have h1 : Real.sqrt S.E ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [S.E_le]
  have h2 : S.L ^ 9 ≤ 9 ^ 9 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 9 := by
    calc S.L ^ 9 ≤ (9 * S.Δ * S.Q ^ S.η) ^ 9 := pow_le_pow_left₀ hL.le S.L_le 9
      _ = 9 ^ 9 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 9 := by ring
  have h3 : S.N ^ (1 / 4 + S.η / 2) ≤
      8 * ((S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2)) := by
    have hN8 : S.N ≤ 8 * S.H := by
      unfold Setup.N; push_cast; nlinarith [S.E_le, S.H_ge]
    have hr0 : 0 ≤ 1 / 4 + S.η / 2 := by have := S.hη; positivity
    have hr1 : 1 / 4 + S.η / 2 ≤ 1 := by have := S.hη1; linarith
    calc S.N ^ (1 / 4 + S.η / 2) ≤ (8 * S.H) ^ (1 / 4 + S.η / 2) :=
          Real.rpow_le_rpow hN.le hN8 hr0
      _ = 8 ^ (1 / 4 + S.η / 2) * (S.H : ℝ) ^ (1 / 4 + S.η / 2) :=
          Real.mul_rpow (by norm_num) hH.le
      _ ≤ 8 * (S.H : ℝ) ^ (1 / 4 + S.η / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (8 : ℝ) ^ (1 / 4 + S.η / 2) ≤ 8 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1
            _ = 8 := Real.rpow_one 8
      _ = 8 * ((S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2)) := by
          rw [Real.rpow_add hH]
  have e : 2 * K0 * Real.sqrt CP * Real.sqrt S.E * S.L ^ 9 * (S.Q ^ S.η) ^ 6 *
        S.N ^ (1 / 4 + S.η / 2) * (6 * (S.Q ^ S.η) ^ 2 * Real.sqrt S.X * A) =
      (12 * K0 * Real.sqrt CP * Real.sqrt S.X * A * (S.Q ^ S.η) ^ 8) *
        (Real.sqrt S.E * S.L ^ 9 * S.N ^ (1 / 4 + S.η / 2)) := by ring
  have e' : 12 * K0 * Real.sqrt CP * 3 * 9 ^ 9 * 8 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 17 *
        (S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2) * Real.sqrt S.X * A =
      (12 * K0 * Real.sqrt CP * Real.sqrt S.X * A * (S.Q ^ S.η) ^ 8) *
        (3 * (9 ^ 9 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 9) *
          (8 * ((S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2)))) := by ring
  rw [e, e']
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr

/-! ### The bounds for `Ξ_M` in parts (a) and (b) -/

set_option maxHeartbeats 1000000 in
/-- **The bound for `Ξ_M` in part (a).** -/
theorem XiM_bound_a {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) {Cls : ℝ → ℝ} {q : ℕ} (D : SpectralData q)
    (hq : q = 4 * S.E * S.d) (hPE : D.PoincareExpansion) (hPT : D.PreTrace)
    (hDI2 : D.LargeSieveDI2 Cls) (hEC : D.EisensteinContinuous)
    {C' : ℝ} (hA : ∀ {n : ℕ} (z : Fin n → ℍ), (D.discFam z).ExcA q θ S.η C')
    {CG : ℝ} (hCG : 0 < CG) (hG : ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ σ : ℝ, ∀ k ≤ 3, ∀ y,
      ‖iteratedDeriv k (S.Gfun ψ₀ s σ) y‖ ≤ CG * S.L ^ k)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ)
    {Cd : ℝ} (hCd : MhDerivBound Cν S.η Cd) {C6 : ℝ} (hC6 : MhBound Cν 6 S.η C6)
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k : ℕ} (hk : 1 ≤ S.η * ((k : ℝ) - 3)) {Ck : ℝ} (hCk : MhBound Cν k S.η Ck)
    {CP : ℝ} (hCP : PairCountBound S.η CP) :
    ‖XiM ψ₀ S.E S.H S.d S.κ S.X S.K S.ψ₁ S.ψ₂ S.M‖ ≤
      12 * KspecF Cν S.η Cls (max C' 0 * CG ^ 2 * 2) Cψ (max Cd 0) (max C6 0) CGt (max Ck 0) *
        Real.sqrt (max CP 0) * 3 * 9 ^ 9 * 8 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 17 *
        (S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2) * Real.sqrt S.X *
        (1 + S.X / (S.d * Real.sqrt S.H)) ^ θ := by
  have hq' : (q : ℝ) = S.q := by rw [hq]; rfl
  obtain ⟨h𝔈, hE0, hEle, hE⟩ := S.exc_a ψ₀ hθ0 D hq' hA hCG hG
  have hMd := S.hMd_of hCd
  obtain ⟨hM6, -⟩ := S.hMk_of hC6
  obtain ⟨-, hMk⟩ := S.hMk_of hCk
  have hM6' : ∀ h ∈ S.Hs, ∀ ξ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤
      max C6 0 * S.L ^ 6 * (1 + |ξ|) ^ (-(6 : ℝ)) := by
    intro h hh ξ
    have := hM6 h hh ξ
    rwa [show ((6 : ℕ) : ℝ) = 6 by norm_num] at this
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
    by_contra hcon
    push Not at hcon
    have : S.η * ((k : ℝ) - 3) < 0 := mul_neg_of_pos_of_neg S.hη (by linarith)
    linarith
  have hL := S.L_pos
  have hCk0 : 0 ≤ max Ck 0 * S.L ^ k * S.T₁ ^ (-((k : ℝ) - 3)) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (Real.rpow_nonneg S.T₁_pos.le _)
  have hCG2 : 0 ≤ max C' 0 * CG ^ 2 * 2 := by
    have := le_max_right C' 0; positivity
  have h := S.XiM_le_pair ψ₀ D hq hB hSC hPE hPT hEC hDI2 hCG2 h𝔈 hE0 hEle hE hCψ hψ
    (le_max_right _ _) hMd (le_max_right _ _) hM6' hGt (k := (k : ℝ)) hk3
    (mul_nonneg (le_max_right _ _) (by positivity)) hMk hCk0
    (S.tail_const hk (le_max_right _ _)) (S.hCP_of hCP hq)
  refine h.trans ?_
  rw [S.Kspec_eq]
  have hK0 := KspecF_nonneg Cν S.η Cls (max C' 0 * CG ^ 2 * 2) Cψ (max Cd 0) (max C6 0) CGt
    (max Ck 0)
  have hA0 : 0 ≤ (1 + S.X / (S.d * Real.sqrt S.H)) ^ θ := by
    have := S.X_pos; have := S.d_ge
    exact Real.rpow_nonneg (by positivity) _
  have hR : S.X * S.K ^ (-(1 / 2 : ℝ)) * Real.sqrt S.W * (1 + S.V / max S.M S.q) ^ θ ≤
      6 * (S.Q ^ S.η) ^ 2 * Real.sqrt S.X * (1 + S.X / (S.d * Real.sqrt S.H)) ^ θ := by
    refine (S.Mopt_a hθ0 hθ).trans ?_
    have hx2 : S.Q ^ S.η ≤ (S.Q ^ S.η) ^ 2 := by
      have := S.Qη_ge; nlinarith
    have := Real.sqrt_nonneg S.X
    gcongr
  exact (S.clean_common hK0 (le_max_right _ _) hR).trans (S.to_raw hK0 hA0)

set_option maxHeartbeats 1000000 in
/-- **The bound for `Ξ_M` in part (b).** -/
theorem XiM_bound_b {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hB : BesselAssumptions)
    (hSC : SelbergConvolution) {Cls : ℝ → ℝ} {q : ℕ} (D : SpectralData q)
    (hq : q = 4 * S.E * S.d) (hPE : D.PoincareExpansion) (hPT : D.PreTrace)
    (hDI2 : D.LargeSieveDI2 Cls) (hDI5 : D.LargeSieveDI5 Cls) (hEB : D.ExceptionalBound θ)
    (hEC : D.EisensteinContinuous)
    {Cψ : ℝ} (hCψ : 0 ≤ Cψ) (hψ : ∀ y, |deriv ψ₀.ψ₀ y| ≤ Cψ)
    {Cd : ℝ} (hCd : MhDerivBound Cν S.η Cd) {C6 : ℝ} (hC6 : MhBound Cν 6 S.η C6)
    {CGt : ℝ} (hGt : ∀ t ξ : ℝ, ‖Gt t (-3 / 2 + I * ξ)‖ ≤
      CGt * Real.exp (-Real.pi * |t| / 2) * (1 + |ξ + t|) ^ (-(5 : ℝ) / 4) *
        (1 + |ξ - t|) ^ (-(5 : ℝ) / 4))
    {k : ℕ} (hk : 1 ≤ S.η * ((k : ℝ) - 3)) {Ck : ℝ} (hCk : MhBound Cν k S.η Ck)
    {CP : ℝ} (hCP : PairCountBound S.η CP) :
    ‖XiM ψ₀ S.E S.H S.d S.κ S.X S.K S.ψ₁ S.ψ₂ S.M‖ ≤
      12 * KspecF Cν S.η Cls (16 * max (Cls S.η) 0 * |Cν 0| ^ 2) Cψ (max Cd 0) (max C6 0) CGt
        (max Ck 0) * Real.sqrt (max CP 0) * 3 * 9 ^ 9 * 8 * S.Δ ^ 9 * (S.Q ^ S.η) ^ 17 *
        (S.H : ℝ) ^ (1 / 4 : ℝ) * (S.H : ℝ) ^ (S.η / 2) * Real.sqrt S.X *
        (1 + S.K / (S.d * Real.sqrt S.H)) ^ θ := by
  have hq' : (q : ℝ) = S.q := by rw [hq]; rfl
  have hq0 : (0 : ℝ) < q := by rw [hq']; exact S.q_pos
  have hBd : ∀ {n : ℕ} (z : Fin n → ℍ), (D.discFam z).ExcB q S.η (max (Cls S.η) 0) :=
    fun z => SpecFam.ExcB_mono hq0 (D.discFam_ExcB z hDI5 S.hη) (le_max_left _ _)
  obtain ⟨h𝔈, hE0, hEle, hE⟩ := S.exc_b ψ₀ hθ0 D hq' hEB (le_max_right _ _) hBd
  have hMd := S.hMd_of hCd
  obtain ⟨hM6, -⟩ := S.hMk_of hC6
  obtain ⟨-, hMk⟩ := S.hMk_of hCk
  have hM6' : ∀ h ∈ S.Hs, ∀ ξ : ℝ, ‖Mh S.ψ₁ S.ψ₂ S.X S.K h (-3 / 2 + I * ξ)‖ ≤
      max C6 0 * S.L ^ 6 * (1 + |ξ|) ^ (-(6 : ℝ)) := by
    intro h hh ξ
    have := hM6 h hh ξ
    rwa [show ((6 : ℕ) : ℝ) = 6 by norm_num] at this
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by
    by_contra hcon
    push Not at hcon
    have : S.η * ((k : ℝ) - 3) < 0 := mul_neg_of_pos_of_neg S.hη (by linarith)
    linarith
  have hL := S.L_pos
  have hCk0 : 0 ≤ max Ck 0 * S.L ^ k * S.T₁ ^ (-((k : ℝ) - 3)) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (Real.rpow_nonneg S.T₁_pos.le _)
  have hKE : 0 ≤ 16 * max (Cls S.η) 0 * S.C₀ ^ 2 := by
    have := le_max_right (Cls S.η) 0; positivity
  have h := S.XiM_le_pair ψ₀ D hq hB hSC hPE hPT hEC hDI2 hKE h𝔈 hE0 hEle hE hCψ hψ
    (le_max_right _ _) hMd (le_max_right _ _) hM6' hGt (k := (k : ℝ)) hk3
    (mul_nonneg (le_max_right _ _) (by positivity)) hMk hCk0
    (S.tail_const hk (le_max_right _ _)) (S.hCP_of hCP hq)
  refine h.trans ?_
  rw [S.Kspec_eq]
  have hK0 := KspecF_nonneg Cν S.η Cls (16 * max (Cls S.η) 0 * S.C₀ ^ 2) Cψ (max Cd 0)
    (max C6 0) CGt (max Ck 0)
  have hA0 : 0 ≤ (1 + S.K / (S.d * Real.sqrt S.H)) ^ θ := by
    have := S.K_pos; have := S.d_ge
    exact Real.rpow_nonneg (by positivity) _
  exact (S.clean_common hK0 (le_max_right _ _) (S.Mopt_b hθ0 hθ)).trans (S.to_raw hK0 hA0)

end Setup

end Triples
