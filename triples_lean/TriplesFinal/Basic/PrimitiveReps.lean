import TriplesFinal.Basic.Thue
import TriplesFinal.Basic.RootCount

/-!
# Primitive representations: `r*(m) = 4 ϱ₁(m)`

A representation `m = x² + y²` is primitive if `gcd(x, y) = 1`. Each primitive representation
determines a root `ν mod m` of `ν² + 1 ≡ 0 (mod m)` by `x ≡ νy (mod m)` (`rootOf`). Conversely,
every root comes from a primitive representation (Thue's lemma), and the primitive
representations attached to a given root are exactly the four rotations `(x, y)`, `(-y, x)`,
`(-x, -y)`, `(y, -x)` of one of them. Hence the number `r*(m)` of primitive representations
equals `4 ϱ₁(m)`, where `ϱ₁(m) = #{ν mod m : ν² + 1 ≡ 0 (mod m)}` (`rho 1 m`).

Paper: §1, Notation (Jacobi's formula for `r(n)`).
-/

namespace Triples

/-- `|x| ≤ x²` for integers. -/
theorem abs_le_sq (x : ℤ) : |x| ≤ x ^ 2 := by
  rcases eq_or_ne x 0 with h0 | h0
  · simp [h0]
  · have := Int.one_le_abs h0
    nlinarith [sq_abs x]

/-- The primitive representations `x² + y² = m`, `gcd(x, y) = 1`. -/
def primReps (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc (-(m : ℤ)) m)).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = m ∧ Int.gcd p.1 p.2 = 1)

theorem mem_primReps {m : ℕ} {x y : ℤ} :
    (x, y) ∈ primReps m ↔ x ^ 2 + y ^ 2 = m ∧ Int.gcd x y = 1 := by
  simp only [primReps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  rintro ⟨h, -⟩
  have hx := abs_le_sq x
  have hy := abs_le_sq y
  have hx2 := sq_nonneg x
  have hy2 := sq_nonneg y
  refine ⟨abs_le.1 (by linarith), abs_le.1 (by linarith)⟩

/-- **Existence.** For `m ∣ ν² + 1` there is a primitive representation with `x ≡ νy (mod m)`. -/
theorem exists_primRep (m : ℕ) (hm : 1 ≤ m) {ν : ℤ} (hν : (m : ℤ) ∣ ν ^ 2 + 1) :
    ∃ x y : ℤ, (x, y) ∈ primReps m ∧ (m : ℤ) ∣ x - ν * y := by
  obtain ⟨x, y, hne, hlt, hdvd⟩ := thue m hm ν
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  have hpos : 0 < x ^ 2 + y ^ 2 := by
    rcases hne with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg y]
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg x]
  obtain ⟨k, hk⟩ := dvd_sum_sq hdvd hν
  have hk1 : k = 1 := by
    have h1 : 0 < k := by
      by_contra h; push Not at h; nlinarith
    have h2 : k < 2 := by
      by_contra h; push Not at h; nlinarith
    omega
  rw [hk1, mul_one] at hk
  refine ⟨x, y, mem_primReps.2 ⟨hk, ?_⟩, hdvd⟩
  -- primitivity
  set g := Int.gcd x y with hg
  have hgpos : 0 < g := Int.gcd_pos_iff.2 hne
  have hg0 : (0 : ℤ) < g := by exact_mod_cast hgpos
  obtain ⟨x₁, hx₁⟩ : (g : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y₁, hy₁⟩ : (g : ℤ) ∣ y := Int.gcd_dvd_right x y
  set m₁ := x₁ ^ 2 + y₁ ^ 2 with hm₁
  have hm' : (m : ℤ) = g ^ 2 * m₁ := by rw [← hk, hx₁, hy₁]; ring
  have hm₁pos : 0 < m₁ := by
    by_contra h; push Not at h
    have : (m : ℤ) ≤ 0 := by rw [hm']; nlinarith
    linarith
  have h1 : (g : ℤ) * m₁ ∣ x₁ - ν * y₁ := by
    have : (g : ℤ) * (g * m₁) ∣ (g : ℤ) * (x₁ - ν * y₁) := by
      have e : (g : ℤ) * (x₁ - ν * y₁) = x - ν * y := by rw [hx₁, hy₁]; ring
      rw [e, show (g : ℤ) * (g * m₁) = m by rw [hm']; ring]
      exact hdvd
    exact (mul_dvd_mul_iff_left hg0.ne').1 this
  have h2 : (g : ℤ) * m₁ ∣ ν ^ 2 + 1 :=
    (Dvd.intro g (by rw [hm']; ring) : (g : ℤ) * m₁ ∣ m).trans hν
  have h3 := dvd_sum_sq h1 h2
  have h4 := Int.le_of_dvd hm₁pos h3
  have h5 : (g : ℤ) ≤ 1 := by nlinarith
  omega

/-- The four rotations `(x, y), (-y, x), (-x, -y), (y, -x)` (multiplication by the units of
`ℤ[i]`). -/
def rot4 (x y : ℤ) : Finset (ℤ × ℤ) := {(x, y), (-y, x), (-x, -y), (y, -x)}

theorem card_rot4 {x y : ℤ} (h : x ≠ 0 ∨ y ≠ 0) : (rot4 x y).card = 4 := by
  unfold rot4
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton, Prod.mk.injEq]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega

/-- **The fibre.** All primitive representations with `x ≡ νy (mod m)` are the rotations of one
of them. -/
theorem fiber_eq_rot4 {m : ℕ} (hm : 1 ≤ m) {ν : ℤ} (hν : (m : ℤ) ∣ ν ^ 2 + 1) {x₀ y₀ : ℤ}
    (h₀ : (x₀, y₀) ∈ primReps m) (h₀ν : (m : ℤ) ∣ x₀ - ν * y₀) :
    (primReps m).filter (fun p => (m : ℤ) ∣ p.1 - ν * p.2) = rot4 x₀ y₀ := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  obtain ⟨hsum₀, hgcd₀⟩ := mem_primReps.1 h₀
  -- `y₀ + ν x₀ ≡ 0`
  have hrot : (m : ℤ) ∣ y₀ + ν * x₀ := by
    have e : y₀ + ν * x₀ = ν * (x₀ - ν * y₀) + (ν ^ 2 + 1) * y₀ := by ring
    rw [e]; exact dvd_add (dvd_mul_of_dvd_right h₀ν _) (dvd_mul_of_dvd_left hν _)
  ext ⟨x', y'⟩
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpν⟩
    obtain ⟨hsum', -⟩ := mem_primReps.1 hp
    -- `u = (x₀x' + y₀y')/m`, `v = (x₀y' - x'y₀)/m`
    have hu : (m : ℤ) ∣ x₀ * x' + y₀ * y' := by
      have e : x₀ * x' + y₀ * y' = x' * (x₀ - ν * y₀) + y₀ * (ν * (x' - ν * y') + (ν ^ 2 + 1) * y') := by
        ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right h₀ν _) (dvd_mul_of_dvd_right (dvd_add
        (dvd_mul_of_dvd_right hpν _) (dvd_mul_of_dvd_left hν _)) _)
    have hv : (m : ℤ) ∣ x₀ * y' - x' * y₀ := by
      have e : x₀ * y' - x' * y₀ = y' * (x₀ - ν * y₀) - y₀ * (x' - ν * y') := by ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right h₀ν _) (dvd_mul_of_dvd_right hpν _)
    obtain ⟨u, hu'⟩ := hu
    obtain ⟨v, hv'⟩ := hv
    have huv : u ^ 2 + v ^ 2 = 1 := by
      have e : (x₀ * x' + y₀ * y') ^ 2 + (x₀ * y' - x' * y₀) ^ 2 =
          (x₀ ^ 2 + y₀ ^ 2) * (x' ^ 2 + y' ^ 2) := by ring
      rw [hu', hv', hsum₀, hsum'] at e
      have : (m : ℤ) ^ 2 * (u ^ 2 + v ^ 2) = (m : ℤ) ^ 2 * 1 := by linear_combination e
      exact mul_left_cancel₀ (by positivity) this
    have hx' : x' = u * x₀ - v * y₀ := by
      have : (m : ℤ) * x' = (m : ℤ) * (u * x₀ - v * y₀) := by
        have e : x' * (x₀ ^ 2 + y₀ ^ 2) = x₀ * (x₀ * x' + y₀ * y') - y₀ * (x₀ * y' - x' * y₀) := by
          ring
        rw [hsum₀, hu', hv'] at e
        linear_combination e
      exact mul_left_cancel₀ hm0.ne' this
    have hy' : y' = u * y₀ + v * x₀ := by
      have : (m : ℤ) * y' = (m : ℤ) * (u * y₀ + v * x₀) := by
        have e : y' * (x₀ ^ 2 + y₀ ^ 2) = y₀ * (x₀ * x' + y₀ * y') + x₀ * (x₀ * y' - x' * y₀) := by
          ring
        rw [hsum₀, hu', hv'] at e
        linear_combination e
      exact mul_left_cancel₀ hm0.ne' this
    have hu1 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg v]
    have hv1 : v ^ 2 ≤ 1 := by nlinarith [sq_nonneg u]
    have hu2 : -1 ≤ u ∧ u ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (u + 1), sq_nonneg (u - 1)]
    have hv2 : -1 ≤ v ∧ v ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (v + 1), sq_nonneg (v - 1)]
    unfold rot4
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    have hcases : (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 1) ∨ (u = -1 ∧ v = 0) ∨ (u = 0 ∧ v = -1) := by
      have hu3 : u = -1 ∨ u = 0 ∨ u = 1 := by omega
      have hv3 : v = -1 ∨ v = 0 ∨ v = 1 := by omega
      clear hu' hv' hx' hy'
      rcases hu3 with rfl | rfl | rfl <;> rcases hv3 with rfl | rfl | rfl <;> revert huv <;> norm_num
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; constructor <;> linarith
    · right; left; constructor <;> linarith
    · right; right; left; constructor <;> linarith
    · right; right; right; constructor <;> linarith
  · intro hp
    unfold rot4 at hp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hp
    rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
    · exact ⟨h₀, h₀ν⟩
    · refine ⟨mem_primReps.2 ⟨by linarith, ?_⟩, ?_⟩
      · rw [Int.gcd_comm, Int.gcd_neg]; exact hgcd₀
      · have : -y₀ - ν * x₀ = -(y₀ + ν * x₀) := by ring
        rw [this]; exact dvd_neg.2 hrot
    · refine ⟨mem_primReps.2 ⟨by linarith, ?_⟩, ?_⟩
      · rw [Int.gcd_neg, Int.neg_gcd]; exact hgcd₀
      · have : -x₀ - ν * -y₀ = -(x₀ - ν * y₀) := by ring
        rw [this]; exact dvd_neg.2 h₀ν
    · refine ⟨mem_primReps.2 ⟨by linarith, ?_⟩, ?_⟩
      · rw [Int.gcd_neg, Int.gcd_comm]; exact hgcd₀
      · have : y₀ - ν * -x₀ = y₀ + ν * x₀ := by ring
        rw [this]; exact hrot

/-- For a primitive representation, `y` is prime to `m`. -/
theorem isCoprime_of_primRep {m : ℕ} {x y : ℤ} (h : (x, y) ∈ primReps m) : IsCoprime y m := by
  obtain ⟨hsum, hgcd⟩ := mem_primReps.1 h
  have h1 : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.2 hgcd
  have h2 : IsCoprime y (x ^ 2 + y * y) := (h1.symm.pow_right (n := 2)).add_mul_left_right y
  rw [show x ^ 2 + y * y = m by rw [← hsum]; ring] at h2
  exact h2

/-- The root `ν mod m` attached to a primitive representation: `x ≡ νy (mod m)`. -/
def rootOf (m : ℕ) (p : ℤ × ℤ) : ℕ := (p.1 * Int.gcdA p.2 m % m).toNat

theorem rootOf_spec {m : ℕ} (hm : 1 ≤ m) {p : ℤ × ℤ} (hp : p ∈ primReps m) :
    rootOf m p < m ∧ (m : ℤ) ∣ p.1 - (rootOf m p : ℤ) * p.2 ∧
      (m : ℤ) ∣ ((rootOf m p : ℕ) : ℤ) ^ 2 + 1 := by
  obtain ⟨x, y⟩ := p
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  have hcop := isCoprime_of_primRep hp
  have hgcd : Int.gcd y m = 1 := Int.isCoprime_iff_gcd_eq_one.1 hcop
  have hbez := Int.gcd_eq_gcd_ab y m
  rw [hgcd] at hbez
  set A := Int.gcdA y m
  have hν : ((rootOf m (x, y) : ℕ) : ℤ) = x * A % m :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm0.ne')
  have h1 : (m : ℤ) ∣ x - (rootOf m (x, y) : ℤ) * y := by
    rw [hν]
    have e : x - x * A % m * y = x * (1 - y * A) + (x * A - x * A % m) * y := by ring
    rw [e]
    refine dvd_add ⟨x * Int.gcdB y m, by push_cast at hbez; linear_combination x * hbez⟩ ?_
    exact dvd_mul_of_dvd_left ⟨x * A / m, by rw [Int.emod_def]; ring⟩ _
  refine ⟨?_, h1, ?_⟩
  · have := Int.emod_lt_of_pos (x * A) hm0
    have h2 : ((rootOf m (x, y) : ℕ) : ℤ) < m := by rw [hν]; exact this
    exact_mod_cast h2
  · obtain ⟨hsum, -⟩ := mem_primReps.1 hp
    have h3 : (m : ℤ) ∣ ((rootOf m (x, y) : ℤ) ^ 2 + 1) * y ^ 2 := by
      have e : ((rootOf m (x, y) : ℤ) ^ 2 + 1) * y ^ 2 =
          (x ^ 2 + y ^ 2) - (x - (rootOf m (x, y) : ℤ) * y) * (x + (rootOf m (x, y) : ℤ) * y) := by
        ring
      rw [e, hsum]
      exact dvd_sub (dvd_refl _) (dvd_mul_of_dvd_left h1 _)
    exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right h3

/-- Uniqueness of the root. -/
theorem rootOf_unique {m : ℕ} (hm : 1 ≤ m) {p : ℤ × ℤ} (hp : p ∈ primReps m) {ν : ℕ} (hνm : ν < m)
    (hν : (m : ℤ) ∣ p.1 - (ν : ℤ) * p.2) : rootOf m p = ν := by
  obtain ⟨h1, h2, -⟩ := rootOf_spec hm hp
  have hcop := isCoprime_of_primRep hp
  have h3 : (m : ℤ) ∣ ((ν : ℤ) - rootOf m p) * p.2 := by
    have := dvd_sub h2 hν
    convert this using 1; ring
  have h4 : (m : ℤ) ∣ (ν : ℤ) - rootOf m p := hcop.symm.dvd_of_dvd_mul_right h3
  have h5 : (ν : ℤ) ≡ rootOf m p [ZMOD m] := (Int.modEq_iff_dvd.2 h4).symm
  rw [Int.natCast_modEq_iff] at h5
  unfold Nat.ModEq at h5
  rw [Nat.mod_eq_of_lt hνm, Nat.mod_eq_of_lt h1] at h5
  exact h5.symm

/-- **`r*(m) = 4 ϱ₁(m)`**: the number of primitive representations of `m ≥ 1` as a sum of two
squares is four times the number of roots of `ν² + 1 ≡ 0 (mod m)`. -/
theorem card_primReps {m : ℕ} (hm : 1 ≤ m) : (primReps m).card = 4 * rho 1 m := by
  classical
  set R₁ := (Finset.range m).filter (fun ν : ℕ => (m : ℤ) ∣ (ν : ℤ) ^ 2 + 1) with hR₁
  have hrho : rho 1 m = R₁.card := rfl
  rw [hrho, Finset.card_eq_sum_card_fiberwise (f := rootOf m) (t := R₁)]
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro ν hν
    rw [hR₁, Finset.mem_filter, Finset.mem_range] at hν
    obtain ⟨x₀, y₀, h₀, h₀ν⟩ := exists_primRep m hm hν.2
    have hfib : (primReps m).filter (fun p => rootOf m p = ν) =
        (primReps m).filter (fun p => (m : ℤ) ∣ p.1 - ν * p.2) := by
      apply Finset.filter_congr
      intro p hp
      constructor
      · intro h; rw [← h]; exact (rootOf_spec hm hp).2.1
      · intro h; exact rootOf_unique hm hp hν.1 h
    rw [hfib, fiber_eq_rot4 hm hν.2 h₀ h₀ν]
    apply card_rot4
    by_contra h
    push Not at h
    obtain ⟨hsum, -⟩ := mem_primReps.1 h₀
    rw [h.1, h.2] at hsum
    have : (m : ℤ) = 0 := by linarith
    omega
  · intro p hp
    rw [Finset.mem_coe] at hp
    obtain ⟨h1, -, h3⟩ := rootOf_spec hm hp
    rw [Finset.mem_coe, hR₁, Finset.mem_filter, Finset.mem_range]
    exact ⟨h1, h3⟩

end Triples
