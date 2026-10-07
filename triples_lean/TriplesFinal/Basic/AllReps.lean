import TriplesFinal.Basic.Defs
import TriplesFinal.Basic.PrimitiveReps

/-!
# Reduction to primitive representations: `r(n) = ∑_{k² ∣ n} r*(n/k²)`

Every representation `n = x² + y²` with `n ≥ 1` is `(kx₁, ky₁)` for a unique `k = gcd(x, y)`
with `k² ∣ n` and a primitive representation `n/k² = x₁² + y₁²`.

Paper: §1, Notation (Jacobi's formula for `r(n)`).
-/

namespace Triples

/-- All representations `x² + y² = n`. -/
def allReps (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 = n)

theorem mem_allReps {n : ℕ} {x y : ℤ} : (x, y) ∈ allReps n ↔ x ^ 2 + y ^ 2 = n := by
  simp only [allReps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_iff_right_iff_imp]
  intro h
  have hx := abs_le_sq x
  have hy := abs_le_sq y
  have hx2 := sq_nonneg x
  have hy2 := sq_nonneg y
  exact ⟨abs_le.1 (by linarith), abs_le.1 (by linarith)⟩

theorem r_eq_card_allReps (n : ℕ) : r n = (allReps n).card := by
  unfold r
  rw [← Set.ncard_coe_finset]
  congr 1
  ext ⟨x, y⟩
  rw [Finset.mem_coe, mem_allReps]
  rfl

/-- **Decomposition by the greatest common divisor**:
`r(n) = ∑_{k² ∣ n} r*(n/k²)`. -/
theorem card_allReps (n : ℕ) (hn : 1 ≤ n) :
    (allReps n).card = ∑ k ∈ n.divisors.filter (fun k => k * k ∣ n),
      (primReps (n / (k * k))).card := by
  classical
  have hdecomp : allReps n = (n.divisors.filter (fun k => k * k ∣ n)).biUnion
      (fun k => (primReps (n / (k * k))).image (fun p => ((k : ℤ) * p.1, (k : ℤ) * p.2))) := by
    ext ⟨x, y⟩
    rw [mem_allReps, Finset.mem_biUnion]
    constructor
    · intro hxy
      have hne : x ≠ 0 ∨ y ≠ 0 := by
        by_contra h; push Not at h; rw [h.1, h.2] at hxy; push_cast at hxy; omega
      set k := Int.gcd x y with hk
      have hk0 : 0 < k := Int.gcd_pos_iff.2 hne
      obtain ⟨x₁, hx₁⟩ : (k : ℤ) ∣ x := Int.gcd_dvd_left x y
      obtain ⟨y₁, hy₁⟩ : (k : ℤ) ∣ y := Int.gcd_dvd_right x y
      have hg1 : Int.gcd x₁ y₁ = 1 := by
        have h1 : Int.gcd x y = k * Int.gcd x₁ y₁ := by
          rw [hx₁, hy₁, Int.gcd_mul_left]; simp
        rw [← hk] at h1
        have : k * Int.gcd x₁ y₁ = k * 1 := by rw [← h1, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hk0 this
      have hn' : (n : ℤ) = (k : ℤ) * k * (x₁ ^ 2 + y₁ ^ 2) := by rw [← hxy, hx₁, hy₁]; ring
      have hkk' : k * k ∣ n := by
        have : ((k * k : ℕ) : ℤ) ∣ n := ⟨x₁ ^ 2 + y₁ ^ 2, by push_cast; rw [hn']⟩
        exact_mod_cast this
      have hm : x₁ ^ 2 + y₁ ^ 2 = ((n / (k * k) : ℕ) : ℤ) := by
        have h2 : (((n / (k * k)) * (k * k) : ℕ) : ℤ) = (n : ℤ) := by
          rw [Nat.div_mul_cancel hkk']
        rw [Nat.cast_mul, Nat.cast_mul] at h2
        have hk2 : (k : ℤ) * k ≠ 0 := by positivity
        apply mul_left_cancel₀ hk2
        linear_combination hn'.symm.trans h2.symm
      refine ⟨k, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_divisors]
        have hkk : ((k * k : ℕ) : ℤ) ∣ n := ⟨x₁ ^ 2 + y₁ ^ 2, by push_cast; rw [hn']⟩
        have hkk' : k * k ∣ n := by exact_mod_cast hkk
        exact ⟨⟨(Nat.dvd_mul_right k k).trans hkk', by omega⟩, hkk'⟩
      · rw [Finset.mem_image]
        exact ⟨(x₁, y₁), mem_primReps.2 ⟨hm, hg1⟩, by rw [hx₁, hy₁]⟩
    · rintro ⟨k, hk, hp⟩
      rw [Finset.mem_filter, Nat.mem_divisors] at hk
      rw [Finset.mem_image] at hp
      obtain ⟨⟨x₁, y₁⟩, hp1, hp2⟩ := hp
      simp only [Prod.mk.injEq] at hp2
      obtain ⟨rfl, rfl⟩ := hp2
      obtain ⟨hsum, -⟩ := mem_primReps.1 hp1
      have h1 : (((n / (k * k)) * (k * k) : ℕ) : ℤ) = (n : ℤ) := by
        rw [Nat.div_mul_cancel hk.2]
      rw [Nat.cast_mul, Nat.cast_mul] at h1
      linear_combination (k : ℤ) ^ 2 * hsum + h1
  rw [hdecomp, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter, Nat.mem_divisors] at hk
    have hk0 : (k : ℤ) ≠ 0 := by
      have : k ≠ 0 := fun h => by rw [h] at hk; simp at hk
      exact_mod_cast this
    apply Finset.card_image_of_injective
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (mul_left_cancel₀ hk0 hpq.1) (mul_left_cancel₀ hk0 hpq.2)
  · intro k hk k' hk' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_image] at hp hp'
    obtain ⟨⟨x₁, y₁⟩, h1, h2⟩ := hp
    obtain ⟨⟨x₂, y₂⟩, h3, h4⟩ := hp'
    have hg1 := (mem_primReps.1 h1).2
    have hg2 := (mem_primReps.1 h3).2
    apply hne
    have e1 : Int.gcd ((k : ℤ) * x₁) ((k : ℤ) * y₁) = k := by
      rw [Int.gcd_mul_left, hg1]; simp
    have e2 : Int.gcd ((k' : ℤ) * x₂) ((k' : ℤ) * y₂) = k' := by
      rw [Int.gcd_mul_left, hg2]; simp
    rw [← e1, ← e2]
    have h5 := Prod.ext_iff.1 (h2.trans h4.symm)
    simp only at h5
    rw [h5.1, h5.2]

end Triples
