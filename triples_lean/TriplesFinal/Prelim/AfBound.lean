import TriplesFinal.Prelim.BetaBound

/-!
# Lemma 5.3(b): the bound for `A_f(t)`

`A_f(t) = ∑_{k ≤ t} χ(k) f(k) ≪_ε t^(1/2+ε) d^(1+ε)`, uniformly in good primes `d`.

* Partial sums of Dirichlet convolutions: `∑_{n ≤ N} (a ∗ b)(n) = ∑_{y ≤ N} b(y) ∑_{x ≤ N/y} a(x)`
  (`sum_Icc_mul_eq`).
* The hyperbola method (`abs_sum_hypSet_le`): with `|χ|, |ψ| ≤ 1`, `|∑_{n ≤ y} χ(n)| ≤ 1` and
  `|∑_{n ≤ y} ψ(n)| ≤ Ψ*`, we get `|∑_{n ≤ y} (χ ∗ ψ)(n)| ≤ 2√y (Ψ* + 1)`.
* The Pólya–Vinogradov inequality gives `Ψ* ≤ C √(8m) log(8m)` (`IsGood.abs_sum_psi_le`).
* Since `χ f = (χ ∗ ψ) ∗ β`, `A_f(t) = ∑_{i ≤ t} β(i) ∑_{n ≤ t/i} (χ ∗ ψ)(n)` (`IsGood.Af_eq`),
  and the bound for `∑ |β(i)| i^(-1/2-ε)` (`betaWeight_sum_le`) finishes the proof
  (`Af_bound`).

Paper: §5.3, proof of Lemma 5.3(b).
-/

namespace Triples

open ArithmeticFunction ZMod
open scoped ArithmeticFunction.Moebius

/-- The lattice points `(x, y)` with `x, y ≥ 1` and `xy ≤ N`. -/
def hypSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun q => q.1 * q.2 ≤ N)

theorem mem_hypSet {N : ℕ} {q : ℕ × ℕ} : q ∈ hypSet N ↔ 1 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.1 * q.2 ≤ N := by
  simp only [hypSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩, h3⟩
    · nlinarith
    · nlinarith

/-- `∑_{n ≤ N} (a ∗ b)(n) = ∑_{xy ≤ N} a(x) b(y)`. -/
theorem sum_Icc_mul_eq_sum_hypSet {R : Type*} [CommSemiring R] (a b : ArithmeticFunction R)
    (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (a * b) n = ∑ q ∈ hypSet N, a q.1 * b q.2 := by
  have hmaps : ∀ q ∈ hypSet N, q.1 * q.2 ∈ Finset.Icc 1 N := by
    intro q hq
    rw [mem_hypSet] at hq
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hq.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [mul_apply]
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter, mem_hypSet, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : q.1 * q.2 ≠ 0 := by omega
      exact ⟨⟨Nat.one_le_iff_ne_zero.2 (left_ne_zero_of_mul hne),
        Nat.one_le_iff_ne_zero.2 (right_ne_zero_of_mul hne), by omega⟩, h1⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h4, by omega⟩
  · intro q _; rfl

/-- `∑_{xy ≤ N} F(x, y) = ∑_{y ≤ N} ∑_{x ≤ N/y} F(x, y)`. -/
theorem sum_hypSet_eq_right {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ) :
    ∑ q ∈ hypSet N, F q.1 q.2 = ∑ y ∈ Finset.Icc 1 N, ∑ x ∈ Finset.Icc 1 (N / y), F x y := by
  rw [hypSet, Finset.sum_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mem_Icc] at hy
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [Nat.le_div_iff_mul_le (by omega)]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by nlinarith⟩, h3⟩

/-- `∑_{xy ≤ N} F(x, y) = ∑_{x ≤ N} ∑_{y ≤ N/x} F(x, y)`. -/
theorem sum_hypSet_eq_left {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) (N : ℕ) :
    ∑ q ∈ hypSet N, F q.1 q.2 = ∑ x ∈ Finset.Icc 1 N, ∑ y ∈ Finset.Icc 1 (N / x), F x y := by
  rw [hypSet, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Icc] at hx
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [Nat.le_div_iff_mul_le (by omega), mul_comm y x]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by nlinarith⟩, h3⟩

/-- **Partial sums of a Dirichlet convolution**:
`∑_{n ≤ N} (a ∗ b)(n) = ∑_{y ≤ N} b(y) ∑_{x ≤ N/y} a(x)`. -/
theorem sum_Icc_mul_eq {R : Type*} [CommSemiring R] (a b : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (a * b) n =
      ∑ y ∈ Finset.Icc 1 N, b y * ∑ x ∈ Finset.Icc 1 (N / y), a x := by
  rw [sum_Icc_mul_eq_sum_hypSet, sum_hypSet_eq_right (fun x y => a x * b y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- **The hyperbola method.** If `|a|, |b| ≤ 1`, the partial sums of `a` are bounded by `1` and
those of `b` by `B`, then `|∑_{xy ≤ N} a(x) b(y)| ≤ 2 √N (B + 1)`. -/
theorem abs_sum_hypSet_le (a b : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (hA : ∀ u, |∑ j ∈ Finset.Icc 1 u, a j| ≤ 1) {B : ℝ}
    (hB : ∀ u, |∑ j ∈ Finset.Icc 1 u, b j| ≤ B) (N : ℕ) :
    |∑ q ∈ hypSet N, a q.1 * b q.2| ≤ 2 * Real.sqrt N * (B + 1) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : hypSet 0 = ∅ := by
      ext q; simp only [mem_hypSet, Finset.notMem_empty, iff_false]; intro h; nlinarith [h.1, h.2.1, h.2.2]
    rw [this, Finset.sum_empty, abs_zero]
    positivity
  set U := Nat.sqrt N with hU
  set S1 := (hypSet N).filter (fun q => q.1 ≤ U) with hS1
  set S2 := (hypSet N).filter (fun q => q.2 ≤ U) with hS2
  have hUN : U * U ≤ N := Nat.sqrt_le N
  have hNU : N < (U + 1) * (U + 1) := Nat.lt_succ_sqrt N
  have hU1 : 1 ≤ U := by
    rw [hU]; exact Nat.le_sqrt.2 (by omega)
  have hUle : U ≤ N := by nlinarith
  have hunion : S1 ∪ S2 = hypSet N := by
    ext q
    simp only [hS1, hS2, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_contra hc
      push Not at hc
      have h1 := hc.1 h
      have h2 := hc.2 h
      rw [mem_hypSet] at h
      have : (U + 1) * (U + 1) ≤ q.1 * q.2 := Nat.mul_le_mul h1 h2
      omega
  have hinter : S1 ∩ S2 = Finset.Icc 1 U ×ˢ Finset.Icc 1 U := by
    ext q
    simp only [hS1, hS2, Finset.mem_inter, Finset.mem_filter, mem_hypSet, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2, _⟩, h4⟩, ⟨_, h6⟩⟩; exact ⟨⟨h1, h4⟩, ⟨h2, h6⟩⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h6⟩⟩
      have : q.1 * q.2 ≤ U * U := Nat.mul_le_mul h4 h6
      exact ⟨⟨⟨h1, h2, by omega⟩, h4⟩, ⟨⟨h1, h2, by omega⟩, h6⟩⟩
  have hsplit := Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := fun q => a q.1 * b q.2)
  rw [hunion, hinter] at hsplit
  -- the three sums
  have hsum1 : ∑ q ∈ S1, a q.1 * b q.2 =
      ∑ x ∈ Finset.Icc 1 U, a x * ∑ y ∈ Finset.Icc 1 (N / x), b y := by
    rw [hS1, Finset.sum_filter, sum_hypSet_eq_left (fun x y => if x ≤ U then a x * b y else 0)]
    rw [show Finset.Icc 1 U = (Finset.Icc 1 N).filter (fun x => x ≤ U) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_filter]; omega, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with hx
    · rw [Finset.mul_sum]
    · simp
  have hsum2 : ∑ q ∈ S2, a q.1 * b q.2 =
      ∑ y ∈ Finset.Icc 1 U, b y * ∑ x ∈ Finset.Icc 1 (N / y), a x := by
    rw [hS2, Finset.sum_filter, sum_hypSet_eq_right (fun x y => if y ≤ U then a x * b y else 0)]
    rw [show Finset.Icc 1 U = (Finset.Icc 1 N).filter (fun y => y ≤ U) by
      ext y; simp only [Finset.mem_Icc, Finset.mem_filter]; omega, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs with hy
    · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    · simp
  have hsum3 : ∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2 =
      (∑ x ∈ Finset.Icc 1 U, a x) * ∑ y ∈ Finset.Icc 1 U, b y := by
    rw [Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  have hb1 : |∑ q ∈ S1, a q.1 * b q.2| ≤ U * B := by
    rw [hsum1]
    calc |∑ x ∈ Finset.Icc 1 U, a x * ∑ y ∈ Finset.Icc 1 (N / x), b y|
        ≤ ∑ x ∈ Finset.Icc 1 U, |a x * ∑ y ∈ Finset.Icc 1 (N / x), b y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Finset.Icc 1 U, B := by
          apply Finset.sum_le_sum
          intro x _
          rw [abs_mul]
          calc |a x| * |∑ y ∈ Finset.Icc 1 (N / x), b y| ≤ 1 * B :=
                mul_le_mul (ha x) (hB _) (abs_nonneg _) zero_le_one
            _ = B := one_mul B
      _ = U * B := by simp
  have hb2 : |∑ q ∈ S2, a q.1 * b q.2| ≤ U := by
    rw [hsum2]
    calc |∑ y ∈ Finset.Icc 1 U, b y * ∑ x ∈ Finset.Icc 1 (N / y), a x|
        ≤ ∑ y ∈ Finset.Icc 1 U, |b y * ∑ x ∈ Finset.Icc 1 (N / y), a x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ Finset.Icc 1 U, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y _
          rw [abs_mul]
          calc |b y| * |∑ x ∈ Finset.Icc 1 (N / y), a x| ≤ 1 * 1 :=
                mul_le_mul (hb y) (hA _) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = U := by simp
  have hb3 : |∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2| ≤ B := by
    rw [hsum3, abs_mul]
    calc |∑ x ∈ Finset.Icc 1 U, a x| * |∑ y ∈ Finset.Icc 1 U, b y| ≤ 1 * B :=
          mul_le_mul (hA U) (hB U) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hUs : (U : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast hN
  have heq : ∑ q ∈ hypSet N, a q.1 * b q.2 = ∑ q ∈ S1, a q.1 * b q.2 + ∑ q ∈ S2, a q.1 * b q.2 -
      ∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2 := by linarith
  rw [heq]
  calc |∑ q ∈ S1, a q.1 * b q.2 + ∑ q ∈ S2, a q.1 * b q.2 -
        ∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2|
      ≤ |∑ q ∈ S1, a q.1 * b q.2| + |∑ q ∈ S2, a q.1 * b q.2| +
          |∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2| := by
        have := abs_sub (∑ q ∈ S1, a q.1 * b q.2 + ∑ q ∈ S2, a q.1 * b q.2)
          (∑ q ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 U, a q.1 * b q.2)
        have := abs_add_le (∑ q ∈ S1, a q.1 * b q.2) (∑ q ∈ S2, a q.1 * b q.2)
        linarith
    _ ≤ U * B + U + B := by linarith
    _ ≤ 2 * Real.sqrt N * (B + 1) := by nlinarith

/-- The partial sums of `χ₄` are `1` or `0`. -/
theorem sum_Icc_chiAF (u : ℕ) :
    ∑ j ∈ Finset.Icc 1 u, (chiAF j : ℝ) = if u % 4 = 1 ∨ u % 4 = 2 then 1 else 0 := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, chiAF_apply, χ₄_nat_eq_if_mod_four (u + 1)]
    have : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
    rcases this with h | h | h | h
    · have h1 : (u + 1) % 4 = 1 := by omega
      have h2 : (u + 1) % 2 = 1 := by omega
      simp [h, h1, h2]
    · have h1 : (u + 1) % 4 = 2 := by omega
      have h2 : (u + 1) % 2 = 0 := by omega
      simp [h, h1, h2]
    · have h1 : (u + 1) % 4 = 3 := by omega
      have h2 : (u + 1) % 2 = 1 := by omega
      simp [h, h1, h2]
    · have h1 : (u + 1) % 4 = 0 := by omega
      have h2 : (u + 1) % 2 = 0 := by omega
      simp [h, h1, h2]

theorem abs_sum_Icc_chiAF_le (u : ℕ) : |∑ j ∈ Finset.Icc 1 u, (chiAF j : ℝ)| ≤ 1 := by
  rw [sum_Icc_chiAF]; split_ifs <;> norm_num

theorem abs_chiAF_le (n : ℕ) : |(chiAF n : ℝ)| ≤ 1 := by
  have := abs_chi_four_le_one n
  rw [chiAF_apply]; exact_mod_cast this

theorem abs_psi_le (m : ℤ) (n : ℕ) : |(psi m n : ℝ)| ≤ 1 := by
  unfold psi
  split_ifs
  · rcases jacobiSym.trichotomy m n with h | h | h <;> simp [h]
  · simp

namespace PatternData

variable {a b : ℕ} {P : PatternData a b}

/-- Pólya–Vinogradov for `ψ`: `|∑_{n ≤ u} ψ(n)| ≤ |C| √(8m) log(8m)`. -/
theorem IsGood.abs_sum_psi_le {C : ℝ}
    (hC : ∀ q : ℕ, 2 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ y : ℕ,
      ‖∑ n ∈ Finset.range (y + 1), χ n‖ ≤ C * Real.sqrt q * Real.log q)
    {d : ℕ} (hd : P.IsGood d) (u : ℕ) :
    |∑ j ∈ Finset.Icc 1 u, (psiAF (P.m d) j : ℝ)| ≤
      |C| * Real.sqrt (8 * (P.m d).natAbs) * Real.log (8 * (P.m d).natAbs) := by
  obtain ⟨ψ', hne, -, hval⟩ := hd.psi_character
  have hM1 : 1 ≤ (P.m d).natAbs := by
    have := P.m_pos hd.d₁_lt; omega
  have hq2 : 2 ≤ 8 * (P.m d).natAbs := by omega
  have h := hC _ hq2 ψ' hne u
  have hsum : ∑ n ∈ Finset.range (u + 1), ψ' n =
      ((∑ j ∈ Finset.Icc 1 u, (psiAF (P.m d) j : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_subset (s₁ := Finset.Icc 1 u) (s₂ := Finset.range (u + 1))]
    · apply Finset.sum_congr rfl
      intro n _
      rw [hval n, psiAF_apply]
    · intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
    · intro n hn1 hn
      rw [Finset.mem_range] at hn1
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      have : n = 0 := by
        by_contra h0
        have := hn (by omega)
        omega
      subst this
      rw [hval 0]; simp [psi]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  have hq : (1 : ℝ) ≤ ((8 * (P.m d).natAbs : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 8 * (P.m d).natAbs)
  have hlog : 0 ≤ Real.log ((8 * (P.m d).natAbs : ℕ) : ℝ) := Real.log_nonneg hq
  calc _ ≤ C * Real.sqrt ((8 * (P.m d).natAbs : ℕ) : ℝ) * Real.log ((8 * (P.m d).natAbs : ℕ) : ℝ) := h
    _ ≤ |C| * Real.sqrt ((8 * (P.m d).natAbs : ℕ) : ℝ) * Real.log ((8 * (P.m d).natAbs : ℕ) : ℝ) := by
        gcongr; exact le_abs_self C
    _ = _ := by push_cast; ring

/-- The partial sums of `χ ∗ ψ`: `|∑_{n ≤ u} (χ ∗ ψ)(n)| ≤ 2 √u (Ψ* + 1)` (hyperbola method). -/
theorem IsGood.abs_sum_chipsi_le {C : ℝ}
    (hC : ∀ q : ℕ, 2 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ y : ℕ,
      ‖∑ n ∈ Finset.range (y + 1), χ n‖ ≤ C * Real.sqrt q * Real.log q)
    {d : ℕ} (hd : P.IsGood d) (u : ℕ) :
    |∑ n ∈ Finset.Icc 1 u, ((chiAF * psiAF (P.m d)) n : ℝ)| ≤
      2 * Real.sqrt u *
        (|C| * Real.sqrt (8 * (P.m d).natAbs) * Real.log (8 * (P.m d).natAbs) + 1) := by
  have h := sum_Icc_mul_eq_sum_hypSet chiAF (psiAF (P.m d)) u
  have h' : ∑ n ∈ Finset.Icc 1 u, ((chiAF * psiAF (P.m d)) n : ℝ) =
      ∑ q ∈ hypSet u, (chiAF q.1 : ℝ) * (psiAF (P.m d) q.2 : ℝ) := by
    exact_mod_cast h
  rw [h']
  exact abs_sum_hypSet_le (fun n => (chiAF n : ℝ)) (fun n => (psiAF (P.m d) n : ℝ))
    abs_chiAF_le (fun n => by rw [psiAF_apply]; exact abs_psi_le _ _) abs_sum_Icc_chiAF_le
    (hd.abs_sum_psi_le hC) u

/-- `A_f(t) = ∑_{y ≤ t} β(y) ∑_{x ≤ t/y} (χ ∗ ψ)(x)`. -/
theorem IsGood.Af_eq {d : ℕ} (hd : P.IsGood d) (t : ℝ) :
    P.Af d t = ∑ y ∈ Finset.Icc 1 ⌊t⌋₊, (P.betaAF d y : ℝ) *
      ∑ x ∈ Finset.Icc 1 (⌊t⌋₊ / y), ((chiAF * psiAF (P.m d)) x : ℝ) := by
  have h1 : P.Af d t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (P.gAF d k : ℝ) := by
    unfold Af
    apply Finset.sum_congr rfl
    intro k _
    rw [P.gAF_apply, Int.cast_mul, hd.fAF_eq, chiAF_apply]
  have h2 := sum_Icc_mul_eq (chiAF * psiAF (P.m d)) (P.betaAF d) ⌊t⌋₊
  rw [← P.gAF_eq] at h2
  rw [h1]
  exact_mod_cast h2

/-- `√⌊N/y⌋ ≤ N^(1/2+ε) y^(-(1/2+ε))` for `1 ≤ y ≤ N`. -/
theorem sqrt_div_le_rpow {N y : ℕ} (hy : 1 ≤ y) (hyN : y ≤ N) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt ((N / y : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * (y : ℝ) ^ (-(1 / 2 + ε)) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hNy : (1 : ℝ) ≤ (N : ℝ) / y := by
    rw [le_div_iff₀ hy0, one_mul]; exact_mod_cast hyN
  calc Real.sqrt ((N / y : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / y) :=
        Real.sqrt_le_sqrt (Nat.cast_div_le)
    _ = ((N : ℝ) / y) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ ≤ ((N : ℝ) / y) ^ (1 / 2 + ε) := Real.rpow_le_rpow_of_exponent_le hNy (by linarith)
    _ = (N : ℝ) ^ (1 / 2 + ε) * (y : ℝ) ^ (-(1 / 2 + ε)) := by
        rw [Real.div_rpow (Nat.cast_nonneg _) hy0.le, Real.rpow_neg hy0.le, div_eq_mul_inv]

variable (P) in
/-- **Lemma 5.3(b).** `A_f(t) ≪_ε t^(1/2+ε) d^(1+ε)`, uniformly in good primes `d`. -/
theorem Af_bound (hPV : PolyaVinogradov) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ d : ℕ, P.IsGood d → ∀ t : ℝ, 1 ≤ t →
      |P.Af d t| ≤ C * t ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε) := by
  obtain ⟨CPV, hCPV⟩ := hPV
  set ε' := ε / 3 with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨Cβ, hCβ, hβ⟩ := P.betaWeight_sum_le hε'pos
  set K : ℝ := 4 * |CPV| * (16 : ℝ) ^ ε' / ε' + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K * Cβ, fun d hd t ht => ?_⟩
  set N := ⌊t⌋₊ with hN
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff t).2 ht
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd.prime.one_lt.le
  have hd0 : (0 : ℝ) ≤ d := by linarith
  set M := (P.m d).natAbs with hM
  have hMle : (M : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by
    have hmb := (P.m_bounds hd.d₁_lt).2
    have hMm : ((P.m d).natAbs : ℤ) = P.m d := Int.natAbs_of_nonneg (P.m_pos hd.d₁_lt).le
    have : (M : ℤ) ≤ 2 * (d : ℤ) ^ 2 := by rw [hM, hMm]; exact hmb
    exact_mod_cast this
  set Ψ := |CPV| * Real.sqrt (8 * (M : ℝ)) * Real.log (8 * (M : ℝ)) with hΨ
  -- `Ψ + 1 ≤ K d^(1+2ε')`
  have hΨ1 : Ψ + 1 ≤ K * (d : ℝ) ^ (1 + 2 * ε') := by
    have h8M : 8 * (M : ℝ) ≤ 16 * (d : ℝ) ^ 2 := by linarith
    have hsq : Real.sqrt (8 * (M : ℝ)) ≤ 4 * d := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hlog : Real.log (8 * (M : ℝ)) ≤ (16 : ℝ) ^ ε' * (d : ℝ) ^ (2 * ε') / ε' := by
      calc Real.log (8 * (M : ℝ)) ≤ (8 * (M : ℝ)) ^ ε' / ε' :=
            Real.log_le_rpow_div (by positivity) hε'pos
        _ ≤ (16 * (d : ℝ) ^ 2) ^ ε' / ε' := by gcongr
        _ = (16 : ℝ) ^ ε' * (d : ℝ) ^ (2 * ε') / ε' := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (d : ℝ) 2,
              ← Real.rpow_mul hd0]
            norm_num
    have hlog0 : 0 ≤ Real.log (8 * (M : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ M := by
        have := P.m_pos hd.d₁_lt
        have h1 : 1 ≤ M := by omega
        exact_mod_cast h1
      linarith
    have hdpow : (d : ℝ) ^ (1 + 2 * ε') = d * (d : ℝ) ^ (2 * ε') := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hdpow1 : (1 : ℝ) ≤ (d : ℝ) ^ (1 + 2 * ε') := Real.one_le_rpow hd1 (by positivity)
    have hΨle : Ψ ≤ (4 * |CPV| * (16 : ℝ) ^ ε' / ε') * (d : ℝ) ^ (1 + 2 * ε') := by
      rw [hΨ, hdpow]
      calc |CPV| * Real.sqrt (8 * (M : ℝ)) * Real.log (8 * (M : ℝ))
          ≤ |CPV| * (4 * d) * ((16 : ℝ) ^ ε' * (d : ℝ) ^ (2 * ε') / ε') := by gcongr
        _ = (4 * |CPV| * (16 : ℝ) ^ ε' / ε') * (d * (d : ℝ) ^ (2 * ε')) := by ring
    rw [hK]
    nlinarith
  have hΨ0 : 0 ≤ Ψ + 1 := by
    have : 0 ≤ Ψ := by
      rw [hΨ]
      have hlog0 : 0 ≤ Real.log (8 * (M : ℝ)) := by
        apply Real.log_nonneg
        have := P.m_pos hd.d₁_lt
        have h1 : 1 ≤ M := by omega
        have : (1 : ℝ) ≤ M := by exact_mod_cast h1
        linarith
      positivity
    linarith
  -- the main estimate
  rw [hd.Af_eq]
  have hterm : ∀ y ∈ Finset.Icc 1 N,
      |(P.betaAF d y : ℝ) * ∑ x ∈ Finset.Icc 1 (N / y), ((chiAF * psiAF (P.m d)) x : ℝ)| ≤
        2 * (Ψ + 1) * (N : ℝ) ^ (1 / 2 + ε') * P.betaWeight d (1 / 2 + ε') y := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    rw [abs_mul]
    have h1 := hd.abs_sum_chipsi_le hCPV (N / y)
    have h2 := sqrt_div_le_rpow hy.1 hy.2 hε'pos.le
    calc |(P.betaAF d y : ℝ)| * |∑ x ∈ Finset.Icc 1 (N / y), ((chiAF * psiAF (P.m d)) x : ℝ)|
        ≤ |(P.betaAF d y : ℝ)| * (2 * Real.sqrt ((N / y : ℕ) : ℝ) * (Ψ + 1)) := by
          gcongr
      _ ≤ |(P.betaAF d y : ℝ)| * (2 * ((N : ℝ) ^ (1 / 2 + ε') * (y : ℝ) ^ (-(1 / 2 + ε'))) *
            (Ψ + 1)) := by gcongr
      _ = 2 * (Ψ + 1) * (N : ℝ) ^ (1 / 2 + ε') * P.betaWeight d (1 / 2 + ε') y := by
          rw [betaWeight]; ring
  calc |∑ y ∈ Finset.Icc 1 N, (P.betaAF d y : ℝ) *
        ∑ x ∈ Finset.Icc 1 (N / y), ((chiAF * psiAF (P.m d)) x : ℝ)|
      ≤ ∑ y ∈ Finset.Icc 1 N, 2 * (Ψ + 1) * (N : ℝ) ^ (1 / 2 + ε') *
          P.betaWeight d (1 / 2 + ε') y :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * (Ψ + 1) * (N : ℝ) ^ (1 / 2 + ε') *
          ∑ y ∈ Finset.Icc 1 N, P.betaWeight d (1 / 2 + ε') y := by rw [Finset.mul_sum]
    _ ≤ 2 * (K * (d : ℝ) ^ (1 + 2 * ε')) * t ^ (1 / 2 + ε) * (Cβ * (d : ℝ) ^ ε') := by
        have hNe : (N : ℝ) ^ (1 / 2 + ε') ≤ t ^ (1 / 2 + ε) :=
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hNt (by positivity)).trans
            (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
        have hs0 : 0 ≤ ∑ y ∈ Finset.Icc 1 N, P.betaWeight d (1 / 2 + ε') y :=
          Finset.sum_nonneg (fun y _ => P.betaWeight_nonneg d _ y)
        gcongr
        exact hβ d hd N
    _ = 2 * K * Cβ * t ^ (1 / 2 + ε) * (d : ℝ) ^ (1 + ε) := by
        have : (d : ℝ) ^ (1 + 2 * ε') * (d : ℝ) ^ ε' = (d : ℝ) ^ (1 + ε) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; rw [hε']; ring
        rw [← this]; ring

end PatternData

end Triples
