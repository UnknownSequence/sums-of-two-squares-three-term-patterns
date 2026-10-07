import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Roots of `ν² ≡ -m (mod n)` (Lemma 5.2(a),(b))

`ϱ_m(n) = #{ν mod n : ν² + m ≡ 0 (mod n)}`, a multiplicative function of `n`.
(a) For odd `n`, `ϱ(n) = #{t mod n : Et² + H ≡ 0 (mod n)}` (when `m = 2^v H`, `2^v E = 2^(2j)`).
(b) For an odd prime `ℓ ∤ m`, `ϱ(ℓ^i) = 1 + (-m/ℓ)` (Hensel's lemma); in general
    `ϱ(ℓ^i) ≤ 2 ℓ^(min(i, v_ℓ(m))/2)`, and hence `ϱ(n) ≤ 2^ω(n) gcd(n, m)^(1/2)` for odd `n`.

These statements do not depend on the pattern; Lemma 5.2(c) is in `Prelim/Roots.lean`. The case
`m = 1` is also used for Jacobi's two-square theorem (`Basic/Jacobi.lean`).

Paper: §5.2, Lemma 5.2 and equation (5.2).
-/

namespace Triples

/-- `ϱ_m(n) = #{ν mod n : ν² + m ≡ 0 (mod n)}`. -/
def rho (m : ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun ν : ℕ => (n : ℤ) ∣ (ν : ℤ) ^ 2 + m)).card

/-- `ϱ_{E,H}(n) = #{ν mod n : Eν² + H ≡ 0 (mod n)}`. -/
def rhoEH (E H : ℤ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun ν : ℕ => (n : ℤ) ∣ E * (ν : ℤ) ^ 2 + H)).card

/-- `ϱ_m(n)` counts the roots of `x² + m` in `ZMod n`. -/
theorem rho_eq_card_zmod (m : ℤ) (n : ℕ) [NeZero n] :
    rho m n = (Finset.univ.filter (fun x : ZMod n => x ^ 2 + (m : ZMod n) = 0)).card := by
  unfold rho
  apply Finset.card_bij (fun (ν : ℕ) _ => (ν : ZMod n))
  · intro ν hν
    rw [Finset.mem_filter] at hν ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((ν : ℤ) ^ 2 + m) n).2 hν.2
    push_cast at this
    exact this
  · intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b n).1 hab
    rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this
  · intro x hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [Finset.mem_filter] at hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx.2

/-- `ϱ` is multiplicative (Chinese remainder theorem). -/
theorem rho_mul (m : ℤ) {n₁ n₂ : ℕ} (h : Nat.Coprime n₁ n₂) :
    rho m (n₁ * n₂) = rho m n₁ * rho m n₂ := by
  classical
  rcases Nat.eq_zero_or_pos n₁ with rfl | h1
  · have : n₂ = 1 := (Nat.coprime_zero_left n₂).1 h
    subst this
    simp [rho]
  rcases Nat.eq_zero_or_pos n₂ with rfl | h2
  · have : n₁ = 1 := (Nat.coprime_zero_right n₁).1 h
    subst this
    simp [rho]
  have : NeZero n₁ := ⟨h1.ne'⟩
  have : NeZero n₂ := ⟨h2.ne'⟩
  have : NeZero (n₁ * n₂) := ⟨by positivity⟩
  rw [rho_eq_card_zmod, rho_eq_card_zmod, rho_eq_card_zmod, ← Finset.card_product]
  set e := ZMod.chineseRemainder h with he
  have key : ∀ x : ZMod (n₁ * n₂), (x ^ 2 + (m : ZMod (n₁ * n₂)) = 0 ↔
      (e x).1 ^ 2 + (m : ZMod n₁) = 0 ∧ (e x).2 ^ 2 + (m : ZMod n₂) = 0) := by
    intro x
    have hm : e (m : ZMod (n₁ * n₂)) = ((m : ZMod n₁), (m : ZMod n₂)) := by
      rw [map_intCast]; rfl
    constructor
    · intro hx
      have := congrArg e hx
      rw [map_add, map_pow, hm, map_zero] at this
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · rintro ⟨h₁, h₂⟩
      apply e.injective
      rw [map_add, map_pow, hm, map_zero]
      exact Prod.ext h₁ h₂
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    obtain ⟨h₁, h₂⟩ := (key x).1 hx.2
    exact ⟨⟨Finset.mem_univ _, h₁⟩, Finset.mem_univ _, h₂⟩
  · intro a _ b _ hab
    exact e.injective hab
  · intro y hy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (key _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact ⟨hy.1.2, hy.2.2⟩

/-- **Lemma 5.2(a).** If `2^v E = 2^(2j)` and `n` is odd, then
`ϱ_{2^v H}(n) = ϱ_{E,H}(n)`. -/
theorem rho_eq_rhoEH {v j : ℕ} {E H : ℤ} (hE : 2 ^ v * E = 2 ^ (2 * j)) {n : ℕ}
    (hn : n % 2 = 1) : rho (2 ^ v * H) n = rhoEH E H n := by
  have hn0 : n ≠ 0 := by omega
  have hodd : Odd n := Nat.odd_iff.2 hn
  have hcop2 : Nat.Coprime (2 ^ j) n := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have hcopv : IsCoprime (n : ℤ) (2 ^ v) := by
    apply IsCoprime.pow_right
    exact Int.isCoprime_two_right.2 (by exact_mod_cast hodd)
  -- `(2^j t)² + 2^v H = 2^v (E t² + H)`
  have key : ∀ t : ℤ, (2 ^ j * t) ^ 2 + 2 ^ v * H = 2 ^ v * (E * t ^ 2 + H) := by
    intro t
    have h2 : ((2 : ℤ) ^ j) ^ 2 = 2 ^ v * E := by rw [hE, ← pow_mul, mul_comm]
    calc (2 ^ j * t) ^ 2 + 2 ^ v * H = ((2 : ℤ) ^ j) ^ 2 * t ^ 2 + 2 ^ v * H := by ring
      _ = 2 ^ v * (E * t ^ 2 + H) := by rw [h2]; ring
  have hdvd : ∀ X : ℤ, (n : ℤ) ∣ 2 ^ v * X ↔ (n : ℤ) ∣ X :=
    fun X => ⟨fun h => hcopv.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩
  -- reduction modulo `n`
  have hred : ∀ t : ℕ, ((2 ^ j * t % n : ℕ) : ℤ) ≡ 2 ^ j * t [ZMOD n] := by
    intro t
    have : ((2 ^ j * t % n : ℕ) : ℤ) = ((2 ^ j * t : ℕ) : ℤ) % (n : ℤ) := Int.natCast_mod _ _
    rw [this]
    have h := Int.mod_modEq ((2 ^ j * t : ℕ) : ℤ) (n : ℤ)
    push_cast at h ⊢
    exact h
  have htransfer : ∀ t : ℕ, ((n : ℤ) ∣ ((2 ^ j * t % n : ℕ) : ℤ) ^ 2 + 2 ^ v * H ↔
      (n : ℤ) ∣ E * (t : ℤ) ^ 2 + H) := by
    intro t
    have h1 : ((2 ^ j * t % n : ℕ) : ℤ) ^ 2 + 2 ^ v * H ≡ (2 ^ j * t) ^ 2 + 2 ^ v * H [ZMOD n] :=
      ((hred t).pow 2).add_right _
    rw [key] at h1
    rw [← hdvd (E * (t : ℤ) ^ 2 + H)]
    have hd := Int.modEq_iff_dvd.1 h1
    constructor
    · intro h
      have := dvd_add h hd
      simpa using this
    · intro h
      have := dvd_sub h hd
      simpa using this
  unfold rho rhoEH
  symm
  apply Finset.card_bij (fun t _ => 2 ^ j * t % n)
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht ⊢
    exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hn0), (htransfer t).2 ht.2⟩
  · intro t₁ ht₁ t₂ ht₂ h
    rw [Finset.mem_filter, Finset.mem_range] at ht₁ ht₂
    have h' : t₁ ≡ t₂ [MOD n] :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hcop2) h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ht₁.1, Nat.mod_eq_of_lt ht₂.1] at h'
  · intro ν hν
    rw [Finset.mem_filter, Finset.mem_range] at hν
    obtain ⟨t, ht, htν⟩ := Nat.exists_mul_mod_eq_of_coprime ν hcop2 hn0
    rw [Nat.mod_eq_of_lt hν.1] at htν
    refine ⟨t, ?_, htν⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ht, (htransfer t).1 ?_⟩
    rw [htν]
    exact hν.2

/-- `ϱ(1) = 1`. -/
theorem rho_one (m : ℤ) : rho m 1 = 1 := by
  unfold rho
  rw [show (Finset.range 1).filter (fun ν : ℕ => ((1 : ℕ) : ℤ) ∣ (ν : ℤ) ^ 2 + m) = {0} by
    ext ν; simp]
  rfl

/-- `ϱ(ℓ) = 1 + (-m/ℓ)` for an odd prime `ℓ`. -/
theorem rho_prime {m : ℤ} {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    (rho m ℓ : ℤ) = 1 + legendreSym ℓ (-m) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [rho_eq_card_zmod, add_comm, ← legendreSym.card_sqrts ℓ hℓ (-m), Set.toFinset_ofPred]
  congr 2
  apply Finset.filter_congr
  intro x _
  push_cast
  exact (eq_neg_iff_add_eq_zero).symm

/-- Hensel's lemma for `ν² + m`: for an odd prime `ℓ ∤ m` and `i ≥ 1`, reduction modulo `ℓ^i`
is a bijection from the roots modulo `ℓ^(i+1)` to the roots modulo `ℓ^i`. -/
theorem rho_succ {m : ℤ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hm : ¬ (ℓ : ℤ) ∣ m) {i : ℕ}
    (hi : 1 ≤ i) : rho m (ℓ ^ (i + 1)) = rho m (ℓ ^ i) := by
  have hℓZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hL : (0 : ℕ) < ℓ ^ i := pow_pos hℓ.pos i
  have hL0 : ((ℓ : ℤ) ^ i) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.ne_zero)
  have hℓL : (ℓ : ℤ) ∣ (ℓ : ℤ) ^ i := dvd_pow_self _ (by omega)
  have hLL : (ℓ : ℤ) ^ i ∣ (ℓ : ℤ) ^ (i + 1) := pow_dvd_pow _ (by omega)
  have h2 : ¬ (ℓ : ℤ) ∣ 2 := by
    intro h
    have : ℓ ∣ 2 := by exact_mod_cast h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  -- a root modulo `ℓ^i` is prime to `ℓ`
  have hroot : ∀ ν : ℤ, (ℓ : ℤ) ^ i ∣ ν ^ 2 + m → ¬ (ℓ : ℤ) ∣ 2 * ν := by
    intro ν hν h
    rcases hℓZ.dvd_or_dvd h with h | h
    · exact h2 h
    · apply hm
      have h1 : (ℓ : ℤ) ∣ ν ^ 2 := dvd_pow h (by norm_num)
      have := dvd_sub (hℓL.trans hν) h1
      simpa using this
  unfold rho
  apply Finset.card_bij (fun ν _ => ν % ℓ ^ i)
  · intro ν hν
    simp only [Finset.mem_filter, Finset.mem_range] at hν ⊢
    push_cast at hν ⊢
    refine ⟨Nat.mod_lt _ hL, ?_⟩
    have h1 : (ℓ : ℤ) ^ i ∣ (ν : ℤ) ^ 2 + m := hLL.trans hν.2
    have hmod : (((ν % ℓ ^ i : ℕ)) : ℤ) ≡ ν [ZMOD (ℓ : ℤ) ^ i] := by
      have : (((ν % ℓ ^ i : ℕ)) : ℤ) = (ν : ℤ) % ((ℓ : ℤ) ^ i) := by push_cast; rfl
      rw [this]; exact Int.mod_modEq _ _
    have h3 := (hmod.pow 2).add_right m
    have := dvd_sub h1 h3.dvd
    push_cast at this
    rwa [sub_sub_cancel] at this
  · intro ν₁ h₁ ν₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at h₁ h₂
    push_cast at h₁ h₂
    have hmod : (ν₁ : ℤ) ≡ ν₂ [ZMOD (ℓ : ℤ) ^ i] := by
      have := (Int.natCast_modEq_iff (n := ℓ ^ i)).2 heq
      push_cast at this; exact this
    obtain ⟨t, ht⟩ := hmod.dvd
    have hdiff := dvd_sub h₂.2 h₁.2
    have hfac : (ν₂ : ℤ) ^ 2 + m - ((ν₁ : ℤ) ^ 2 + m) =
        (ℓ : ℤ) ^ i * (t * (2 * ν₁ + (ℓ : ℤ) ^ i * t)) := by
      have : (ν₂ : ℤ) = ν₁ + (ℓ : ℤ) ^ i * t := by linarith
      rw [this]; ring
    rw [hfac, pow_succ] at hdiff
    have hdiv := (mul_dvd_mul_iff_left hL0).1 hdiff
    have ht' : (ℓ : ℤ) ∣ t := by
      rcases hℓZ.dvd_or_dvd hdiv with h | h
      · exact h
      · exfalso
        apply hroot ν₁ (hLL.trans h₁.2)
        have := dvd_sub h (dvd_mul_of_dvd_left hℓL t)
        simpa using this
    obtain ⟨s, hs⟩ := ht'
    have hdvd : (ℓ : ℤ) ^ (i + 1) ∣ (ν₂ : ℤ) - ν₁ := ⟨s, by rw [ht, hs]; ring⟩
    have : (ν₁ : ℤ) ≡ ν₂ [ZMOD ((ℓ ^ (i + 1) : ℕ) : ℤ)] := by
      push_cast; exact Int.modEq_iff_dvd.2 hdvd
    rw [Int.natCast_modEq_iff] at this
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt h₁.1, Nat.mod_eq_of_lt h₂.1] at this
  · intro μ hμ
    simp only [Finset.mem_filter, Finset.mem_range] at hμ
    push_cast at hμ
    obtain ⟨k, hk⟩ := hμ.2
    have hcop : IsCoprime (2 * (μ : ℤ)) ℓ :=
      ((hℓZ.coprime_iff_not_dvd).2 (hroot μ hμ.2)).symm
    obtain ⟨u, v, huv⟩ := hcop
    have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
    have htZ : (((-k * u) % (ℓ : ℤ)).toNat : ℤ) = (-k * u) % ℓ :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hℓpos.ne')
    have htℓ : ((-k * u) % (ℓ : ℤ)).toNat < ℓ := by
      have := Int.emod_lt_of_pos (-k * u) hℓpos
      omega
    set t : ℕ := ((-k * u) % (ℓ : ℤ)).toNat with ht
    refine ⟨μ + t * ℓ ^ i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · calc μ + t * ℓ ^ i < ℓ ^ i + t * ℓ ^ i := by omega
          _ = (t + 1) * ℓ ^ i := by ring
          _ ≤ ℓ * ℓ ^ i := Nat.mul_le_mul_right _ htℓ
          _ = ℓ ^ (i + 1) := by ring
      · push_cast
        have hkey : (ℓ : ℤ) ∣ k + 2 * μ * t + (ℓ : ℤ) ^ i * t ^ 2 := by
          have h1 : (ℓ : ℤ) ∣ (t : ℤ) - (-k * u) := by
            rw [htZ]
            exact Int.ModEq.dvd (Int.mod_modEq (-k * u) ℓ).symm
          obtain ⟨c, hc⟩ := h1
          have hℓL' : (ℓ : ℤ) ∣ (ℓ : ℤ) ^ i * t ^ 2 := dvd_mul_of_dvd_left hℓL _
          obtain ⟨e, he⟩ := hℓL'
          exact ⟨k * v + 2 * μ * c + e, by linear_combination (-k) * huv + 2 * (μ : ℤ) * hc + he⟩
        obtain ⟨c, hc⟩ := hkey
        refine ⟨c, ?_⟩
        linear_combination hk + (ℓ : ℤ) ^ i * hc
    · show (μ + t * ℓ ^ i) % ℓ ^ i = μ
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hμ.1]

/-- **Lemma 5.2(b).** For an odd prime `ℓ` with `ℓ ∤ m` and `i ≥ 1`,
`ϱ(ℓ^i) = 1 + (-m/ℓ)`. -/
theorem rho_prime_pow_of_not_dvd {m : ℤ} {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2)
    (hm : ¬ (ℓ : ℤ) ∣ m) {i : ℕ} (hi : 1 ≤ i) :
    (rho m (ℓ ^ i) : ℤ) = 1 + legendreSym ℓ (-m) := by
  induction i, hi using Nat.le_induction with
  | base => rw [pow_one]; exact rho_prime hℓ
  | succ i hi ih => rw [rho_succ Fact.out hℓ hm hi]; exact ih

/-- All roots modulo `ℓ^i` are congruent to `±ν₀` modulo `ℓ^(i - s)`, `s = ⌊min(i, v_ℓ(m))/2⌋`. -/
theorem roots_pm {m : ℤ} (hm : m ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {i : ℕ}
    {ν ν₀ : ℤ} (hν : (ℓ : ℤ) ^ i ∣ ν ^ 2 + m) (hν₀ : (ℓ : ℤ) ^ i ∣ ν₀ ^ 2 + m) :
    (ℓ : ℤ) ^ (i - min i (padicValInt ℓ m) / 2) ∣ ν - ν₀ ∨
      (ℓ : ℤ) ^ (i - min i (padicValInt ℓ m) / 2) ∣ ν + ν₀ := by
  have := Fact.mk hℓ
  set s := min i (padicValInt ℓ m) / 2 with hs
  have hab : (ℓ : ℤ) ^ i ∣ (ν - ν₀) * (ν + ν₀) := by
    have := dvd_sub hν hν₀
    convert this using 1; ring
  have hnat : ℓ ^ i ∣ (ν - ν₀).natAbs * (ν + ν₀).natAbs := by
    rw [← Int.natAbs_mul]
    have := Int.natAbs_dvd_natAbs.2 hab
    simpa [Int.natAbs_pow] using this
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := dvd_mul.1 hnat
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 (Dvd.intro _ hk.symm)
  have hk₂' : k₂ = ℓ ^ (i - j) := by
    have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hk, ← pow_add, Nat.add_sub_cancel' hj]
  subst hk₂'
  have hA : (ℓ : ℤ) ^ j ∣ ν - ν₀ := by
    rw [← Int.natAbs_dvd_natAbs]; simpa [Int.natAbs_pow] using hk₁
  have hB : (ℓ : ℤ) ^ (i - j) ∣ ν + ν₀ := by
    rw [← Int.natAbs_dvd_natAbs]; simpa [Int.natAbs_pow] using hk₂
  by_cases h1 : i - s ≤ j
  · left; exact (pow_dvd_pow _ h1).trans hA
  by_cases h2 : j ≤ s
  · right; exact (pow_dvd_pow _ (by omega)).trans hB
  exfalso
  have hA' : (ℓ : ℤ) ^ (s + 1) ∣ ν - ν₀ := (pow_dvd_pow _ (by omega)).trans hA
  have hB' : (ℓ : ℤ) ^ (s + 1) ∣ ν + ν₀ := (pow_dvd_pow _ (by omega)).trans hB
  have h2ν : (ℓ : ℤ) ^ (s + 1) ∣ 2 * ν := by
    have := dvd_add hA' hB'
    convert this using 1; ring
  have hcop : IsCoprime ((ℓ : ℤ) ^ (s + 1)) 2 := by
    apply IsCoprime.pow_left
    have := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hℓ Nat.prime_two).2 hℓ2)
    simpa using this
  have hνdvd : (ℓ : ℤ) ^ (s + 1) ∣ ν := hcop.dvd_of_dvd_mul_left h2ν
  have hν2 : (ℓ : ℤ) ^ (2 * s + 2) ∣ ν ^ 2 := by
    have := pow_dvd_pow_of_dvd hνdvd 2
    rwa [← pow_mul, show (s + 1) * 2 = 2 * s + 2 by ring] at this
  have hi2 : 2 * s + 2 ≤ i := by omega
  have hm2 : (ℓ : ℤ) ^ (2 * s + 2) ∣ m := by
    have := dvd_sub ((pow_dvd_pow _ hi2).trans hν) hν2
    simpa using this
  have hα := ((padicValInt_dvd_iff (2 * s + 2) m).1 hm2).resolve_left hm
  have : 2 * s + 2 ≤ min i (padicValInt ℓ m) := le_min hi2 hα
  omega

/-- `ϱ(ℓ^i) ≤ 2 ℓ^⌊min(i, v_ℓ(m))/2⌋`. -/
theorem rho_prime_pow_le_nat {m : ℤ} (hm : m ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (i : ℕ) : rho m (ℓ ^ i) ≤ 2 * ℓ ^ (min i (padicValInt ℓ m) / 2) := by
  classical
  set s := min i (padicValInt ℓ m) / 2 with hs
  have hsi : s ≤ i := by omega
  have hL : 0 < ℓ ^ (i - s) := pow_pos hℓ.pos _
  unfold rho
  rcases ((Finset.range (ℓ ^ i)).filter
      (fun ν : ℕ => ((ℓ ^ i : ℕ) : ℤ) ∣ (ν : ℤ) ^ 2 + m)).eq_empty_or_nonempty with hS | ⟨ν₀, hν₀⟩
  · rw [hS]; simp
  simp only [Finset.mem_filter, Finset.mem_range] at hν₀
  push_cast at hν₀
  let f : ℕ → ℕ × ℕ := fun ν =>
    (if ((ℓ : ℤ) ^ (i - s) ∣ (ν : ℤ) - ν₀) then 0 else 1, ν / ℓ ^ (i - s))
  have hcard : (Finset.range 2 ×ˢ Finset.range (ℓ ^ s)).card = 2 * ℓ ^ s := by simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn f
  · intro ν hν
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hν
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, f]
    constructor
    · split_ifs <;> norm_num
    · rw [Nat.div_lt_iff_lt_mul hL, ← pow_add, Nat.add_sub_cancel' hsi]
      exact hν.1
  · intro ν₁ h₁ ν₂ h₂ heq
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at h₁ h₂
    push_cast at h₁ h₂
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨hsign, hq⟩ := heq
    have hpm₁ := roots_pm hm hℓ hℓ2 h₁.2 hν₀.2
    have hpm₂ := roots_pm hm hℓ hℓ2 h₂.2 hν₀.2
    rw [← hs] at hpm₁ hpm₂
    have hdiff : (ℓ : ℤ) ^ (i - s) ∣ (ν₁ : ℤ) - ν₂ := by
      by_cases c₁ : (ℓ : ℤ) ^ (i - s) ∣ (ν₁ : ℤ) - ν₀ <;>
        by_cases c₂ : (ℓ : ℤ) ^ (i - s) ∣ (ν₂ : ℤ) - ν₀ <;> simp [c₁, c₂] at hsign
      · have := dvd_sub c₁ c₂
        convert this using 1; ring
      · have := dvd_sub (hpm₁.resolve_left c₁) (hpm₂.resolve_left c₂)
        convert this using 1; ring
    have hmod : ν₂ % ℓ ^ (i - s) = ν₁ % ℓ ^ (i - s) := by
      have : (ν₂ : ℤ) ≡ ν₁ [ZMOD ((ℓ ^ (i - s) : ℕ) : ℤ)] := by
        push_cast; exact Int.modEq_iff_dvd.2 hdiff
      exact (Int.natCast_modEq_iff).1 this
    rw [← Nat.div_add_mod ν₁ (ℓ ^ (i - s)), ← Nat.div_add_mod ν₂ (ℓ ^ (i - s)), hq, hmod]

/-- **Lemma 5.2(b), general bound.** For an odd prime `ℓ` and `m ≠ 0`,
`ϱ(ℓ^i) ≤ 2 ℓ^(min(i, v_ℓ(m))/2)`. -/
theorem rho_prime_pow_le {m : ℤ} (hm : m ≠ 0) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (i : ℕ) :
    (rho m (ℓ ^ i) : ℝ) ≤ 2 * (ℓ : ℝ) ^ ((min i (padicValInt ℓ m) : ℕ) / 2 : ℝ) := by
  have h := rho_prime_pow_le_nat hm hℓ hℓ2 i
  have h1 : (rho m (ℓ ^ i) : ℝ) ≤ 2 * (ℓ : ℝ) ^ (min i (padicValInt ℓ m) / 2) := by
    exact_mod_cast h
  refine h1.trans ?_
  gcongr
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hℓ.one_lt.le)
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have : (min i (padicValInt ℓ m) / 2) * 2 ≤ min i (padicValInt ℓ m) := Nat.div_mul_le_self _ _
  exact_mod_cast this

/-- **Lemma 5.2(b), consequence.** For odd `n` and `m ≠ 0`,
`ϱ(n) ≤ 2^ω(n) gcd(n, m)^(1/2)`. -/
theorem rho_le {m : ℤ} (hm : m ≠ 0) {n : ℕ} (hn : n % 2 = 1) :
    (rho m n : ℝ) ≤ 2 ^ n.primeFactors.card * Real.sqrt (Nat.gcd n m.natAbs) := by
  have hn0 : n ≠ 0 := by omega
  have hm0 : m.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hm
  have hfac : rho m n = ∏ p ∈ n.primeFactors, rho m (p ^ n.factorization p) := by
    rw [Nat.multiplicative_factorization (rho m) (fun x y h => rho_mul m h) (rho_one m) hn0,
      Nat.prod_factorization_eq_prod_primeFactors]
  set e : ℕ → ℕ := fun p => min (n.factorization p) (padicValInt p m) / 2 with he
  have hbound : rho m n ≤ ∏ p ∈ n.primeFactors, 2 * p ^ e p := by
    rw [hfac]
    apply Finset.prod_le_prod
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := Nat.dvd_of_mem_primeFactors hp
      omega
    exact rho_prime_pow_le_nat hm hpp hp2 _
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hbound
  set Q := ∏ p ∈ n.primeFactors, p ^ e p with hQ
  have hQdvd : Q ^ 2 ∣ Nat.gcd n m.natAbs := by
    rw [hQ, ← Finset.prod_pow]
    have hint : ((∏ p ∈ n.primeFactors, (p ^ e p) ^ 2 : ℕ) : ℤ) ∣
        ((Nat.gcd n m.natAbs : ℕ) : ℤ) := by
      push_cast
      apply Finset.prod_dvd_of_coprime
      · intro p hp q hq hpq
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hqq := Nat.prime_of_mem_primeFactors hq
        have : Nat.Coprime ((p ^ e p) ^ 2) ((q ^ e q) ^ 2) := by
          apply Nat.Coprime.pow; apply Nat.Coprime.pow
          exact (Nat.coprime_primes hpp hqq).2 hpq
        have := Nat.isCoprime_iff_coprime.2 this
        simpa [Function.onFun] using this
      · intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have h2e : 2 * e p ≤ min (n.factorization p) (padicValInt p m) := by
          simp only [he]; omega
        have hdn : p ^ (2 * e p) ∣ n :=
          (hpp.pow_dvd_iff_le_factorization hn0).2 (h2e.trans (min_le_left _ _))
        have hdm : p ^ (2 * e p) ∣ m.natAbs := by
          apply (hpp.pow_dvd_iff_le_factorization hm0).2
          rw [Nat.factorization_def _ hpp]
          exact h2e.trans (min_le_right _ _)
        have := Nat.dvd_gcd hdn hdm
        rw [← pow_mul, mul_comm]
        exact_mod_cast this
    exact_mod_cast hint
  have hg : 0 < Nat.gcd n m.natAbs := Nat.gcd_pos_of_pos_left _ (by omega)
  have hQle : (Q : ℝ) ≤ Real.sqrt (Nat.gcd n m.natAbs) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.le_of_dvd hg hQdvd
  calc (rho m n : ℝ) ≤ ((2 ^ n.primeFactors.card * Q : ℕ) : ℝ) := by exact_mod_cast hbound
    _ = 2 ^ n.primeFactors.card * (Q : ℝ) := by push_cast; ring
    _ ≤ 2 ^ n.primeFactors.card * Real.sqrt (Nat.gcd n m.natAbs) := by gcongr

end Triples
