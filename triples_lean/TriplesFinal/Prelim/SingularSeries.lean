import TriplesFinal.Prelim.Roots
import TriplesFinal.Assumptions.Assumptions
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Data.Nat.Squarefree

/-!
# Lemma 5.3: the singular series

For a good prime `d` with `m = m_d`: let `ψ(n) = (m/n)` (Jacobi symbol) for odd `n ≥ 1` and
`ψ(n) = 0` for even `n`, let `A_f(t) = ∑_{k ≤ t} χ(k) f(k)`, and let
`𝔏_d = ∑_{k ≥ 1} χ(k) f(k)/k` (a conditionally convergent series).

(a) `ψ` is a non-principal real Dirichlet character modulo `8m`.
(b) `A_f(t) ≪_ε t^(1/2+ε) d^(1+ε)` (uses the Pólya–Vinogradov inequality).
(c) The series `𝔏_d` converges, `|𝔏_d| ≪ d^(1+ε)`, and `𝔏_d = L(1, χ) L(1, ψ) 𝒫_d` with
    `𝒫_d ≥ (6/π²) φ(dm)/(dm)`.
(d) `𝔏_d ≫_ε d^(-ε)` (uses Siegel's theorem).

The implied constants depend only on `a`, `b` and `ε`.

This file contains the definitions and part (a). Parts (b)–(d) are in `Prelim/AfBound.lean`
(`Af_bound`) and `Prelim/SingularSeriesValue.lean` (`Ld_tendsto`, `Ld_bound`, `Ld_product`,
`Ld_lower`), with the preparations in `Prelim/Beta.lean`, `Prelim/BetaBound.lean`,
`Prelim/Abel.lean` and `Prelim/LValue.lean`.

Paper: §5.3, Lemma 5.3.
-/

namespace Triples

open ZMod Filter Topology

/-- `ψ(n) = (m/n)` for odd `n` and `ψ(n) = 0` for even `n`. -/
def psi (m : ℤ) (n : ℕ) : ℤ := if n % 2 = 1 then jacobiSym m n else 0

section PsiChar

variable (m : ℤ)

theorem psi_one : psi m 1 = 1 := by simp [psi, jacobiSym.one_right]

theorem psi_mul (a b : ℕ) : psi m (a * b) = psi m a * psi m b := by
  unfold psi
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
  · have hab : a * b % 2 = 1 := by rw [Nat.mul_mod, ha, hb]
    simp only [hab, ha, hb, ↓reduceIte]
    have : NeZero a := ⟨by omega⟩
    have : NeZero b := ⟨by omega⟩
    exact jacobiSym.mul_right m a b
  · have hab : ¬ a * b % 2 = 1 := by
      rw [Nat.mul_mod]; have : b % 2 = 0 := by omega
      rw [this]; simp
    simp [hab, hb]
  · have hab : ¬ a * b % 2 = 1 := by
      rw [Nat.mul_mod]; have : a % 2 = 0 := by omega
      rw [this]; simp
    simp [hab, ha]
  · have hab : ¬ a * b % 2 = 1 := by
      rw [Nat.mul_mod]; have : a % 2 = 0 := by omega
      rw [this]; simp
    simp [hab, ha]

theorem psi_mod (n : ℕ) : psi m (n % (8 * m.natAbs)) = psi m n := by
  unfold psi
  have h2 : (n % (8 * m.natAbs)) % 2 = n % 2 :=
    Nat.mod_mod_of_dvd n (Dvd.intro (4 * m.natAbs) (by ring))
  rw [h2]
  split_ifs with h
  · have hodd : Odd n := Nat.odd_iff.2 h
    have hodd' : Odd (n % (8 * m.natAbs)) := Nat.odd_iff.2 (h2 ▸ h)
    rw [jacobiSym.mod_right m hodd, jacobiSym.mod_right m hodd',
      Nat.mod_mod_of_dvd n (Dvd.intro 2 (by ring) : 4 * m.natAbs ∣ 8 * m.natAbs)]
  · rfl

theorem psi_eq_zero_of_not_coprime {n : ℕ} (h : ¬ Nat.Coprime n (8 * m.natAbs)) :
    psi m n = 0 := by
  unfold psi
  split_ifs with hn
  · have : NeZero n := ⟨by omega⟩
    apply jacobiSym.eq_zero_iff_not_coprime.2
    intro hg
    apply h
    have hg' : Nat.Coprime m.natAbs n := by
      have : Int.gcd m n = 1 := hg
      simpa [Int.gcd] using this
    have h8 : Nat.Coprime n 8 := by
      have : Nat.Coprime n 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 hn)
      simpa using this.pow_right 3
    exact Nat.Coprime.mul_right h8 hg'.symm
  · rfl

/-- `ψ` as a Dirichlet character modulo `8|m|`. -/
noncomputable def psiChar (hm : m ≠ 0) : DirichletCharacter ℂ (8 * m.natAbs) where
  toFun x := (psi m x.val : ℂ)
  map_one' := by
    have : Fact (1 < 8 * m.natAbs) := ⟨by have := Int.natAbs_pos.2 hm; omega⟩
    simp only [ZMod.val_one, psi_one, Int.cast_one]
  map_mul' x y := by
    rw [ZMod.val_mul, psi_mod m, psi_mul, Int.cast_mul]
  map_nonunit' x hx := by
    have : NeZero (8 * m.natAbs) := ⟨by have := Int.natAbs_pos.2 hm; omega⟩
    rw [psi_eq_zero_of_not_coprime m, Int.cast_zero]
    intro hcop
    apply hx
    have := (ZMod.unitOfCoprime x.val hcop).isUnit
    rwa [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val] at this

theorem psiChar_apply (hm : m ≠ 0) (n : ℕ) : psiChar m hm n = (psi m n : ℂ) := by
  show (psi m ((n : ZMod (8 * m.natAbs)).val) : ℂ) = _
  rw [ZMod.val_natCast, psi_mod m]

theorem psiChar_sq (hm : m ≠ 0) : psiChar m hm ^ 2 = 1 := by
  ext u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hcop : Nat.Coprime (u : ZMod (8 * m.natAbs)).val (8 * m.natAbs) := ZMod.val_coe_unit_coprime u
  show ((psi m (u : ZMod (8 * m.natAbs)).val : ℂ)) ^ 2 = 1
  set v := (u : ZMod (8 * m.natAbs)).val
  have hodd : v % 2 = 1 := by
    have : Nat.Coprime v 2 := Nat.Coprime.coprime_dvd_right (Dvd.intro (4 * m.natAbs) (by ring)) hcop
    exact Nat.odd_iff.1 (Nat.coprime_two_right.1 this)
  unfold psi
  simp only [hodd, ↓reduceIte]
  have hg : m.gcd (v : ℤ) = 1 := by
    have : Nat.Coprime v m.natAbs := Nat.Coprime.coprime_dvd_right (Dvd.intro_left 8 rfl) hcop
    show m.natAbs.gcd (v : ℤ).natAbs = 1
    simpa [Nat.coprime_comm] using this
  have := jacobiSym.sq_one hg
  exact_mod_cast this

theorem psiChar_ne_one (hm : m ≠ 0) {n : ℕ} (hn : psi m n = -1) : psiChar m hm ≠ 1 := by
  intro h
  have h1 := psiChar_apply m hm n
  rw [h, hn] at h1
  by_cases hu : IsUnit (n : ZMod (8 * m.natAbs))
  · rw [MulChar.one_apply hu] at h1; norm_num at h1
  · rw [MulChar.map_nonunit _ hu] at h1; norm_num at h1

end PsiChar

/-- If `m > 0` is not a perfect square, then `J(m | n) = -1` for some odd `n` (proof of
Lemma 5.3(a)). -/
theorem exists_jacobiSym_eq_neg_one {m : ℤ} (hm : 0 < m) (hsq : ¬ ∃ s : ℤ, m = s ^ 2) :
    ∃ n : ℕ, n % 2 = 1 ∧ jacobiSym m n = -1 := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = M := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  have hM : 0 < M := by exact_mod_cast hm
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hM
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hsq ⟨b, by rw [← hab]; push_cast; ring⟩
  by_cases hodd : ∃ p, p.Prime ∧ p ∣ a ∧ p ≠ 2
  · -- an odd prime `p` divides `M` to an odd power
    obtain ⟨p, hp, ⟨a', rfl⟩, hp2⟩ := hodd
    have hpa' : ¬ p ∣ a' := by
      rintro ⟨c, rfl⟩
      have := hsf p ⟨c, by ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
    obtain ⟨s, b', hpb', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
    set w := b' ^ 2 * a' with hw
    have hMw : M = p ^ (2 * s + 1) * w := by rw [← hab, hw]; ring
    have hpw : ¬ p ∣ w := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hpb' (hp.dvd_of_dvd_pow h)
      · exact hpa' h
    have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have := Fact.mk hp
    obtain ⟨g, hg⟩ : ∃ g : ℤ, legendreSym p g = -1 := by
      obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
      refine ⟨x.val, ?_⟩
      rw [legendreSym.eq_neg_one_iff]
      simpa using hx
    have hcop : Nat.Coprime (8 * w) p := by
      apply Nat.coprime_mul_iff_left.2
      refine ⟨?_, ?_⟩
      · have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
        simpa using this.pow_left 3
      · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpw))
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop 1 (g % p).toNat
    have hn8 : n % 8 = 1 := by
      have := (Nat.ModEq.of_mul_right w hn1)
      unfold Nat.ModEq at this; simpa using this
    refine ⟨n, by omega, ?_⟩
    have hn_odd : Odd n := Nat.odd_iff.2 (by omega)
    -- `J(w | n) = 1`, since `n ≡ 1 (mod 4w)`
    have hJw : jacobiSym (w : ℤ) n = 1 := by
      rw [jacobiSym.mod_right _ hn_odd]
      have h4 : n % (4 * (w : ℤ).natAbs) = 1 := by
        rw [Int.natAbs_natCast]
        have := Nat.ModEq.of_mul_left 2 (show n ≡ 1 [MOD 2 * (4 * w)] by
          rw [show 2 * (4 * w) = 8 * w by ring]; exact hn1)
        unfold Nat.ModEq at this
        rw [this]
        apply Nat.mod_eq_of_lt
        have : 0 < w := by
          rcases Nat.eq_zero_or_pos w with h | h
          · rw [h] at hMw; omega
          · exact h
        omega
      rw [h4, jacobiSym.one_right]
    -- `J(p | n) = J(n | p) = (g/p) = -1`
    have hJp : jacobiSym (p : ℤ) n = -1 := by
      rw [← jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hp_odd]
      rw [← hg, jacobiSym.legendreSym.to_jacobiSym]
      apply jacobiSym.mod_left'
      have h2 : ((g % p).toNat : ℤ) = g % p :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero))
      have h1 : n % p = (g % p).toNat := by
        have := hn2; unfold Nat.ModEq at this
        rw [this]; apply Nat.mod_eq_of_lt
        have : ((g % p).toNat : ℤ) < p := by
          rw [h2]; exact Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
        exact_mod_cast this
      rw [← Int.natCast_mod, h1, h2]
    rw [hMw]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, hJp, hJw]
    rw [pow_succ, pow_mul]
    norm_num
  · -- otherwise `a = 2` and `M = 2^(2s+1) b'^2` with `b'` odd
    push Not at hodd
    have ha2 : a = 2 := by
      obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha1
      have hq2 := hodd q hq hqa
      subst hq2
      obtain ⟨a', rfl⟩ := hqa
      by_contra hne
      have ha'1 : a' ≠ 1 := by rintro rfl; exact hne rfl
      obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd ha'1
      have hr2 := hodd r hr (Dvd.dvd.mul_left hra 2)
      subst hr2
      obtain ⟨c, rfl⟩ := hra
      have := hsf 2 ⟨c, by ring⟩
      exact absurd (Nat.isUnit_iff.1 this) (by norm_num)
    subst ha2
    obtain ⟨s, b', hb'odd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hb.ne'
    set w := b' ^ 2 with hw
    have hw_odd : Odd w := hb'odd.pow
    have hMw : M = 2 ^ (2 * s + 1) * w := by rw [← hab, hw]; ring
    have hcop : Nat.Coprime 8 w := by
      have : Nat.Coprime 2 w := Nat.coprime_two_left.2 hw_odd
      simpa using this.pow_left 3
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop 5 1
    have hn8 : n % 8 = 5 := by
      have := hn1; unfold Nat.ModEq at this; simpa using this
    refine ⟨n, by omega, ?_⟩
    have hn_odd : Odd n := Nat.odd_iff.2 (by omega)
    have hJ2 : jacobiSym 2 n = -1 := by
      have h2 : n % 2 = 1 := by omega
      rw [jacobiSym.at_two hn_odd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hn8, h2]
    have hJw : jacobiSym (w : ℤ) n = 1 := by
      have := jacobiSym.quadratic_reciprocity_one_mod_four (a := n) (b := w) (by omega) hw_odd
      rw [← this]
      rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
      have h1 : n % w = 1 % w := hn2
      rw [← Int.natCast_mod, h1]
      push_cast
      rfl
    rw [hMw]
    push_cast
    rw [jacobiSym.mul_left, jacobiSym.pow_left, hJ2, hJw]
    rw [pow_succ, pow_mul]
    norm_num


namespace PatternData

variable {a b : ℕ} (P : PatternData a b)

/-- `A_f(t) = ∑_{k ≤ t} χ(k) f(k)`. -/
noncomputable def Af (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (χ₄ (k : ZMod 4) : ℝ) * P.fd d k

/-- The partial sums `∑_{k < N} χ(k) f(k)/k` of the singular series. -/
noncomputable def LdPartial (d N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (χ₄ (k : ZMod 4) : ℝ) * P.fd d k / k

/-- The singular series `𝔏_d = ∑_{k ≥ 1} χ(k) f(k)/k`, defined as the limit of the partial
sums (it converges by Lemma 5.3(c)). -/
noncomputable def Ld (d : ℕ) : ℝ := limUnder atTop (P.LdPartial d)

variable {P}

/-- **Lemma 5.3(a).** For a good prime `d`, `ψ` is a non-principal real Dirichlet character
modulo `8 m_d`. -/
theorem IsGood.psi_character {d : ℕ} (hd : P.IsGood d) :
    ∃ ψ' : DirichletCharacter ℂ (8 * (P.m d).natAbs), ψ' ≠ 1 ∧ ψ' ^ 2 = 1 ∧
      ∀ n : ℕ, ψ' n = (psi (P.m d) n : ℂ) := by
  have hm : 0 < P.m d := P.m_pos (d := (d : ℤ)) hd.d₁_lt
  obtain ⟨n, hn2, hn⟩ := exists_jacobiSym_eq_neg_one hm hd.2.2.2.1
  refine ⟨psiChar (P.m d) hm.ne', psiChar_ne_one _ _ (n := n) ?_, psiChar_sq _ _,
    psiChar_apply _ _⟩
  simp [psi, hn2, hn]

end PatternData

end Triples
