import Quantum.Hadamard.PowerThreeModFour

/-! Frobenius-stretched seeds and the eventual order spectrum at odd prime powers. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.Arithmetic.PowerResidues

/-- The arithmetic specifications of the stretched Paley construction. -/
def FrobeniusSeeds (m : ℕ) : Prop :=
  ∀ t : ℕ, t.Prime → t % 4 = 3 →
    ∃ h > 0, AtOrder m h ∧ h ≡ 2 [MOD 4] ∧ h ≡ 2 * (t^2 + 1) [MOD m]

/-- Singular classes are represented by twice a prime square plus two.
The prime can simultaneously be chosen three modulo four. -/
theorem singular_frobenius_prime {p a r : ℕ} (pp : p.Prime) (p4 : p % 4 = 1)
    (singular : p ∣ r) :
    ∃ t : ℕ, t.Prime ∧ t % 4 = 3 ∧ 2 * (t^2 + 1) ≡ r [MOD p^(a+1)] := by
  let m := p^(a+1)
  let : Fact p.Prime := ⟨pp⟩
  have po : 2 < p := by have := pp.two_le; omega
  have mp : 0 < m := pow_pos pp.pos _
  have om : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right _
  let two := ZMod.unitOfCoprime 2 om
  have two_val : (two : ZMod m) = 2 := by
    simpa only [Nat.cast_ofNat] using ZMod.coe_unitOfCoprime 2 om
  let x := (r : ZMod m) * (↑two⁻¹ : ZMod m) - 1
  have rx : red p a x = -1 := by
    simp only [x, map_sub, map_mul, map_one, map_natCast,
      (ZMod.natCast_eq_zero_iff _ _).mpr singular, zero_mul, zero_sub]
  have ux : IsUnit x := unit_of_red (p:=p) (a:=a) (rx ▸ neg_ne_zero.mpr one_ne_zero)
  have sx : IsSquare (red p a x) := rx ▸ ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨z, hz⟩ := square_of_red (p:=p) (a:=a) po ux sx
  have uz : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ ux : IsUnit (z*z))
  obtain ⟨t, _, tp, tz, t4⟩ := realize_unit_prime mp om uz 3 (by decide) 2
  refine ⟨t, tp, t4, (ZMod.natCast_eq_natCast_iff _ _ m).mp ?_⟩
  push_cast
  calc
    2 * ((t : ZMod m)^2 + 1) = 2 * (x + 1) := by rw [tz, pow_two, ← hz]
    _ = (r : ZMod m) := by
      rw [← two_val]
      dsimp only [x]
      simp [mul_left_comm]

/-- It suffices to construct one twice-odd seed for each singular residue.
The period of the two lexicographic steps can then be made exactly four
times the modulus. -/
theorem complete_prime_power_of_singular_twice_seeds {p : ℕ}
    (pp : p.Prime) (po : 2 < p) (e : ℕ)
    (singularSeeds : ∀ r : ℕ, p ∣ r →
      ∃ h > 0, AtOrder (p^e) h ∧ h ≡ 2 [MOD 4] ∧ h ≡ r [MOD p^e]) :
    ∃ B : ℕ, ∀ n ≥ B, IntegralSolution (p^e) n ↔ Even n ∨ IsSquare (n : ZMod (p^e)) := by
  classical
  obtain _|a := e
  · simpa using prime_power_units_classification pp po 0
  let m := p^(a+1)
  have mh : 1 < m := lt_of_lt_of_le pp.one_lt (Nat.le_self_pow (by omega : a+1≠0) _)
  have om := (two_coprime_prime pp po).pow_right (a+1)
  obtain ⟨U, units⟩ := prime_power_units_classification pp po (a+1)
  obtain ⟨A, fours⟩ := large_four_two_prime_powers pp pp po po (a+1) 0
  obtain ⟨S, squares⟩ := all_large_prime_power_squares pp po (a+1)
  have cls (i : Fin m) :
      ∃ B : ℕ, ∀ n ≥ B, n ≡ i.val [MOD m] → n ≡ 2 [MOD 4] → AtOrder m n := by
    by_cases cu : i.val.Coprime m
    · refine ⟨U, fun n hn ni n4 =>
        atOrder_of_integral ((units n hn (coprime_of_modEq ni cu)).mpr (Or.inl ?_))⟩
      change n%4=2 at n4
      rw [Nat.even_iff]
      omega
    have pi : p ∣ i.val := by
      by_contra h
      exact cu ((pp.coprime_iff_not_dvd.mpr h).symm.pow_right _)
    obtain ⟨h, hp, H, h4, hr⟩ := singularSeeds i.val pi
    let b := i.val+m-1
    have ri : i.val ≡ b+1 [MOD m] := by
      rw [show b+1=i.val+m by dsimp [b]; omega]
      simp [Nat.ModEq]
    have pm : p ∣ m := dvd_pow_self p (by omega : a+1≠0)
    have pb : ¬p ∣ b := by
      intro dv
      have ds : p ∣ b+1 := by
        rw [show b+1=i.val+m by dsimp [b]; omega]
        exact dvd_add pi pm
      exact pp.not_dvd_one (by simpa using Nat.dvd_sub ds dv)
    obtain ⟨B, all⟩ := composite_seed_class mh om ((pp.coprime_iff_not_dvd.mpr pb).symm.pow_right _)
      (hr.trans ri) (primeConstruction m) hp H
    exact ⟨B, fun n hn ni n4 => all n hn (n4.trans h4.symm) (ni.trans hr.symm)⟩
  choose bounds spec using cls
  refine ⟨max (Finset.univ.sup bounds) (max A S), ?_⟩
  intro n hn
  constructor
  · intro H
    rcases Nat.even_or_odd n with ev|od
    · exact Or.inl ev
    · exact Or.inr (odd_prime_power_necessary pp od H)
  · rintro (ev|sq)
    · by_cases four : 4 ∣ n
      · apply integer_gram
        apply at_weaker_modulus (dvd_mul_left m 4)
        simpa [m] using fours n (by omega) four
      have two : n ≡ 2 [MOD 4] := by
        have h := Nat.even_iff.mp ev
        have f := mt Nat.dvd_of_mod_eq_zero four
        change n%4=2
        omega
      let i : Fin m := ⟨n%m, Nat.mod_lt _ (by omega)⟩
      exact integer_gram (spec i n ((Finset.le_sup (f:=bounds) (Finset.mem_univ i)).trans
        (by omega)) (Nat.mod_modEq n m).symm two)
    · exact integer_gram (squares n (by omega) sq)

theorem split_prime_power_of_frobenius {p : ℕ} (pp : p.Prime) (p4 : p % 4 = 1)
    (e : ℕ) (seeds : FrobeniusSeeds (p^e)) :
    ∃ B : ℕ, ∀ n ≥ B, IntegralSolution (p^e) n ↔ Even n ∨ IsSquare (n : ZMod (p^e)) := by
  obtain _|a := e
  · simpa using prime_power_units_classification pp (by have := pp.two_le; omega) 0
  apply complete_prime_power_of_singular_twice_seeds pp (by have := pp.two_le; omega)
  intro r pr
  obtain ⟨t, tp, t4, tr⟩ := singular_frobenius_prime (a:=a) pp p4 pr
  obtain ⟨h, hp, H, h4, ht⟩ := seeds t tp t4
  exact ⟨h, hp, H, h4, ht.trans tr⟩

/-- The complete eventual spectrum, conditional only on the geometric Frobenius
seed construction in the split case. The exponent may be zero. -/
theorem odd_prime_power_spectrum_of_frobenius {p : ℕ} (pp : p.Prime) (po : 2 < p)
    (e : ℕ) (seeds : p % 4 = 1 → FrobeniusSeeds (p^e)) :
    ∃ B : ℕ, ∀ n ≥ B, IntegralSolution (p^e) n ↔
      4 ∣ n ∨ (n % 4 = 2 ∧ (p % 4 = 1 ∨ p^e ∣ n ∨ Even (n.factorization p))) ∨
        (Odd n ∧ IsSquare (n : ZMod (p^e))) := by
  by_cases split : p%4=1
  · obtain ⟨B, all⟩ := split_prime_power_of_frobenius pp split e (seeds split)
    refine ⟨B, fun n hn => (all n hn).trans ?_⟩
    simp only [split, true_or, and_true]
    have even_iff : Even n ↔ 4 ∣ n ∨ n%4=2 := by rw [Nat.even_iff]; omega
    constructor
    · rintro (ev|sq)
      · rcases even_iff.mp ev with f|t
        · exact Or.inl f
        · exact Or.inr (Or.inl t)
      · rcases Nat.even_or_odd n with ev|od
        · rcases even_iff.mp ev with f|t
          · exact Or.inl f
          · exact Or.inr (Or.inl t)
        · exact Or.inr (Or.inr ⟨od,sq⟩)
    · rintro (f|t|⟨_,sq⟩)
      · exact Or.inl (even_iff.mpr (Or.inl f))
      · exact Or.inl (even_iff.mpr (Or.inr t))
      · exact Or.inr sq
  · have odd := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
    have inert : p%4=3 := by omega
    simpa only [split, false_or] using three_mod_four_prime_power_classification pp inert e

#print axioms singular_frobenius_prime
#print axioms split_prime_power_of_frobenius
#print axioms odd_prime_power_spectrum_of_frobenius
end HadamardMod
