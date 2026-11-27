import Quantum.Hadamard.PowerAllTwice
import Quantum.Hadamard.ArithmeticEvenObstruction

/-! Eventual classification at every power of a prime three modulo four, with no
restriction on the order or its common divisors with the modulus. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

theorem square_factor_of_valuation {p e n:ℕ} (pp:p.Prime) (nz:n≠0)
    (eligible:p^e∣n ∨ Even (n.factorization p)) : SquareTimesUnit (n:ZMod (p^e)) := by
  rcases eligible with dv|ev
  · exact ⟨1,0,by rw [(ZMod.natCast_eq_zero_iff _ _).mpr dv]; simp⟩
  obtain ⟨k,hk⟩ := ev
  let v := n.factorization p
  let u := n/(p^v)
  have nu : n=p^v*u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have cu : u.Coprime (p^e) := (Nat.coprime_ordCompl pp nz).symm.pow_right e
  have iu := (ZMod.isUnit_iff_coprime u (p^e)).mpr cu
  refine ⟨iu.unit,(p:ZMod (p^e))^k,?_⟩
  rw [iu.unit_spec,←pow_mul,show k*2=v by dsimp [v];omega]
  conv_lhs => rw [nu]
  push_cast
  ring

theorem three_mod_four_prime_power_classification {p:ℕ} (pp:p.Prime) (p4:p%4=3) (e:ℕ) :
    ∃ B : ℕ, ∀ n ≥ B, IntegralSolution (p^e) n ↔
      4∣n ∨ (n%4=2 ∧ (p^e∣n ∨ Even (n.factorization p))) ∨
      (Odd n ∧ IsSquare (n:ZMod (p^e))) := by
  have po : 2<p := by omega
  obtain ⟨A,ha⟩ := large_four_two_prime_powers pp pp po po e 0
  obtain ⟨C,hc⟩ := power_even_square_factor pp po e
  obtain ⟨D,hd⟩ := odd_prime_power_classification pp po e
  refine ⟨1+max A (max C D),?_⟩
  intro n hn
  have nz : n≠0 := by omega
  constructor
  · intro H
    by_cases four : 4∣n
    · exact Or.inl four
    rcases Nat.even_or_odd n with ev|od
    · have two : n%4=2 := by
        have h := Nat.even_iff.mp ev
        have f := mt Nat.dvd_of_mod_eq_zero four
        omega
      refine Or.inr (Or.inl ⟨two,?_⟩)
      by_cases full : p^e∣n
      · exact Or.inl full
      right
      by_contra bad
      have ve : n.factorization p < e := by
        by_contra! ge
        exact full ((pp.pow_dvd_iff_le_factorization nz).mpr ge)
      exact no_even_singular_valuation pp p4 two ve (Nat.not_even_iff_odd.mp bad) H
    · exact Or.inr (Or.inr ⟨od,odd_prime_power_necessary pp od H⟩)
  · rintro (four|⟨two,good⟩|⟨od,square⟩)
    · apply integer_gram
      apply at_weaker_modulus (dvd_mul_left (p^e) 4)
      simpa using ha n (by omega) four
    · have ev : Even n := by rw [Nat.even_iff]; omega
      exact integer_gram (hc n (by omega) ev (square_factor_of_valuation pp nz good))
    · exact (hd n (by omega) od).mpr square

#print axioms three_mod_four_prime_power_classification
end HadamardMod
