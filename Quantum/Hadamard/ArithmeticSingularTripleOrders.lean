import Quantum.Hadamard.ArithmeticSingularTripleCenters
import Quantum.Hadamard.CompositeConductorSpectrum
import Quantum.Hadamard.ArithmeticParityLift

/-! Uniform order bounds for all odd moduli supported on at most three primes. -/
noncomputable section
namespace HadamardMod.TripleRouting

theorem admissible_double {m k : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (ok : CompositeAdmissible m k) : CompositeAdmissible m (2*k) := by
  obtain ⟨h,_,H,hc⟩ := (composite_progression_spectrum mp om).mp ok (4*m) (by omega) 0
  have full := at_mul (order_two m) (atOrder_of_integral H)
  exact composite_admissible_of_congr mp (hc.mul_left 2) (composite_necessary mp om (integer_gram full))

theorem triple_large_fourfold {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) :
    ∃ B : ℕ, ∀ k≥B, CompositeAdmissible m k → AtOrder m (4*k) := by
  obtain ⟨C,large⟩ := odd_modulus_spectrum_at_three_centers mp om
  refine ⟨max C 2,?_⟩
  intro k hk eligible
  rcases centers_after_two_halvings mp om small (by omega : 2≤k) with h|h|h
  · exact atOrder_of_integral ((large _ (by omega) h).mpr (Or.inl (dvd_mul_right 4 k)))
  · have half := atOrder_of_integral ((large _ (by omega) h).mpr (admissible_double mp om eligible))
    simpa only [←Nat.mul_assoc,show (2:ℕ)*2=4 by decide] using at_mul (order_two m) half
  · have quarter := atOrder_of_integral ((large _ (by omega) h).mpr eligible)
    exact at_mul (at_mul (order_two m) (order_two m)) quarter

theorem triple_large_twofold_no_three {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (no3 : ¬3∣m) :
    ∃ B : ℕ, ∀ k≥B, CompositeAdmissible m k → AtOrder m (2*k) := by
  obtain ⟨C,large⟩ := odd_modulus_spectrum_at_three_centers mp om
  refine ⟨max C 2,?_⟩
  intro k hk eligible
  rcases centers_after_one_halving mp om small no3 (by omega : 2≤k) with h|h
  · exact atOrder_of_integral ((large _ (by omega) h).mpr (admissible_double mp om eligible))
  · exact at_mul (order_two m) (atOrder_of_integral ((large _ (by omega) h).mpr eligible))

theorem triple_all_large_sixteen {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) :
    ∃ B : ℕ, ∀ n≥B, 16∣n → IntegralSolution m n := by
  obtain ⟨K,H⟩ := triple_large_fourfold mp om small
  refine ⟨16*K,?_⟩
  rintro n hn ⟨u,rfl⟩
  have mat := H (4*u) (by omega) (Or.inl (dvd_mul_right 4 u))
  exact integer_gram (by simpa only [←Nat.mul_assoc,show (4:ℕ)*4=16 by decide] using mat)

theorem triple_all_large_eight_no_three {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (no3 : ¬3∣m) :
    ∃ B : ℕ, ∀ n≥B, 8∣n → IntegralSolution m n := by
  obtain ⟨K,H⟩ := triple_large_twofold_no_three mp om small no3
  refine ⟨8*K,?_⟩
  rintro n hn ⟨u,rfl⟩
  have mat := H (4*u) (by omega) (Or.inl (dvd_mul_right 4 u))
  exact integer_gram (by simpa only [←Nat.mul_assoc,show (2:ℕ)*4=8 by decide] using mat)

def SimpleInertFactors (m : ℕ) : Prop :=
  ∀ p∈m.primeFactors, p%4=1 ∨ m.factorization p=1

theorem even_admissible_of_simple_inert {m n : ℕ} (simple : SimpleInertFactors m)
    (even : Even n) : CompositeAdmissible m n := by
  by_cases f : 4∣n
  · exact Or.inl f
  have e := Nat.even_iff.mp even
  refine Or.inr (Or.inl ⟨by omega,?_⟩)
  intro p hp
  rcases simple p hp with split|one
  · exact Or.inl split
  by_cases d : p∣n
  · exact Or.inr (Or.inl (by simpa [one] using d))
  · exact Or.inr (Or.inr (by simp [Nat.factorization_eq_zero_of_not_dvd d]))

theorem triple_all_large_eight_simple_inert {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (simple : SimpleInertFactors m) :
    ∃ B : ℕ, ∀ n≥B, 8∣n → IntegralSolution m n := by
  obtain ⟨K,H⟩ := triple_large_fourfold mp om small
  refine ⟨8*K,?_⟩
  rintro n hn ⟨u,rfl⟩
  have mat := H (2*u) (by omega) (even_admissible_of_simple_inert simple (even_two_mul u))
  exact integer_gram (by simpa only [←Nat.mul_assoc,show (4:ℕ)*2=8 by decide] using mat)

theorem triple_all_large_four_simple_inert {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (no3 : ¬3∣m) (simple : SimpleInertFactors m) :
    ∃ B : ℕ, ∀ n≥B, 4∣n → IntegralSolution m n := by
  obtain ⟨K,H⟩ := triple_large_twofold_no_three mp om small no3
  refine ⟨4*K,?_⟩
  rintro n hn ⟨u,rfl⟩
  have mat := H (2*u) (by omega) (even_admissible_of_simple_inert simple (even_two_mul u))
  exact integer_gram (by simpa only [←Nat.mul_assoc,show (2:ℕ)*2=4 by decide] using mat)

/-- One additional doubling raises the modulus to four times its odd part. -/
theorem triple_four_modulus_eightfold {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) :
    ∃ B : ℕ, ∀ k≥B, CompositeAdmissible m k → AtOrder (4*m) (8*k) := by
  obtain ⟨K,H⟩ := triple_large_fourfold mp om small
  refine ⟨K,fun k hk ok => ?_⟩
  have ev : Even (4*k) := ⟨2*k,by omega⟩
  simpa only [←Nat.mul_assoc,show (2:ℕ)*4=8 by decide] using at_doubled_order_four_modulus om ev (H k hk ok)

theorem triple_four_modulus_fourfold_no_three {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (no3 : ¬3∣m) :
    ∃ B : ℕ, ∀ k≥B, CompositeAdmissible m k → AtOrder (4*m) (4*k) := by
  obtain ⟨K,H⟩ := triple_large_twofold_no_three mp om small no3
  refine ⟨K,fun k hk ok => ?_⟩
  simpa only [←Nat.mul_assoc,show (2:ℕ)*2=4 by decide] using
    at_doubled_order_four_modulus om (even_two_mul k) (H k hk ok)

#print axioms triple_large_fourfold
#print axioms triple_large_twofold_no_three
#print axioms triple_all_large_sixteen
#print axioms triple_all_large_four_simple_inert
#print axioms triple_four_modulus_eightfold
end HadamardMod.TripleRouting
