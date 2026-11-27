import Quantum.Hadamard.ThreeCenterConductor
import Quantum.Hadamard.ArithmeticSingularCompositeDense
import Quantum.Hadamard.TorusOddCompositeConsequences

/-! Which congruence classes contain modular Hadamard orders for an arbitrary
positive odd modulus, and which orders occur eventually for a product of at
most two odd prime powers. -/
noncomputable section
namespace HadamardMod

def CompositeAdmissible (m n : ℕ) : Prop :=
  4∣n ∨ (n%4=2 ∧ TwiceLocallyAdmissible m n) ∨ (Odd n ∧ IsSquare (n:ZMod m))

theorem composite_necessary {m n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (H : IntegralSolution m n) : CompositeAdmissible m n := by
  by_cases four : 4∣n
  · exact Or.inl four
  by_cases two : n%4=2
  · exact Or.inr (Or.inl ⟨two,twice_necessary_at_odd_modulus mp om two H⟩)
  have nz : n%4≠0 := fun h => four (Nat.dvd_of_mod_eq_zero h)
  have odd : Odd n := Nat.odd_iff.mpr (by omega)
  exact Or.inr (Or.inr ⟨odd,odd_integral_necessary mp odd H⟩)

theorem composite_admissible_of_congr {m r n : ℕ} (mp : 0 < m)
    (res : r ≡ n [MOD 4*m]) (ok : CompositeAdmissible m r) : CompositeAdmissible m n := by
  have four := res.of_dvd (dvd_mul_right 4 m)
  have base := res.of_dvd (dvd_mul_left m 4)
  rcases ok with f|⟨two,localOk⟩|⟨odd,sq⟩
  · exact Or.inl ((res.dvd_iff (dvd_mul_right 4 m)).mp f)
  · have n4 : n%4=2 := (show r%4=n%4 from four).symm.trans two
    exact Or.inr (Or.inl ⟨n4,twice_admissible_of_congr mp base localOk⟩)
  · have par : r%2=n%2 := four.of_dvd (by decide : 2∣4)
    refine Or.inr (Or.inr ⟨Nat.odd_iff.mpr (par.symm.trans (Nat.odd_iff.mp odd)),?_⟩)
    rwa [←(ZMod.natCast_eq_natCast_iff _ _ _).mpr base]

/-- Every arithmetic progression through a locally admissible order contains
arbitrarily large realizations, for any positive odd modulus. -/
theorem composite_progression_spectrum {m n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    CompositeAdmissible m n ↔ ∀ A : ℕ, 0 < A → ∀ N : ℕ,
      ∃ h>N, IntegralSolution m h ∧ h ≡ n [MOD A] := by
  constructor
  · intro ok A ap N
    rcases ok with ⟨w,rfl⟩|⟨two,localOk⟩|⟨_,sq⟩
    · obtain ⟨h,big,H,res⟩ := dense_four_seeds mp om ap w N
      exact ⟨h,big,integer_gram (at_weaker_modulus (dvd_mul_left m 4) H),
        res.of_dvd (dvd_mul_left A 4)⟩
    · obtain ⟨h,big,H,_,res⟩ := dense_composite_twice mp om ap two localOk N
      exact ⟨h,big,integer_gram H,res⟩
    · obtain ⟨h,big,H,res⟩ := TorusOddComposite.square_dense_above mp om
          (Nat.mul_pos mp ap) (dvd_mul_right m A) sq N
      exact ⟨h,big,integer_gram H,res.of_dvd (dvd_mul_left A m)⟩
  · intro hits
    obtain ⟨h,_,H,hn⟩ := hits (4*m) (by omega) 0
    exact composite_admissible_of_congr mp hn (composite_necessary mp om H)

theorem odd_modulus_spectrum_at_three_centers {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    ∃ B : ℕ, ∀ n≥B, ThreeUnitCenters m n →
      (IntegralSolution m n ↔ CompositeAdmissible m n) := by
  by_cases tiny : m=1
  · subst m
    refine ⟨0,fun n _ _ => ⟨composite_necessary mp om,fun _ => ?_⟩⟩
    exact integer_gram (ones (Subsingleton.elim _ _))
  have dense (a : ℕ) (ap : 0 < a) (_ : 4*m∣a) (n : ℕ) (ok : CompositeAdmissible m n) :
      ∃ h>0, AtOrder m h ∧ h ≡ n [MOD a] := by
    obtain ⟨h,hp,H,cong⟩ := (composite_progression_spectrum mp om).mp ok a ap 0
    exact ⟨h,hp,atOrder_of_integral H,cong⟩
  obtain ⟨B,large⟩ := cofinite_at_three_centers (by omega) om (CompositeAdmissible m) dense
  exact ⟨B,fun n hn c => ⟨composite_necessary mp om,fun h => integer_gram (large n hn h c)⟩⟩

/-- The entire eventual spectrum for two arbitrary odd prime powers. The
primes may coincide and both exponents are unrestricted. -/
theorem two_prime_power_spectrum {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : 2<p) (qo : 2<q) (a b : ℕ) :
    ∃ B : ℕ, ∀ n≥B, IntegralSolution (p^a*q^b) n ↔ CompositeAdmissible (p^a*q^b) n := by
  have pos := Nat.mul_pos (pow_pos pp.pos a) (pow_pos qp.pos b)
  have odd := ((Hadamard.Arithmetic.two_coprime_prime pp po).pow_right a).mul_right
    ((Hadamard.Arithmetic.two_coprime_prime qp qo).pow_right b)
  obtain ⟨B,h⟩ := odd_modulus_spectrum_at_three_centers pos odd
  exact ⟨B,fun n hn => h n hn (three_centers_two_prime_powers pp qp po qo a b n)⟩

#print axioms composite_progression_spectrum
#print axioms odd_modulus_spectrum_at_three_centers
#print axioms two_prime_power_spectrum
end HadamardMod
