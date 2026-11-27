import Quantum.Hadamard.ArithmeticSingularCompositeCRT
import Quantum.Hadamard.TorusFrobeniusScaled

/-! Exact realization of twice-odd residue classes over every odd modulus. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

theorem composite_twice_seed {m r : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (eligible : TwiceLocallyAdmissible m r) :
    ∃ h > 0, AtOrder m h ∧ h ≡ 2 [MOD 4] ∧ h ≡ r [MOD m] := by
  classical
  by_cases one : m=1
  · subst m
    exact ⟨2,by decide,ones (Subsingleton.elim _ _),Nat.ModEq.refl _, by simp [Nat.ModEq,Nat.mod_one]⟩
  have mh : 1 < m := by omega
  let : NeZero m := ⟨mp.ne'⟩
  obtain ⟨v,x,y,vo,_,V,xu,eq⟩ := composite_frobenius_parameters mp om eligible
  obtain ⟨t,_,tp,tx,t4⟩ := realize_unit_prime mp om xu 3 (by decide) 2
  let : Fact t.Prime := ⟨tp⟩
  obtain ⟨s,sp,S,s4,sv⟩ := TorusFrobenius.scaled_seed mp om vo (Periodic.matrix V) t t4
  let z := (y^2).val
  have ze : (z:ZMod m)=y^2 := ZMod.natCast_zmod_val _
  have zs : IsSquare (z:ZMod m) := ⟨y,by rw [ze,pow_two]⟩
  obtain ⟨k,kp,K,k4,kz⟩ := square_seed_each_mod_four mh om zs (1:Fin 4)
  refine ⟨s*k,Nat.mul_pos sp kp,at_mul S K,by simpa using s4.mul k4,?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
  rw [Nat.cast_mul,(ZMod.natCast_eq_natCast_iff _ _ _).mpr sv,
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr kz,ze]
  push_cast
  rw [tx,eq]

/-- An iff about actual sign matrices, with no lower bound on the modulus
or upper bound on its number of distinct prime divisors. -/
theorem twice_class_realizable_iff {m r : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    (∃ h > 0, IntegralSolution m h ∧ h%4=2 ∧ h ≡ r [MOD m]) ↔
      TwiceLocallyAdmissible m r := by
  constructor
  · rintro ⟨h,_,H,h4,hr⟩
    exact twice_admissible_of_congr mp hr (twice_necessary_at_odd_modulus mp om h4 H)
  · intro eligible
    obtain ⟨h,hp,H,h4,hr⟩ := composite_twice_seed mp om eligible
    exact ⟨h,hp,integer_gram H,h4,hr⟩

/-- If the preceding residue is a unit, every sufficiently large
twice-odd order in the class attains the full local criterion. -/
theorem twice_class_large_of_unit_predecessor {m r : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (pred : IsUnit ((r:ZMod m)-1)) :
    ∃ B : ℕ, ∀ n ≥ B, n%4=2 → n ≡ r [MOD m] →
      (IntegralSolution m n ↔ TwiceLocallyAdmissible m n) := by
  by_cases one : m=1
  · subst m
    exact ⟨0,fun n _ n4 _ => ⟨twice_necessary_at_odd_modulus mp om n4,
      fun _ => integer_gram (ones (Subsingleton.elim _ _))⟩⟩
  have mh : 1 < m := by omega
  by_cases er : TwiceLocallyAdmissible m r
  · obtain ⟨h,hp,H,h4,hr⟩ := composite_twice_seed mp om er
    let a := r+m-1
    have ra : r ≡ a+1 [MOD m] := by
      rw [show a+1=r+m by dsimp [a]; omega]; simp [Nat.ModEq]
    have az : (a:ZMod m)=(r:ZMod m)-1 := by
      have eq := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ra
      push_cast at eq
      linear_combination -eq
    have ca := (ZMod.isUnit_iff_coprime a m).mp (az ▸ pred)
    obtain ⟨B,all⟩ := composite_seed_class mh om ca (hr.trans ra) (primeConstruction m) hp H
    exact ⟨B,fun n hn n4 nr => ⟨twice_necessary_at_odd_modulus mp om n4, fun _ =>
      integer_gram (all n hn ((show n ≡ 2 [MOD 4] from n4).trans h4.symm) (nr.trans hr.symm))⟩⟩
  · exact ⟨0,fun n _ n4 nr => ⟨twice_necessary_at_odd_modulus mp om n4,
      fun en => (er (twice_admissible_of_congr mp nr en)).elim⟩⟩

theorem composite_twice_large_of_unit_predecessor {m : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    ∃ B : ℕ, ∀ n ≥ B, n%4=2 → IsUnit ((n:ZMod m)-1) →
      (IntegralSolution m n ↔ TwiceLocallyAdmissible m n) := by
  classical
  have cls (i:Fin m) : ∃ B : ℕ, ∀ n ≥ B, n%4=2 → n ≡ i.val [MOD m] →
      IsUnit ((n:ZMod m)-1) → (IntegralSolution m n ↔ TwiceLocallyAdmissible m n) := by
    by_cases unit : IsUnit ((i.val:ZMod m)-1)
    · obtain ⟨B,all⟩ := twice_class_large_of_unit_predecessor mp om unit
      exact ⟨B,fun n hn n4 ni _ => all n hn n4 ni⟩
    · exact ⟨0,fun _ _ _ ni un => (unit ((ZMod.natCast_eq_natCast_iff _ _ _).mpr ni ▸ un)).elim⟩
  choose bounds spec using cls
  refine ⟨Finset.univ.sup bounds,?_⟩
  intro n hn n4 un
  let i : Fin m := ⟨n%m,Nat.mod_lt _ mp⟩
  exact spec i n ((Finset.le_sup (f:=bounds) (Finset.mem_univ i)).trans hn)
    n4 (Nat.mod_modEq n m).symm un

#print axioms composite_twice_seed
#print axioms twice_class_realizable_iff
#print axioms composite_twice_large_of_unit_predecessor
end HadamardMod
