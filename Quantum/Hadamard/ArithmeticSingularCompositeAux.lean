import Quantum.Hadamard.ArithmeticSingularComposite
import Quantum.Hadamard.ArithmeticSingularCompositeSelectors

/-! Additional congruences on the seed can be prescribed at every unsaturated
primary component, even when the desired period has a larger local exponent. -/
noncomputable section
namespace HadamardMod.FrobeniusConic
open Hadamard.Arithmetic

theorem twice_seed_primary_precision {m M n : ℕ} (mp : 0 < m) (big : 1<M)
    (odd : (2:ℕ).Coprime M) (mM : m∣M) (n4 : n%4=2) (ok : TwiceLocallyAdmissible m n) :
    ∃ s>0, AtOrder m s ∧ s%4=2 ∧ ∀ p∈M.primeFactors,
      if p^m.factorization p∣n then s ≡ 1 [MOD p^M.factorization p]
      else s*4 ≡ n [MOD p^M.factorization p] := by
  classical
  obtain ⟨k,_,hinv⟩ := Nat.exists_mul_mod_eq_one_of_coprime (odd.pow_left 2 : (4:ℕ).Coprime M) big
  have kinv : 4*k ≡ 1 [MOD M] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt big] using hinv
  have kc : k.Coprime M := Nat.coprime_of_mul_modEq_one 4 (by simpa [mul_comm] using kinv)
  have kp : k≠0 := by rintro rfl; simpa [Nat.ModEq,Nat.mod_eq_of_lt big] using kinv
  let g (p:ℕ) := if p^m.factorization p∣n then 1 else k*n
  obtain ⟨r,hr⟩ := primary_congruences (by omega : 0 < M) g
  have locally : TwiceLocallyAdmissible M r := by
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    apply primary_transport pp (hr p hp).symm
    by_cases saturated : p^m.factorization p∣n
    · simp [g,saturated]
    · have pm : p∣m := by
        by_contra miss
        have zero := Nat.factorization_eq_zero_of_not_dvd miss
        exact saturated (by simp [zero])
      rcases ok p (Nat.mem_primeFactors.mpr ⟨pp,pm,mp.ne'⟩) with split|contr|ev
      · exact Or.inl split
      · exact (saturated contr).elim
      · have pk : ¬p∣k := fun h => Nat.not_coprime_of_dvd_of_dvd pp.one_lt h
            (Nat.dvd_of_mem_primeFactors hp) kc
        simpa [g,saturated,Nat.factorization_mul kp (by omega : n≠0),Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd pk] using (Or.inr (Or.inr ev) :
            p%4=1 ∨ p^M.factorization p∣k*n ∨ Even (n.factorization p))
  obtain ⟨s,sp,S,s4,sr⟩ := composite_twice_seed (by omega : 0 < M) odd locally
  refine ⟨s,sp,at_weaker_modulus mM S,s4,?_⟩
  intro p hp
  have d := Finset.dvd_prod_of_mem (fun q=>q^M.factorization q) hp |>.trans
    (dvd_of_eq (Nat.prod_primeFactors_pow_factorization (by omega : M≠0)).symm)
  have sg := (sr.of_dvd d).trans (hr p hp)
  by_cases sat : p^m.factorization p∣n
  · simpa [sat,g] using sg
  · simp only [sat,ite_false]
    have e : s ≡ k*n [MOD p^M.factorization p] := by simpa [g,sat] using sg
    calc
      s*4 ≡ (k*n)*4 [MOD p^M.factorization p] := e.mul_right 4
      _ = (4*k)*n := by ring
      _ ≡ n [MOD p^M.factorization p] := by simpa using ((kinv.of_dvd d).mul_right n)

#print axioms twice_seed_primary_precision
end HadamardMod.FrobeniusConic
