import Quantum.Hadamard.ArithmeticOddPeriods
import Quantum.Hadamard.CompositeUnits

/-! The complete asymptotic classification at unit orders, for every
odd modulus having only prime factors congruent to three modulo four. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG Finset

private theorem weaken_integral {m M n : ℕ} (dv : m ∣ M) (H : AtOrder M n) : AtOrder m n := by
  obtain ⟨A,sign,dot⟩ := integer_gram H
  exact atOrder_of_integral ⟨A,sign,fun i k => (show (m:ℤ)∣(M:ℤ) by exact_mod_cast dv).trans (dot i k)⟩

theorem four_orders_at_unit {m r : ℕ} (mp : 1 < m) (odd : (2:ℕ).Coprime m) (cr : r.Coprime m) :
    ∃ B, ∀ n ≥ B, 4∣n → n ≡ r [MOD m] → AtOrder m n := by
  have c4 : (4:ℕ).Coprime m := odd.pow_left 2
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime c4 mp
  have inv : 4*i ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mp] using hi
  have ci : i.Coprime m := Nat.coprime_of_mul_modEq_one 4 (by rw [mul_comm]; exact inv)
  obtain ⟨B,hB⟩ := unit_four_large (by omega : 0 < m) odd (cr.mul_left ci)
  refine ⟨B,?_⟩
  intro n hn four nr
  apply weaken_integral (dvd_mul_left m 4) (hB n hn four ?_)
  apply (Nat.modEq_and_modEq_iff_modEq_mul c4).mp
  refine ⟨(Nat.modEq_zero_iff_dvd.mpr four).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 4 _)).symm,?_⟩
  have rr : 4*(r*i) ≡ r [MOD m] := by
    rw [show 4*(r*i)=(4*i)*r by ring]
    simpa using inv.mul_right r
  exact nr.trans rr.symm

private theorem sum_repeat {m q e : ℕ} (per : (q:ZMod m)^e=1) (z:ℕ) :
    (geom q (e*z):ZMod m)=(z:ZMod m)*(geom q e:ZMod m) := by
  have plus (a b:ℕ) : geom q (a+b)=geom q a+q^a*geom q b := by simp [geom,sum_range_add,pow_add,mul_sum]
  induction z with
  | zero => simp [geom]
  | succ z ih =>
    rw [Nat.mul_succ,plus,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,pow_mul,per,one_pow,one_mul,ih]
    push_cast
    ring

theorem even_unit_class {m r : ℕ} (mp : 1 < m) (odd : (2:ℕ).Coprime m) (cr : r.Coprime m)
    (periods : ∀ q : ℕ, q.Coprime m → ∃ t : ℕ, Odd t ∧ q^(2*t) ≡ 1 [MOD m]) :
    ∃ B, ∀ n ≥ B, Even n → n ≡ r [MOD m] → AtOrder m n := by
  have c4 : (4:ℕ).Coprime m := odd.pow_left 2
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime cr mp
  have inv : r*i ≡ 1 [MOD m] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mp] using hi
  have ci : i.Coprime m := Nat.coprime_of_mul_modEq_one r (by rw [mul_comm]; exact inv)
  obtain ⟨q,qp,prime,q4,qr⟩ := prime_crt (m:=4) (n:=m) (a:=1) (b:=4*i)
    (by decide) (by omega) c4 (by decide) (c4.mul_left ci) 2
  have : Fact q.Prime := ⟨prime⟩
  have rel : (r:ZMod m)*(q:ZMod m)=4 := by
    have eq : r*q ≡ 4 [MOD m] := calc
      _ ≡ r*(4*i) [MOD m] := qr.mul_left r
      _ = 4*(r*i) := by ring
      _ ≡ 4 [MOD m] := by simpa using inv.mul_left 4
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eq
  obtain ⟨t,todd,tp⟩ := periods q (coprime_of_modEq qr (c4.mul_left ci))
  have per : (q:ZMod m)^(2*t)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr tp
  let d := 2*t*m
  have om : Odd m := Nat.coprime_two_left.mp odd
  have td : d%4=2 := by
    obtain ⟨a,ha⟩:=todd
    obtain ⟨b,hb⟩:=om
    dsimp [d]
    rw [ha,hb,show 2*(2*a+1)*(2*b+1)=4*(2*a*b+a+b)+2 by ring]
    simp
  have d2 : d-2+2=d := by omega
  have zero : (geom q d:ZMod m)=0 := by dsimp [d]; rw [sum_repeat per]; simp
  have power : (q:ZMod m)^d=1 := by dsimp [d]; rw [pow_mul,per,one_pow]
  let k := d-2
  have kd : k+2=d := d2
  have kz : (geom q ((k+1)+1):ZMod m)=0 := by simpa only [show (k+1)+1=d by omega] using zero
  have er : 4*(q:ZMod m)^(k+1)=(r:ZMod m) := by
    rw [←kd,show k+2=k+1+1 by omega,pow_succ] at power
    linear_combination (r:ZMod m)*power-(q:ZMod m)^(k+1)*rel
  obtain ⟨D⟩ := projective_extender_at (d:=k+1) kz
  rw [er] at D
  let v := geom q ((k+1)+2)
  have sm : m ∣ v-1 := by
    have dim : (v:ZMod m)=1 := by simpa [v] using D.dim
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have vp : 0 < v := by simpa [v] using D.pos
    rw [Nat.cast_sub (by omega),dim,Nat.cast_one,sub_self]
  have s4 : (v-1)%4=2 := by
    have qz : (q:ZMod 4)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr q4
    have vg := geom_at_one q 4 ((k+1)+2) qz
    have mr := (ZMod.natCast_eq_natCast_iff _ _ _).mp vg
    change v%4=((k+1)+2)%4 at mr
    omega
  obtain ⟨B,hB⟩ := four_orders_at_unit mp odd cr
  refine ⟨B+(v-1)+1,?_⟩
  intro n hn en nr
  by_cases four : 4 ∣ n
  · exact hB n (by omega) four nr
  have ev := Nat.even_iff.mp en
  let j := n-(v-1)
  have jp : 0 < j := by dsimp [j]; omega
  have jn : j+(v-1)=n := by dsimp [j]; omega
  have j4 : 4 ∣ j := by dsimp [j]; omega
  have jm : j ≡ r [MOD m] := by
    have e := (Nat.modEq_zero_iff_dvd.mpr sm).add_left j
    rw [jn,add_zero] at e
    exact e.symm.trans nr
  have J := hB j (by dsimp [j]; omega) j4 jm
  have final := D.grow jp J ((ZMod.natCast_eq_natCast_iff _ _ _).mpr jm)
  simpa only [Fintype.card_fin,← jn] using final

theorem three_mod_four_units_classification {m : ℕ} (mp : 0 < m) (odd : (2:ℕ).Coprime m)
    (primes : ∀ p, p.Prime → p ∣ m → p%4=3) :
    ∃ B : ℕ, ∀ n : ℕ, n ≥ B → n.Coprime m →
      (IntegralSolution m n ↔ Even n ∨ IsSquare (n:ZMod m)) := by
  classical
  by_cases m1 : m=1
  · subst m
    exact ⟨0,fun n _ _ => ⟨fun _ => Or.inr ⟨0,Subsingleton.elim _ _⟩,
      fun _ => integer_gram (ones (Subsingleton.elim _ _))⟩⟩
  have cls (i:Fin m) : ∃ B, ∀ n ≥ B, Even n → n ≡ i.val [MOD m] → n.Coprime m → AtOrder m n := by
    by_cases ci : i.val.Coprime m
    · obtain ⟨B,hB⟩ := even_unit_class (by omega) odd ci (fun _ c => odd_unit_exponent mp c primes)
      exact ⟨B,fun n hn en r _ => hB n hn en r⟩
    · exact ⟨0,fun _ _ _ r c => (ci (coprime_of_modEq r.symm c)).elim⟩
  choose B hB using cls
  obtain ⟨U,hu⟩ := all_large_unit_squares mp odd
  refine ⟨max U (univ.sup B),?_⟩
  intro n hn cn
  refine ⟨fun H => ?_,?_⟩
  · by_cases e : Even n
    · exact Or.inl e
    · exact Or.inr (odd_unit_necessary cn (Nat.not_even_iff_odd.mp e) (atOrder_of_integral H))
  · rintro (en|sq)
    · let i : Fin m := ⟨n%m,Nat.mod_lt _ mp⟩
      exact integer_gram (hB i n ((le_sup (mem_univ i)).trans (le_trans (le_max_right _ _) hn))
        en (Nat.mod_modEq n m).symm cn)
    · exact integer_gram (hu n ((le_max_left _ _).trans hn) cn sq)

#print axioms three_mod_four_units_classification
end HadamardMod
