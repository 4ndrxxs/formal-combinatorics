import Quantum.Hadamard.TripleExtender
import Quantum.Hadamard.ArithmeticTwoPowers

/-! An arbitrary-period seed construction becomes an eventual statement
in any class where one of r, r-1, r-2 is a unit. This covers all classes
when the odd modulus is supported on at most two primes. -/
noncomputable section
namespace HadamardMod
open Finset Hadamard.PG Hadamard.Arithmetic

def ThreeUnitCenters (m n : ℕ) : Prop :=
  IsUnit (n : ZMod m) ∨ IsUnit ((n : ZMod m)-1) ∨ IsUnit ((n : ZMod m)-2)

private theorem growth_chart {m r : ℕ} (mp : 1 < m) (om : (2:ℕ).Coprime m)
    (centers : ThreeUnitCenters m r) :
    ∃ (I : Type) (_ : Fintype I), 1 < Fintype.card I ∧ Nonempty (Extender m I (r:ZMod m)) := by
  rcases centers with unit|unit|unit
  · have four : IsUnit (4:ZMod m) := by simpa using (ZMod.isUnit_iff_coprime 4 m).mpr (om.pow_left 2)
    obtain ⟨q,_,qp,qz,_⟩ := realize_unit_prime (by omega) om (four.mul unit.unit⁻¹.isUnit) 3 (by decide) 2
    have qc : q.Coprime m := (ZMod.isUnit_iff_coprime q m).mp (qz ▸ four.mul unit.unit⁻¹.isUnit)
    obtain ⟨d,zero,period⟩ := geom_period (by omega) qc
    have rel : (q:ZMod m)*r=4 := calc
      (q:ZMod m)*r = (4*(↑unit.unit⁻¹:ZMod m))*↑unit.unit := congrArg₂ (·*·) qz unit.unit_spec.symm
      _ = 4 := by rw [mul_assoc]; simp
    have eq : 4*(q:ZMod m)^(d+1)=(r:ZMod m) := by
      rw [show d+2=d+1+1 by omega,pow_succ] at period
      linear_combination (r:ZMod m)*period-(q:ZMod m)^(d+1)*rel
    letI : Fact q.Prime := ⟨qp⟩
    obtain ⟨D⟩ := projective_extender_at (d:=d+1) zero
    refine ⟨_,inferInstance,?_,⟨eq ▸ D⟩⟩
    rw [Fintype.card_fin,geom_succ]
    have growth : 0 < geom q ((d+1)+1) := by rw [geom_succ]; omega
    exact Nat.lt_add_of_pos_right (Nat.mul_pos growth qp.pos)
  · obtain ⟨q,qbig,qp,qz,q4⟩ := realize_unit_prime (by omega) om unit 3 (by decide) 2
    obtain ⟨s,sbig,sp,sz,s4⟩ := realize_unit_prime (by omega) om unit.unit⁻¹.isUnit 3 (by decide) 2
    letI : Fact q.Prime := ⟨qp⟩
    letI : Fact s.Prime := ⟨sp⟩
    have product : (Fintype.card (ZMod s) * Fintype.card (ZMod q) : ZMod m)=1 := by
      simp only [ZMod.card]
      calc
        (s:ZMod m)*q = (↑unit.unit⁻¹:ZMod m)*↑unit.unit := congrArg₂ (·*·) sz (qz.trans unit.unit_spec.symm)
        _ = 1 := by simp
    let D := lexExtension (paleySkew m s s4) (paleySkew m q q4).inner (by simpa using product)
    have eq : 1+(Fintype.card (ZMod q):ZMod m)=(r:ZMod m) := by simp [qz]
    refine ⟨ZMod s × ZMod q,inferInstance,?_,⟨eq ▸ D⟩⟩
    simp only [Fintype.card_prod,ZMod.card]
    nlinarith
  · obtain ⟨v,big,D⟩ := brouwer_odd_class (by omega) om unit
    exact ⟨Fin v,inferInstance,by simpa using big,D⟩

/-- Admissibility need not be defined periodically. It suffices to have an
admissible seed in each arithmetic progression containing admissible orders. -/
theorem cofinite_at_three_centers {m : ℕ} (mp : 1 < m) (om : (2:ℕ).Coprime m)
    (P : ℕ → Prop)
    (dense : ∀ a : ℕ, 0<a → 4*m∣a → ∀ n : ℕ, P n →
      ∃ h>0, AtOrder m h ∧ h ≡ n [MOD a]) :
    ∃ B : ℕ, ∀ n≥B, P n → ThreeUnitCenters m n → AtOrder m n := by
  classical
  have cls (r : Fin m) : ∃ B : ℕ, ∀ n≥B, n ≡ r.val [MOD m] →
      P n → ThreeUnitCenters m n → AtOrder m n := by
    by_cases c : ThreeUnitCenters m r.val
    · obtain ⟨I,ft,size,⟨D⟩⟩ := growth_chart mp om c
      letI : Fintype I := ft
      let step := Fintype.card I-1
      have st : 0<step := by dsimp [step]; omega
      let a := 4*m*step
      have ap : 0<a := by dsimp [a]; positivity
      have ma : m∣a := dvd_trans (dvd_mul_left m 4) (dvd_mul_right (4*m) step)
      have sa : step∣a := dvd_mul_left step (4*m)
      have aux (i : Fin a) : ∃ K : ℕ, ∀ n≥K, n ≡ i.val [MOD a] →
          n ≡ r.val [MOD m] → P n → AtOrder m n := by
        by_cases existsN : ∃ z : ℕ, z ≡ i.val [MOD a] ∧ P z
        · obtain ⟨z,zi,pz⟩ := existsN
          obtain ⟨h,hp,H,hz⟩ := dense a ap (dvd_mul_right _ _) z pz
          refine ⟨h,fun n hn ni nr _ => ?_⟩
          have hnA := (hz.trans zi).trans ni.symm
          have hr := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hnA.of_dvd ma).trans nr)
          obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hn).mp (hnA.of_dvd sa)
          have raw := D.iterate hp H hr k
          change AtOrder m (h+k*step) at raw
          rwa [show h+k*step=n by rw [Nat.mul_comm]; omega] at raw
        · exact ⟨0,fun n _ ni _ pn => False.elim (existsN ⟨n,ni,pn⟩)⟩
      choose K spec using aux
      refine ⟨Finset.univ.sup K,fun n hn nr pn _ => ?_⟩
      let i : Fin a := ⟨n%a,Nat.mod_lt _ ap⟩
      exact spec i n ((Finset.le_sup (f:=K) (Finset.mem_univ i)).trans hn)
        (Nat.mod_modEq _ _).symm nr pn
    · refine ⟨0,fun n _ nr _ cn => False.elim (c ?_)⟩
      simpa only [ThreeUnitCenters,(ZMod.natCast_eq_natCast_iff _ _ _).mpr nr] using cn
  choose B spec using cls
  refine ⟨Finset.univ.sup B,fun n hn pn g => ?_⟩
  let i : Fin m := ⟨n%m,Nat.mod_lt _ (by omega)⟩
  exact spec i n ((Finset.le_sup (f:=B) (Finset.mem_univ i)).trans hn) (Nat.mod_modEq _ _).symm pn g

theorem three_centers_two_prime_powers {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : 2<p) (qo : 2<q) (a b n : ℕ) : ThreeUnitCenters (p^a*q^b) n := by
  let m := p^a*q^b
  have mp : 0 < m := Nat.mul_pos (pow_pos pp.pos _) (pow_pos qp.pos _)
  letI : NeZero m := ⟨mp.ne'⟩
  have om : (2:ℕ).Coprime m := ((two_coprime_prime pp po).pow_right a).mul_right
    ((two_coprime_prime qp qo).pow_right b)
  let u := ZMod.unitOfCoprime 4 (om.pow_left 2)
  let x := (↑u⁻¹ : ZMod m)*(n:ZMod m)
  let w := x.val+m
  have wp : 0<w := by dsimp [w]; omega
  have wx : (w:ZMod m)=x := by simp [w]
  have hu : (u:ZMod m)=4 := ZMod.coe_unitOfCoprime _ _
  have fourw : 4*(w:ZMod m)=(n:ZMod m) := by rw [wx,←hu]; simp [x]
  change ThreeUnitCenters m n
  rcases units_at_two_powers pp qp a b wp with unit|unit|unit
  · apply Or.inl
    rw [←fourw]
    exact (hu ▸ u.isUnit).mul ((ZMod.isUnit_iff_coprime w m).mpr unit)
  · apply Or.inr ∘ Or.inl
    have eq : ((4*w-1:ℕ):ZMod m)=(n:ZMod m)-1 := by
      rw [Nat.cast_sub (by omega),Nat.cast_mul]; simpa using fourw
    exact eq ▸ (ZMod.isUnit_iff_coprime _ _).mpr unit
  · apply Or.inr ∘ Or.inr
    have eq : (2:ZMod m)*(↑(2*w-1:ℕ):ZMod m)=(n:ZMod m)-2 := by
      rw [Nat.cast_sub (by omega),Nat.cast_mul,←fourw]; push_cast; ring
    exact eq ▸ ((ZMod.isUnit_iff_coprime 2 m).mpr om).mul ((ZMod.isUnit_iff_coprime _ _).mpr unit)

#print axioms cofinite_at_three_centers
#print axioms three_centers_two_prime_powers
end HadamardMod
