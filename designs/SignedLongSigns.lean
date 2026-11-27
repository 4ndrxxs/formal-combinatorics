import SignedLongMultiplier
import SignedMultiplierOrbits

namespace Signed39.Contraction

open Finset

variable {p : ℕ} [Fact p.Prime]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem row_multiplier_fixed {f:ZMod p×H→ℤ} {k l:ℤ} (hf:IsSDS k l f) (hn:0<k-l)
    (B:H≃+H) (surj:∀t:H,∃b,B b-b=t)
    (matchEq:∃t:ZMod p×H,∀x,f (((AddEquiv.refl (ZMod p)).prodCongr B).symm x)=f (x-t)) :
    ∃base:H,∀i x,f (i,B x+base)=f (i,x+base) := by
  let E:=(AddEquiv.refl (ZMod p)).prodCongr B
  obtain ⟨t,h⟩:=matchEq
  have eq (i:ZMod p) (x:H) : f (i,x)=f (i-t.1,B x-t.2) := by
    have v:=h (E (i,x))
    change f (E.symm (E (i,x)))=_ at v
    rwa [E.symm_apply_apply] at v
  let A:=rowMass f
  have period (i:ZMod p) : A i=A (i-t.1) := by
    calc
      _=∑x:H,f (i-t.1,B x-t.2) := sum_congr rfl (fun x _=>eq i x)
      _=∑x:H,f (i-t.1,x) := Fintype.sum_equiv (B.toEquiv.trans (Equiv.addRight (-t.2))) _ _
        (fun x=>by simp [sub_eq_add_neg])
  have t0 : t.1=0 := by
    by_contra nz
    have atP (i) : A (i+t.1)=A i := by simpa using period (i+t.1)
    have same : corr A t.1=corr A 0 := by simp [corr,atP]
    change corr (rowMass f) t.1=corr (rowMass f) 0 at same
    rw [rowmass_corr hf,rowmass_corr hf] at same
    simp only [ite_eq_right nz,zero_add,ite_true] at same
    omega
  obtain ⟨b,hb⟩:=surj t.2
  refine ⟨b,fun i x=>?_⟩
  have e:=eq i (x+b)
  rw [t0,sub_zero,map_add,add_sub_assoc,←hb,sub_sub_cancel] at e
  exact e.symm

def signBit (z sg:ℤ) : ℤ := if z=sg then 1 else 0

private theorem sign_total {G:Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {f:G→ℤ} {k l:ℤ} (hf:IsSDS k l f) (sg:ℤ) (sign:sg=1∨sg= -1) :
    2*(∑x,signBit (f x) sg)=k+sg*mass f := by
  have val (x:G) : 2*signBit (f x) sg=f x*f x+sg*f x := by
    rcases hf.ternary x with z|z|z <;> rcases sign with rfl|rfl <;> simp [z,signBit]
  have ek : (∑x:G,f x*f x)=k := by simpa [corr] using hf.flat 0
  calc
    _=∑x,2*signBit (f x) sg := by rw [mul_sum]
    _=∑x,(f x*f x+sg*f x) := sum_congr rfl (fun x _=>val x)
    _=_ := by rw [sum_add_distrib,←mul_sum,ek]; rfl

theorem fixed_sign_counts {f:ZMod p×H→ℤ} {k l:ℤ} (hf:IsSDS k l f)
    (B:H≃+H) (base:H) (fix:∀i x,f (i,B x+base)=f (i,x+base))
    (d:ℕ) (W:H→ℤ) (levels:∀x,(d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W (B x)-W x) :
    ∃a b:Fin (p+1),a.val+b.val≤p ∧
      (d:ℤ)∣(k+mass f)/2-a.val ∧ (d:ℤ)∣(k-mass f)/2-b.val := by
  let mark (sg:ℤ) (i:ZMod p) (x:H) := signBit (f (i,x+base)) sg
  let fixedCount (sg:ℤ) := ∑i:ZMod p,mark sg i 0
  have nonneg (sg:ℤ) : 0≤fixedCount sg := sum_nonneg (fun i _=>by dsimp [mark,signBit]; split <;> decide)
  have total : fixedCount 1+fixedCount (-1) ≤ (p:ℤ) := by
    have one (i:ZMod p) : mark 1 i 0+mark (-1) i 0≤1 := by
      dsimp [mark,signBit]
      rcases hf.ternary (i,base) with h|h|h <;> simp [h]
    have a:=sum_le_sum (s:=univ) (fun i _=>one i)
    simpa only [sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one,fixedCount] using a
  have congruent (sg:ℤ) (ss:sg=1∨sg= -1) : (d:ℤ)∣(k+sg*mass f)/2-fixedCount sg := by
    have each (i:ZMod p) : (d:ℤ)∣mass (mark sg i)-mark sg i 0 := orbit_mass_dvd B.toEquiv (mark sg i) W _ 0
      (fun x=>by change signBit (f (i,B x+base)) sg=signBit (f (i,x+base)) sg; rw [fix]) levels
    have all:=dvd_sum (s:=univ) (fun i _=>each i)
    rw [sum_sub_distrib] at all
    have translated (i:ZMod p) : mass (mark sg i)=∑x:H,signBit (f (i,x)) sg :=
      sum_translate (fun x:H=>signBit (f (i,x)) sg) base
    rw [show (∑i:ZMod p,mass (mark sg i))=(∑x:ZMod p×H,signBit (f x) sg) by
      simp only [translated,Fintype.sum_prod_type]] at all
    have st:=sign_total hf sg ss
    rwa [←st,Int.mul_ediv_cancel_left _ (by decide : (2:ℤ)≠0)]
  let a:=(fixedCount 1).toNat
  let b:=(fixedCount (-1)).toNat
  have av : (a:ℤ)=fixedCount 1 := Int.toNat_of_nonneg (nonneg _)
  have bv : (b:ℤ)=fixedCount (-1) := Int.toNat_of_nonneg (nonneg _)
  have pos:=nonneg 1
  have neg:=nonneg (-1)
  refine ⟨⟨a,by omega⟩,⟨b,by omega⟩,show a+b≤p by omega,?_,?_⟩
  · simpa [av] using congruent 1 (Or.inl rfl)
  · simpa [bv,sub_eq_add_neg] using congruent (-1) (Or.inr rfl)

#print axioms row_multiplier_fixed
#print axioms fixed_sign_counts

end Signed39.Contraction

