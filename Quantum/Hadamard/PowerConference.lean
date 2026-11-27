import Quantum.Hadamard.PowerTwist
import Quantum.Hadamard.ConferenceSeed

/-! The conference-hyperplane construction over a residue ring, and its nonsquare seed at prime powers. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.Arithmetic.PowerResidues Hadamard.PG

theorem realize_unit_prime {m:ℕ} (mp : 0 < m) (odd:(2:ℕ).Coprime m)
    {t:ZMod m} (ut:IsUnit t) (j:ℕ) (cj:j.Coprime 4) (N:ℕ) :
    ∃ q>N, q.Prime ∧ (q:ZMod m)=t ∧ q ≡ j [MOD 4] := by
  letI : NeZero m := ⟨mp.ne'⟩
  obtain ⟨q,big,qp,q4,qm⟩ := prime_crt (m:=4) (n:=m) (by decide) mp.ne' (odd.pow_left 2)
    cj (ZMod.val_coe_unit_coprime ut.unit) N
  exact ⟨q,big,qp,((ZMod.natCast_eq_natCast_iff _ _ _).mpr qm).trans ((ZMod.natCast_zmod_val _).trans ut.unit_spec),q4⟩

theorem conference_twice_order {m u:ℕ} (mp : 0 < m) (odd:(2:ℕ).Coprime m) (x:(ZMod m)ˣ)
    (sep:IsUnit ((x:ZMod m)-1)) (idn:(x:ZMod m)^(2*u+2)*(2-x)=1) :
    ∃ h>0, AtOrder m h ∧ h ≡ 2 [MOD 4] ∧ (h:ZMod m)=4*(x:ZMod m)^(2*u+1) := by
  have ut : IsUnit (2-(x:ZMod m)) := isUnit_of_mul_isUnit_right (by rw [idn]; exact isUnit_one)
  obtain ⟨q,_,hq,qx,q4⟩ := realize_unit_prime mp odd x.isUnit 1 (by decide) 2
  obtain ⟨s,sbig,hs,sv,s4⟩ := realize_unit_prime mp odd (ut.mul x⁻¹.isUnit) 1 (by decide) 2
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact s.Prime := ⟨hs⟩
  let n := 2*u+1
  let v := geom q (n+2)
  have eq : (x:ZMod m)^(n+1)*(2-x)=1 := idn
  have weight : (geom q (n+1):ZMod m)=(x:ZMod m)^(n+1) := by
    have g := congrArg (fun z:ℤ => (z:ZMod m)) (geom_int q (n+1))
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_sub,Int.cast_one,Int.cast_pow,qx] at g
    apply sep.mul_left_inj.mp
    linear_combination g+eq
  have count : (v:ZMod m)=2*(x:ZMod m)^(n+1) := by
    dsimp [v]
    rw [show n+2=n+1+1 by omega,geom_succ_last,Nat.cast_add,Nat.cast_pow,weight,qx]
    ring
  have sx : (s:ZMod m)*x=2-x := by rw [sv,mul_assoc]; simp
  have target : (((s+1)*v:ℕ):ZMod m)=4*(x:ZMod m)^n := by
    push_cast
    rw [count,pow_succ]
    linear_combination 2*(x:ZMod m)^n*sx
  obtain ⟨A,sign,row,off⟩ := projective_sign m q n
  have zero (i : Fin v) : ∑ j, A i j=0 := by rw [row,weight]; change (v:ZMod m)-2*(x:ZMod m)^(n+1)=0; rw [count,sub_self]
  have cross (i k : Fin v) (ne:i≠k) : (∑ j,A i j*A k j) = -(s:ZMod m)*(v:ZMod m) := by
    rw [off i k ne,qx]
    change (v:ZMod m)-4*(x:ZMod m)^n= _
    push_cast at target
    linear_combination target
  refine ⟨(s+1)*v,?_,conference_join (by omega) A sign zero cross,?_,target⟩
  · have vv : 0<v := by dsimp [v]; rw [show n+2=n+1+1 by omega,geom_succ]; omega
    exact Nat.mul_pos (Nat.succ_pos _) vv
  · apply (ZMod.natCast_eq_natCast_iff _ _ 4).mp
    have sq4 : (s:ZMod 4)=1 := (ZMod.natCast_eq_natCast_iff s 1 4).mpr s4
    have qq4 : (q:ZMod 4)=1 := (ZMod.natCast_eq_natCast_iff q 1 4).mpr q4
    push_cast
    rw [sq4,show (v:ZMod 4)=((n+2:ℕ):ZMod 4) from geom_at_one q 4 (n+2) qq4]
    dsimp [n]
    push_cast
    ring_nf
    rfl

theorem power_nonsquare_seed {p:ℕ} [Fact p.Prime] (a:ℕ) (h8:p%8=1) :
    ∃ h>0, AtOrder (p^(a+1)) h ∧ h ≡ 2 [MOD 4] ∧ ¬IsSquare (h:ZMod p) := by
  have pp : p.Prime := Fact.out
  have po : 2<p := by have := pp.two_le; omega
  obtain ⟨x,u,nx,sep,eq⟩ := twist a h8
  obtain ⟨h,pos,H,h4,hm⟩ := conference_twice_order (pow_pos pp.pos _) ((two_coprime_prime pp po).pow_right _) x sep eq
  refine ⟨h,pos,H,h4,?_⟩
  have t := congrArg (red p a) hm
  simp only [map_natCast,map_mul,map_ofNat,map_pow] at t
  have tw : (2:ZMod p)≠0 := fun e => (Nat.not_dvd_of_pos_of_lt (by decide) po) ((ZMod.natCast_eq_zero_iff 2 p).mp e)
  have four : quadraticChar (ZMod p) 4=1 := by
    rw [show (4:ZMod p)=2^2 by ring,map_pow,quadraticChar_sq_one tw]
  apply quadraticChar_neg_one_iff_not_isSquare.mp
  rw [t,map_mul,map_pow,four,quadraticChar_neg_one_iff_not_isSquare.mpr nx,one_mul]
  simp [pow_succ,pow_mul]

#print axioms power_nonsquare_seed
end HadamardMod
