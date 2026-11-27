import Quantum.Hadamard.Conference
import Quantum.Hadamard.PaleySign
import Quantum.Hadamard.PaleyParity
import Quantum.Hadamard.ArithmeticReduction

/-! Projective hyperplanes of zero signed row sum, placed on the diagonal of
a conference array, give a twice-odd order in a nonsquare residue class. -/
noncomputable section
namespace HadamardMod
open Hadamard.PG

theorem conference_nonsquare_seed {p : ℕ} [Fact p.Prime] (hp : 2<p) {x : ZMod p} {u : ℕ}
    (ns : ¬ IsSquare x) (identity : x^(2*u+2)*(2-x)=1) : TwiceOddNonsquareSeed p := by
  have xn : x ≠ 0 := by rintro rfl; exact ns ⟨0,by simp⟩
  have xo : x ≠ 1 := by rintro rfl; exact ns ⟨1,by simp⟩
  have xt : 2-x ≠ 0 := by intro e; simp [e] at identity
  have two : (2:ZMod p) ≠ 0 := by
    intro e
    exact (Nat.not_dvd_of_pos_of_lt (by decide) hp) ((ZMod.natCast_eq_zero_iff 2 p).mp e)
  obtain ⟨q,hq,qx,q4⟩ := choose_base hp xn
  obtain ⟨s,hs,sv,s4⟩ := choose_base hp (div_ne_zero xt xn)
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact s.Prime := ⟨hs⟩
  let n := 2*u+1
  let v := geom q (n+2)
  have eq : x^(n+1)*(2-x)=1 := identity
  have weight : (geom q (n+1):ZMod p)=x^(n+1) := by
    have g := congrArg (fun z : ℤ => (z:ZMod p)) (geom_int q (n+1))
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_sub,Int.cast_one,Int.cast_pow,qx] at g
    apply mul_right_cancel₀ (sub_ne_zero.mpr xo)
    linear_combination g+eq
  have count : (v:ZMod p)=2*x^(n+1) := by
    dsimp [v]
    rw [show n+2=n+1+1 by omega,geom_succ_last,Nat.cast_add,Nat.cast_pow,weight,qx]
    ring
  have target : (((s+1)*v:ℕ):ZMod p)=4*x^n := by
    push_cast
    rw [sv,count,pow_succ]
    field_simp
    ring
  have odd : s≠2 := by
    intro e
    subst s
    exact (by decide : (2:ZMod 4)≠1) s4
  obtain ⟨A,sign,row,off⟩ := projective_sign p q n
  have zero (i : Fin v) : ∑ j, A i j=0 := by
    rw [row,weight]
    change (v:ZMod p)-2*x^(n+1)=0
    rw [count,sub_self]
  have cross (i k : Fin v) (ne:i≠k) : (∑ j,A i j*A k j) = -(s:ZMod p)*(v:ZMod p) := by
    rw [off i k ne,qx]
    change (v:ZMod p)-4*x^n= _
    push_cast at target
    linear_combination target
  refine ⟨(s+1)*v,?_,conference_join odd A sign zero cross,?_,?_⟩
  · have vv : 0<v := by dsimp [v]; rw [show n+2=n+1+1 by omega,geom_succ]; omega
    exact Nat.mul_pos (Nat.succ_pos _) vv
  · apply (ZMod.natCast_eq_natCast_iff _ _ 4).mp
    push_cast
    rw [s4,show (v:ZMod 4)=((n+2:ℕ):ZMod 4) from geom_at_one q 4 (n+2) q4]
    dsimp [n]
    push_cast
    ring_nf
    rfl
  · rw [target]
    apply quadraticChar_neg_one_iff_not_isSquare.mp
    have xs := quadraticChar_neg_one_iff_not_isSquare.mpr ns
    have four : quadraticChar (ZMod p) 4=1 := by
      rw [show (4:ZMod p)=2^2 by ring,map_pow,quadraticChar_sq_one two]
    rw [map_mul,map_pow,four,xs,one_mul]
    dsimp [n]
    simp [pow_succ,pow_mul]

#print axioms conference_nonsquare_seed
end HadamardMod
