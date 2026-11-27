import Quantum.Hadamard.ArithmeticDense
import Quantum.Hadamard.PaleySign

/-! Dense seeds make a single positive extender sufficient for all large
orders in its class. The projective construction works at a composite
modulus when a geometric sum vanishes. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG

theorem large_of_one_extender {b c : ℕ} (bp : 0 < b) (odd : (2 : ℕ).Coprime b)
    {I : Type*} [Fintype I] (D : Extender (4*b) I (c:ZMod (4*b))) (large : 1 < Fintype.card I) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ c [MOD 4*b] → AtOrder (4*b) n := by
  classical
  let a := Fintype.card I-1
  have ap : 0 < a := by dsimp [a]; omega
  have am : 4*b ∣ a := by
    apply (ZMod.natCast_eq_zero_iff a (4*b)).mp
    dsimp [a]
    rw [Nat.cast_sub (by omega),Nat.cast_one,D.dim,sub_self]
  have a4 : 4 ∣ a := (dvd_mul_right 4 b).trans am
  obtain ⟨T,hT⟩ := a4
  have tp : 0 < T := by omega
  have cls (i : Fin T) : ∃ h > 0, AtOrder (4*b) h ∧ h ≡ 4*i.val [MOD a] := by
    rw [hT]
    exact dense_four_seeds bp odd tp i.val 0
  choose h pos mat res using cls
  refine ⟨Finset.univ.sup h,?_⟩
  rintro n big ⟨k,hk⟩ nc
  let i : Fin T := ⟨k%T,Nat.mod_lt _ tp⟩
  have fouri : 4*i.val ≡ n [MOD a] := by
    rw [hT,hk]
    exact (Nat.mod_modEq k T).mul_left' 4
  have incl := (res i).trans fouri
  have le := (Finset.le_sup (f := h) (Finset.mem_univ i)).trans big
  obtain ⟨t,ht⟩ := (Nat.modEq_iff_dvd' le).mp incl
  have cn : (h i : ZMod (4*b))=(c:ZMod (4*b)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((incl.of_dvd am).trans nc)
  have reached := D.iterate (pos i) (mat i) cn t
  change AtOrder (4*b) (h i+t*a) at reached
  rwa [show h i+t*a=n by rw [Nat.mul_comm]; omega] at reached

theorem projective_extender_at {m q d : ℕ} [Fact q.Prime]
    (zero : (geom q (d+1):ZMod m)=0) :
    Nonempty (Extender m (Fin (geom q (d+2))) (4*(q:ZMod m)^d)) := by
  obtain ⟨A,sg,row,off⟩ := projective_sign m q d
  have dim : (geom q (d+2):ZMod m)=1 := by
    rw [show d+2=d+1+1 by omega,geom_succ]
    push_cast
    simp [zero]
  refine ⟨{entry := A,sign := sg,row := ?_,off := ?_,dim := ?_,pos := ?_}⟩
  · intro i
    rw [row,dim,zero]
    ring
  · intro i j h
    rw [off i j h,dim]
  · simpa using dim
  · simp only [Fintype.card_fin]
    rw [show d+2=d+1+1 by omega,geom_succ]
    omega

end HadamardMod
