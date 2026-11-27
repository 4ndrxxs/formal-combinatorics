import PermanentArrowKernel
import PermanentArrowEntries

/-! The exact rank predicted in Bedi--Suagee, Remark 2.2.18, for all
orders at least two over every field of characteristic different from two. -/
noncomputable section
open Matrix Module Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Field K]

def traceMap (K : Type*) [Field K] (I : Type*) [Fintype I] : (I→K)→ₗ[K] K :=
  ∑ i : I, LinearMap.proj i

omit [DecidableEq I] in
@[simp] theorem trace_apply (d : I → K) : traceMap K I d=∑ i,d i := by simp [traceMap]

def radicalEquiv [Nonempty I] (two_ne : (2:K)≠0) :
    (model K I).mulVecLin.ker ≃ₗ[K] (traceMap K I).ker where
  toFun w := ⟨fun i ↦ w.1 (old (i,i)),by
    change traceMap K I _=0
    rw [trace_apply]
    exact ((ker_iff two_ne w.1).mp w.2).1⟩
  invFun d := ⟨diagonalLift d.1,by
    change model K I *ᵥ diagonalLift d.1=0
    rw [image_lift,←trace_apply,show traceMap K I d.1=0 from d.2,zero_smul]⟩
  left_inv w := Subtype.ext ((ker_iff two_ne w.1).mp w.2).2.symm
  right_inv d := by
    apply Subtype.ext
    funext i
    simp [diagonalLift,old]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem model_nullity [Nonempty I] (two_ne : (2:K)≠0) :
    Module.finrank K (model K I).mulVecLin.ker+1=Fintype.card I := by
  rw [(radicalEquiv (I:=I) two_ne).finrank_eq]
  have right : Function.Surjective (traceMap K I) := by
    obtain ⟨i⟩ := ‹Nonempty I›
    intro x
    exact ⟨Pi.single i x,by simp [Pi.single_apply]⟩
  have sum := (traceMap K I).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr right] at sum
  simpa [add_comm] using sum

theorem model_rank [Nonempty I] (two_ne : (2:K)≠0) :
    (model K I).rank=(Fintype.card I+1)^2-(Fintype.card I+1)+2 := by
  have null := model_nullity (I:=I) two_ne
  have total := (model K I).mulVecLin.finrank_range_add_finrank_ker
  change (model K I).rank+Module.finrank K (model K I).mulVecLin.ker=_ at total
  rw [Module.finrank_pi] at total
  change _=Fintype.card (Option I × Option I) at total
  rw [Fintype.card_prod,Fintype.card_option,←pow_two] at total
  have lower : Fintype.card I+1≤(Fintype.card I+1)^2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem exact_rank (two_ne : (2:K)≠0) (c : J) (size : 2≤Fintype.card J) :
    (hessian (per K J) (point K c)).rank=(Fintype.card J)^2-Fintype.card J+2 := by
  let I := {i : J // i≠c}
  let b := Equiv.optionSubtypeNe c
  have cc : Fintype.card J=Fintype.card I+1 := (Fintype.card_congr b).symm.trans Fintype.card_option
  have pos : 0<Fintype.card I := by omega
  let _ : Nonempty I := Fintype.card_pos_iff.mp pos
  have e : hessian (per K (Option I)) (point K (none:Option I))=model K I := by
    ext u v
    exact (all_entries K (none:Option I) u v).2.2
  have same := transport_rank b (point K (none:Option I))
  rw [point_equiv b (none:Option I),e] at same
  have center : b none=c := Equiv.optionSubtypeNe_none c
  rw [center] at same
  rw [same,model_rank two_ne,cc]

theorem bedi_suagee (two_ne : (2:K)≠0) (c : J) (size : 2≤Fintype.card J) :
    PermanentBorder.value (point K c)=0 ∧ gradAt (point K c) (c,c)=1 ∧
      (hessian (per K J) (point K c)).rank=(Fintype.card J)^2-Fintype.card J+2 :=
  ⟨(all_entries K c (c,c) (c,c)).1,(all_entries K c (c,c) (c,c)).2.1,exact_rank two_ne c size⟩

#print axioms bedi_suagee
end PermanentArrow
