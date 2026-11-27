import PermanentArrowTable

/-! Row and column identities for the finite equality-pattern table.
They isolate an off-diagonal coordinate and the trace-zero directions. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

def model (K : Type*) [Field K] (I : Type*) [DecidableEq I] : Matrix (Bigger I) (Bigger I) K :=
  Matrix.of fun e f ↦ (entry (none:Option I) e f:K)

def common (K : Type*) [Field K] {I : Type*} [DecidableEq I] : Bigger I → K
  | (some i,some j) => if i=j then 0 else 1
  | _ => 1

omit [Fintype I] in
private theorem off_rows_int (i j : I) (ij : i≠j) (f : Bigger I) :
    entry none (old (i,j)) f-entry none (left i) f-entry none (right j) f+
      entry none corner f=(if f=old (j,i) then -4 else 0) := by
  rcases f with ⟨a,b⟩
  cases a with
  | none =>
    cases b with
    | none => simp [entry,other,old,left,right,corner,ij]
    | some b => by_cases h : i=b <;> by_cases k : j=b <;> simp_all [entry,other,old,left,right,corner,eq_comm]
  | some a =>
    cases b with
    | none => by_cases h : i=a <;> by_cases k : j=a <;> simp_all [entry,other,old,left,right,corner,eq_comm]
    | some b =>
      by_cases k : a=b <;> by_cases p : i=a <;> by_cases q : j=a <;>
        by_cases r : i=b <;> by_cases s : j=b <;>
        simp_all [entry,other,old,left,right,corner,eq_comm]

omit [Fintype I] in
theorem off_rows (i j : I) (ij : i≠j) (f : Bigger I) :
    model K I (old (i,j)) f-model K I (left i) f-model K I (right j) f+model K I corner f=
      (if f=old (j,i) then -4 else 0) := by
  have h := congrArg (Int.castRingHom K) (off_rows_int i j ij f)
  simpa [model,apply_ite (Int.castRingHom K)] using h

omit [Fintype I] in
theorem common_cols (i : I) (e : Bigger I) :
    model K I e (old (i,i))+model K I e (left i)+model K I e (right i)=common K e := by
  rcases e with ⟨a,b⟩
  cases a with
  | none =>
    cases b with
    | none => simp [entry,other,common,model,old,left,right]
    | some b => by_cases h : b=i <;> simp [entry,other,common,model,old,left,right,h,Ne.symm]
  | some a =>
    cases b with
    | none => by_cases h : a=i <;> simp [entry,other,common,model,old,left,right,h,Ne.symm]
    | some b =>
      by_cases h : a=b <;> by_cases s : a=i <;> by_cases t : b=i <;>
        simp_all [entry,other,common,model,old,left,right,eq_comm]
      ring

def unitDirection (K : Type*) [Field K] (i : I) : Bigger I → K :=
  Pi.single (old (i,i)) 1+Pi.single (left i) 1+Pi.single (right i) 1

def diagonalLift (d : I → K) : Bigger I → K
  | (some i,some j) => if i=j then d i else 0
  | (some i,none) => d i
  | (none,some j) => d j
  | (none,none) => 0

theorem diagonal_sum (d : I → K) : diagonalLift d=∑ i, d i • unitDirection K i := by
  funext ⟨a,b⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,unitDirection,Pi.add_apply,Pi.single_apply]
  cases a with
  | none => cases b <;> simp [diagonalLift,old,left,right,mul_ite]
  | some a =>
    cases b with
    | none => simp [diagonalLift,old,left,right,mul_ite]
    | some b =>
      by_cases h : a=b
      · subst b; simp [diagonalLift,old,left,right,mul_ite]
      · have ne (i : I) : ¬(a=i ∧ b=i) := fun q ↦ h (q.1.trans q.2.symm)
        simp [diagonalLift,old,left,right,h,ne]

theorem image_unit (i : I) : model K I *ᵥ unitDirection K i=common K := by
  funext e
  simpa [unitDirection,Matrix.mulVec_add,Matrix.mulVec_single_one] using common_cols (K:=K) i e

theorem image_lift (d : I → K) : model K I *ᵥ diagonalLift d=(∑ i,d i) • common K := by
  rw [diagonal_sum,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,image_unit,Finset.sum_smul]

#print axioms image_lift
end PermanentArrow
