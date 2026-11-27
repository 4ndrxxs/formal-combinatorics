import PermanentCurveImages

/-! Finite star Laplacian on the trace-zero differences, including its
principal minor when the number of ordinary indices vanishes in the field. -/
noncomputable section
open Matrix Finset PermanentFive PermanentBorder
namespace PermanentDeformation
variable {K J S : Type*} [Field K] [Fintype J] [DecidableEq J] [Fintype S] [DecidableEq S]

def unitAt (K : Type*) [Field K] (i j : J) : K := if j=i then 1 else 0

def mode (K : Type*) [Field K] (j : J) : Option J→K := Option.elim' (-1) (unitAt K j)

theorem mode_sum (j : J) : ∑ i,mode K j i=0 := by simp [mode,Fintype.sum_option,unitAt]

private theorem pair_singles (i j : J) :
    (∑ l,(unitAt K i l)*(unitAt K j l))=if i=j then 1 else 0 := by
  simp [unitAt,eq_comm]

theorem mode_energy (i j : J) :
    (∑ l,(mode K i none-mode K i (some l))*(mode K j none-mode K j (some l)))=
      (if i=j then 1 else 0)+(Fintype.card J:K)+2 := by
  have localEq (l : J) : (mode K i none-mode K i (some l))*(mode K j none-mode K j (some l))=
      1+unitAt K i l+unitAt K j l+unitAt K i l*unitAt K j l := by
    simp only [mode,Option.elim']
    ring
  simp only [localEq,Finset.sum_add_distrib,pair_singles]
  simp [unitAt]
  ring

def gram (K : Type*) [Field K] (J : Type*) [Fintype J] (S : Type*) [Fintype S] [DecidableEq S] :
    Matrix S S K := Matrix.of (fun i j ↦ -2*((if i=j then 1 else 0)+(Fintype.card J:K)+2))

omit [DecidableEq J] in
theorem gram_det : (gram K J S).det= (-2:K)^Fintype.card S*
    (1+((Fintype.card J:K)+2)*(Fintype.card S:K)) := by
  let c := (Fintype.card J:K)+2
  let u : S→K := fun _ ↦ c
  let v : S→K := fun _ ↦ 1
  have eq : gram K J S=(-2:K) • (1+ replicateCol Unit u*replicateRow Unit v) := by
    ext i j
    simp [gram,Matrix.mul_apply,Matrix.one_apply,c,u,v,add_assoc,smul_eq_mul]
  rw [eq,Matrix.det_smul,Matrix.det_one_add_replicateCol_mul_replicateRow]
  have form : v ⬝ᵥ u=((Fintype.card J:K)+2)*(Fintype.card S:K) := by
    simp [dotProduct,u,v,c]
    ring
  rw [form]

theorem gram_full (two : (2:K)≠0) (n : (Fintype.card J:K)+1≠0) : (gram K J J).det≠0 := by
  rw [gram_det]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr two))
  convert pow_ne_zero 2 n using 1
  ring

omit [DecidableEq J] in
theorem gram_deleted (two : (2:K)≠0) (n : (Fintype.card J:K)+1=0)
    (size : Fintype.card S+1=Fintype.card J) : (gram K J S).det≠0 := by
  rw [gram_det]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr two))
  have ca := congrArg (Nat.cast : ℕ→K) size
  push_cast at ca
  have a : (Fintype.card J:K)= -1 := by linear_combination n
  have b : (Fintype.card S:K)= -2 := by linear_combination ca+n
  rw [a,b]
  norm_num

end PermanentDeformation
