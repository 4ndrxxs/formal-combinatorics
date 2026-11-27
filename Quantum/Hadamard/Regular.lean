import Quantum.Hadamard.Lex

/-! Regular modular sign matrices at square orders and extensions in residue one. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

private theorem row_delta {H : RowMatrix m I} (g : Good H) (dim : (Fintype.card I : ZMod m)=1)
    (i j : I) : (∑ b, H i b*H j b) = if i=j then 1 else 0 := by
  by_cases e : i=j
  · subst j
    simpa using (g.norm_rows i).trans dim
  · simpa [e] using g.ortho i j e

private theorem column_delta {H : RowMatrix m I} (g : Good H) (dim : (Fintype.card I : ZMod m)=1)
    (a c : I) : (∑ j, H j a*H j c) = if a=c then 1 else 0 := by
  let M : Matrix I I (ZMod m) := H
  have rowId : M*M.transpose=1 := by
    ext i j
    rw [Matrix.mul_apply,Matrix.one_apply]
    exact row_delta g dim i j
  have columnId : M.transpose*M=1 := mul_eq_one_comm.mp rowId
  have h : (M.transpose*M) a c=(1:Matrix I I (ZMod m)) a c := congrArg (fun A : Matrix I I (ZMod m) => A a c) columnId
  rw [Matrix.mul_apply,Matrix.one_apply] at h
  exact h

/-- Row and column sign changes of a tensor square give an extender in residue one. -/
def regularExtension {H : RowMatrix m I} (g : Good H) [Nonempty I] (dim : (Fintype.card I : ZMod m)=1) :
    Extender m (I×I) 1 where
  entry := squareRegular g
  sign := fun i j => sign_mul (sign_mul (sign_mul (g.sign _ _) (g.sign _ _)) (g.sign _ _)) (g.sign _ _)
  row := by
    rintro ⟨i,a⟩
    rw [Fintype.sum_prod_type]
    have expansion (j b : I) : squareRegular g (i,a) (j,b) =
        (H i a*H j a)*(H i b*H j b) := by unfold squareRegular; dsimp; ring
    simp only [expansion,←Finset.mul_sum,row_delta g dim]
    have diag (j : I) : H i a*H j a*(if i=j then 1 else 0) =
        if i=j then (1:ZMod m) else 0 := by
      by_cases e : i=j
      · subst j; simp [sign_sq (g.sign i a)]
      · simp [e]
    simp [diag]
  off := by
    rintro ⟨i,a⟩ ⟨k,c⟩ ne
    rw [Fintype.sum_prod_type]
    have expansion (j b : I) : squareRegular g (i,a) (j,b) * squareRegular g (k,c) (j,b) =
        (H i a*H k c) * (H j a*H j c) * (H i b*H k b) := by
      unfold squareRegular
      dsimp
      calc
        _ = (H i a*H k c) * (H j a*H j c) * (H i b*H k b) * (H j b*H j b) := by ring
        _ = _ := by rw [sign_sq (g.sign j b),mul_one]
    simp only [expansion,←Finset.mul_sum,←Finset.sum_mul,column_delta g dim,row_delta g dim]
    by_cases e : i=k
    · have f : a≠c := fun ac => ne (Prod.ext e ac)
      simp [e,f]
    · simp [e]
  dim := by simp [Fintype.card_prod,dim]
  pos := Fintype.card_pos

theorem square_grow {m n h : ℕ} (hp : 0<h) (H : AtOrder m h) (dim : (h:ZMod m)=1)
    (np : 0<n) (N : AtOrder m n) (res : (n:ZMod m)=1) (t : ℕ) :
    AtOrder m (n+t*(h^2-1)) := by
  obtain ⟨A,g⟩:=H
  letI : NeZero h := ⟨hp.ne'⟩
  let D := regularExtension g (by simpa using dim)
  simpa [Fintype.card_prod,pow_two] using D.iterate np N res t

#print axioms regularExtension
#print axioms square_grow
end HadamardMod
