module
public import Quantum.DiagonalSixModel

/-! The diagonal four-cell tiles and the forced missing sector of every tile. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix Finset
open scoped Matrix BigOperators ComplexOrder MatrixOrder
abbrev Pair := Bit × Bit

def label (i j : Tri) : Tri := -(i+j)

theorem label_self : ∀ i, label i i=i := by decide +kernel
theorem label_swap : ∀ i j, label i j=label j i := by decide +kernel
theorem label_invol : ∀ i j, label i (label i j)=j := by decide +kernel
theorem label_ne : ∀ i j, i≠j → label i j≠i ∧ label i j≠j := by decide +kernel

namespace Model
variable (g : Model)

def e (i j : Tri) (a : Pair) := g.p (i,a.1) (j,a.2)
def tile (i j : Tri) : M := ∑ a, g.e i j a
def P (i : Tri) := g.tile i i
def X (i : Tri) : M := 1-g.P i

theorem rowTiles (i : Tri) : ∑ j, g.tile i j=1+1 := by
  calc
    _ = (∑ c, g.p (i,0) c)+(∑ c, g.p (i,1) c) := by
      simp only [tile,e,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three]
      abel
    _ = _ := by rw [g.row,g.row]

theorem colTiles (j : Tri) : ∑ i, g.tile i j=1+1 := by
  calc
    _ = (∑ r, g.p r (j,0))+(∑ r, g.p r (j,1)) := by
      simp only [tile,e,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three]
      abel
    _ = _ := by rw [g.col,g.col]

theorem diagTotal : ∑ i, g.P i=1+1 := by
  calc
    _ = (∑ r, g.p r r)+(∑ r : Idx, g.p r (r.1,r.2.rev)) := by
      simp only [P,tile,e,Fintype.sum_prod_type,Fin.sum_univ_two,Fin.sum_univ_three,
        show (0:Bit).rev=1 from rfl,show (1:Bit).rev=0 from rfl]
      abel
    _ = _ := by rw [g.main,g.anti]

theorem diagProd (i : Tri) (a b : Pair) :
    g.e i i a*g.e i i b=if a=b then g.e i i a else 0 := by
  rcases a with ⟨t,s⟩
  rcases b with ⟨u,v⟩
  fin_cases t <;> fin_cases s <;> fin_cases u <;> fin_cases v
  all_goals simp [e]
  all_goals first
    | exact g.idem _ _
    | exact g.rowOrth _ _ _ (by simp)
    | exact g.colOrth _ _ _ (by simp)
    | exact g.mainOrth _ _ (by simp)
    | exact g.antiOrth (i,0) (i,1) (by simp)
    | exact g.antiOrth (i,1) (i,0) (by simp)

theorem Pherm (i : Tri) : (g.P i)ᴴ=g.P i := by
  simp [P,tile,e,Matrix.conjTranspose_sum,g.herm]

theorem Pidem (i : Tri) : g.P i*g.P i=g.P i := by
  simp [P,tile,Finset.sum_mul,Finset.mul_sum,g.diagProd]

theorem Xherm (i : Tri) : (g.X i)ᴴ=g.X i := by simp [X,g.Pherm]

theorem PX (i : Tri) : g.P i*g.X i=0 := by simp [X,mul_sub,g.Pidem]
theorem XP (i : Tri) : g.X i*g.P i=0 := by simp [X,sub_mul,g.Pidem]

theorem Xtotal : ∑ i, g.X i=1 := by
  simp only [X,Finset.sum_sub_distrib,g.diagTotal,Fin.sum_univ_three]
  abel

theorem Xtrace (i : Tri) : (g.X i).trace=2 := by
  simp [X,P,tile,e,Matrix.trace_sub,Matrix.trace_sum,g.trace]
  <;> norm_num

theorem diagAbsorb (i : Tri) (a : Pair) : g.e i i a*g.X i=0 := by
  simp [X,P,tile,mul_sub,Finset.mul_sum,g.diagProd]

/-- Every tile paired with its transpose adds to twice the third diagonal tile. -/
theorem paired (i j : Tri) (h : i≠j) :
    g.tile i j+g.tile j i=g.P (label i j)+g.P (label i j) := by
  have aux := g.diagTotal
  simp only [Fin.sum_univ_three,P] at aux
  have row := g.rowTiles
  have col := g.colTiles
  simp only [Fin.sum_univ_three] at row col
  have h01 : g.tile 0 1+g.tile 1 0=g.tile 2 2+g.tile 2 2 := by
    linear_combination (norm := abel) row 0 + row 1 - col 2 - aux
  have h02 : g.tile 0 2+g.tile 2 0=g.tile 1 1+g.tile 1 1 := by
    linear_combination (norm := abel) row 0 + row 2 - col 1 - aux
  have h12 : g.tile 1 2+g.tile 2 1=g.tile 0 0+g.tile 0 0 := by
    linear_combination (norm := abel) row 1 + row 2 - col 0 - aux
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first
    | exact h01
    | exact h02
    | exact h12
    | exact (add_comm _ _).trans h01
    | exact (add_comm _ _).trans h02
    | exact (add_comm _ _).trans h12

theorem sandwich_nonneg (i j : Tri) (a : Pair) (H : M) (hh : Hᴴ=H) :
    0≤H*g.e i j a*H := by
  let q := g.e i j a
  have he : (q*H)ᴴ*(q*H)=H*q*H := by
    rw [Matrix.conjTranspose_mul,hh,show qᴴ=q from g.herm _ _,mul_assoc,← mul_assoc q,
      show q*q=q from g.idem _ _,mul_assoc]
  rw [← he]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg

theorem missing (i j : Tri) (a : Pair) : g.e i j a*g.X (label i j)=0 := by
  by_cases hij : i=j
  · subst j; rw [label_self]; exact g.diagAbsorb i a
  let k := label i j
  let H := g.X k
  have hh : Hᴴ=H := g.Xherm k
  have total := congrArg (fun m : M => H*m*H) (g.paired i j hij)
  change H*(g.tile i j+g.tile j i)*H=H*(g.P k+g.P k)*H at total
  simp only [mul_add,add_mul,show H*g.P k=0 from g.XP k,zero_mul,add_zero,tile,
    Finset.mul_sum,Finset.sum_mul] at total
  have ha := Finset.sum_nonneg (fun x (_ : x∈(Finset.univ : Finset Pair)) =>
    g.sandwich_nonneg i j x H hh)
  have hb := Finset.sum_nonneg (fun x (_ : x∈(Finset.univ : Finset Pair)) =>
    g.sandwich_nonneg j i x H hh)
  have h0 : ∑ x, H*g.e i j x*H=0 := le_antisymm (by
    rw [← total]
    exact le_add_of_nonneg_right hb) ha
  have z := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => g.sandwich_nonneg i j x H hh)).mp h0 a (by simp)
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  change (g.e i j a*H)ᴴ*(g.e i j a*H)=0
  rw [Matrix.conjTranspose_mul,hh,show (g.e i j a)ᴴ=g.e i j a from g.herm _ _,
    mul_assoc,← mul_assoc (g.e i j a),show g.e i j a*g.e i j a=g.e i j a from g.idem _ _]
  simpa only [mul_assoc] using z

end Model
end DiagonalSix
