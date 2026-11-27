import PermanentBoardRigidity
import QuinticScalarExtension

/-! A kernel that equals a coordinate board over a field equals that same
board after each scalar extension. Board symmetries act uniformly over
all extension fields. -/
noncomputable section
open Matrix Module Finset MvPolynomial QuinticPencil
namespace PermanentFive
variable {K E n : Type*} [Field K] [Field E] [Fintype n] [DecidableEq n]

private def boardCoordinates (K : Type*) [Field K] (S : Finset Cell) :
    boardSpace K S ≃ₗ[K] (S → K) where
  toFun x i := x.val i.val
  invFun y := ⟨fun j ↦ if h : j ∈ S then y ⟨j,h⟩ else 0,fun j hj ↦ dite_eq_right hj⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases h : j∈S
    · simp [h]
    · simpa [h] using (x.property j h).symm
  right_inv y := by funext j; simp [j.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem board_dimension (K : Type*) [Field K] (S : Finset Cell) : finrank K (boardSpace K S) = S.card :=
  (boardCoordinates K S).finrank_eq.trans ((Module.finrank_pi K).trans (Fintype.card_coe _))

theorem extend_coordinate_kernel (g : K →+* E) (b c : n → Cell → K) (S : Finset Cell)
    (whole : (endpoints b c).ker = boardSpace K S) :
    (endpoints (fun i j ↦ g (b i j)) (fun i j ↦ g (c i j))).ker = boardSpace E S := by
  classical
  let _ := g.toAlgebra
  let B (i : n) (j : Cell) := g (b i j)
  let C' (i : n) (j : Cell) := g (c i j)
  have rows (u : Cell) (hu : u ∈ S) (i : n) : b i u=0 ∧ c i u=0 := by
    let x : Cell → K := fun v ↦ if v=u then 1 else 0
    have hx : x ∈ (endpoints b c).ker := by
      rw [whole]
      intro v hv
      have ne : v ≠ u := fun e ↦ hv (e ▸ hu)
      exact ite_eq_right ne
    obtain ⟨a,d⟩ := (endpoint_zero_iff b c x).mp hx
    simpa [value,x,mul_ite] using And.intro (a i) (d i)
  have incl : boardSpace E S ≤ (endpoints B C').ker := by
    intro y hy
    apply (endpoint_zero_iff B C' y).mpr
    constructor <;> intro i <;> apply Finset.sum_eq_zero <;> intro u _
    · by_cases h : u∈S
      · simp [B,(rows u h i).1]
      · simp [hy u h]
    · by_cases h : u∈S
      · simp [C',(rows u h i).2]
      · simp [hy u h]
  have card : S.card = finrank K (endpoints b c).ker := by rw [whole,board_dimension]
  have d : finrank E (endpoints B C').ker ≤ S.card := by
    apply extended_endpoint_dimension (E:=E) b c S card
    intro z
    refine ⟨fun i ↦ if i∈S then z i else 0,?_,?_⟩
    · rw [whole]
      intro i hi
      exact ite_eq_right hi
    · intro i hi
      exact ite_eq_left hi
  exact (Submodule.eq_of_le_of_finrank_le incl (d.trans_eq (board_dimension E S).symm)).symm

inductive GridMotion : Equiv.Perm Cell → Prop
  | refl : GridMotion (Equiv.refl _)
  | step {a e} : GridMotion a → GridAction e → GridMotion (a.trans e)

theorem GridMotion.rename {e : Equiv.Perm Cell} (m : GridMotion e) (R : Type*) [CommRing R] :
    MvPolynomial.rename e (per R Idx) = per R Idx := by
  induction m with
  | refl => exact MvPolynomial.rename_id_apply _
  | step _ a ih => exact rename_comp ih (a.rename R)

theorem SameBoard.motion {M S : Finset Cell} (h : SameBoard M S) :
    ∃ e : Equiv.Perm Cell, GridMotion e ∧ ∀ u, u ∈ M ↔ e u ∈ S := by
  induction h with
  | refl => exact ⟨Equiv.refl _,.refl,fun _ ↦ Iff.rfl⟩
  | move e a _ ih =>
    obtain ⟨g,m,mem⟩ := ih
    refine ⟨g.trans e,.step m a,fun u ↦ ?_⟩
    simpa using mem u

#print axioms extend_coordinate_kernel
#print axioms SameBoard.motion
end PermanentFive
