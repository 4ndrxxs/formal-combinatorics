import PermanentBoardScalarExtension
import PermanentFifteenRankProfile
import PermanentCurvePrime

/-! A coordinate strip in a normalized permanent representation transports
the same nilpotence and Hessian-rank implications to every field extension. -/
noncomputable section
open Matrix Module Polynomial Finset QuinticPencil PermanentCurve
namespace PermanentFive
variable {K E R T n : Type*} [Field K] [Field E] [CommRing R] [CommRing T]
  [Fintype n] [DecidableEq n]

def transferAt (g : K →+* R) (D : n → n → Cell → K) (e : Equiv.Perm Cell) (z : Cell → R) :
    Matrix n n R := transfer (fun i j x ↦ g (D i j x)) (z ∘ e.symm)

omit [Fintype n] [DecidableEq n] in
theorem transferAt_map (f : R →+* T) (g : K →+* R) (D : n → n → Cell → K)
    (e : Equiv.Perm Cell) (z : Cell → R) :
    (transferAt g D e z).map f = transferAt (f.comp g) D e (f ∘ z) := by
  apply Matrix.ext
  intro i j
  simp [transferAt,transfer,value,map_sum,map_mul,Function.comp_apply]

omit [Fintype n] [DecidableEq n] in
theorem transferAt_top (g : K →+* E) (D : n → n → Cell → K) (e : Equiv.Perm Cell)
    (u : E) (i j : n) :
    PencilWeight.Top ((transferAt (C.comp g) D e (plane (X : E[X]) (C u))) i j) 1
      ((transferAt g D e ((Int.castRingHom E) ∘ slopePoint)) i j) := by
  change PencilWeight.Top (∑ x : Cell, C (g (D i j x)) * plane (X : E[X]) (C u) (e.symm x)) 1
    (∑ x : Cell, g (D i j x) * ((slopePoint (e.symm x) : ℤ) : E))
  apply PencilWeight.top_sum
  intro x _
  have c : PencilWeight.Top (C (g (D i j x))) 0 (g (D i j x)) := by simp [PencilWeight.Top]
  exact PencilWeight.top_mul c (top_coordinate u (e.symm x))

theorem scalar_charZero [CharZero K] (g : K →+* E) : CharZero E where
  cast_injective m n eq := Nat.cast_injective (g.injective
    (show g (m : K)=g (n : K) by simpa only [map_natCast] using eq))

theorem strip_over_field [CharZero K] (g : K →+* E) (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20) (S : Finset Cell)
    (whole : (endpoints b c).ker = boardSpace K S) (card : S.card=15)
    (e : Equiv.Perm Cell) (motion : GridMotion e) (board : ∀ u, u ∈ shapeModel 11 ↔ e u ∈ S)
    (z : Cell → E) (supp : ∀ u ∉ shapeModel 11, z u=0) :
    (transferAt g D e z)^4=0 ∧ (10 ≤ (hessian (per E Idx) z).rank → ((transferAt g D e z)^3).rank=5) := by
  let _ : CharZero E := scalar_charZero g
  let b' (i : n) (j : Cell) := g (b i j)
  let c' (i : n) (j : Cell) := g (c i j)
  let D' (i j : n) (u : Cell) := g (D i j u)
  have rep' : per E Idx = regularDet b' c' D' := by
    rw [←mapped_permanent g,rep,mapped_regular_det]
  have whole' : (endpoints b' c').ker=boardSpace E S := extend_coordinate_kernel g b c S whole
  have dim : finrank E (endpoints b' c').ker=15 := by rw [whole',board_dimension,card]
  have hz : z ∘ e.symm ∈ (endpoints b' c').ker := by
    rw [whole']
    intro u out
    apply supp
    intro inside
    exact out (by simpa using (board (e.symm u)).mp inside)
  refine ⟨fifteen_transfer_fourth_zero b' c' D' rep' size.le dim _ hz,?_⟩
  intro high
  have high' : 10 ≤ (hessian (per E Idx) (z ∘ e.symm)).rank := by
    rw [(transport e (motion.rename E) z).2]
    exact high
  exact (fifteen_transfer_rank_profile b' c' D' rep' size dim _ hz high').2.2.1

#print axioms strip_over_field
end PermanentFive
