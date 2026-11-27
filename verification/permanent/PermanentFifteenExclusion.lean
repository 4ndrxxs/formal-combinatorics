import PermanentCurveTransfer
import PencilFourPrime

/-! A size-twenty-one affine determinant for the five-by-five permanent
cannot have endpoint kernel of dimension fifteen. The proof compares a
degree-fifteen irreducible Hessian divisor with the smaller closed point
forced by the nilpotent transfer pencil. -/
noncomputable section
open Matrix Module Polynomial Finset QuinticPencil PermanentCurve
namespace PermanentFive
variable {K E H n : Type*} [Field K] [Field E] [Field H] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private theorem map_test (f : E[X] →+* H) (g : K →+* E) (D : n → n → Cell → K)
    (e : Equiv.Perm Cell) (u : E) :
    (transferAt (C.comp g) D e (plane X (C u))).map f =
      transferAt (f.comp (C.comp g)) D e (plane (f X) (f (C u))) := by
  rw [transferAt_map,plane_map]

theorem fifteen_impossible [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20) :
    finrank K (endpoints b c).ker ≠ 15 := by
  intro dim
  obtain ⟨S,orbit,whole⟩ := fifteen_kernel_equals_strip b c D rep size.le dim
  have card : S.card=15 := by rw [←board_dimension K,←whole,dim]
  obtain ⟨e,motion,board⟩ := orbit.motion
  let L := RatFunc K
  let g : K →+* L := RatFunc.C
  let _ : CharZero L := scalar_charZero g
  let u : L := RatFunc.X
  let A := transferAt (C.comp g) D e (plane (X : L[X]) (C u))
  let a := transferAt g D e ((Int.castRingHom L) ∘ slopePoint)
  have top (i j) : PencilWeight.Top (A i j) 1 (a i j) := transferAt_top g D e u i j
  have inf := strip_over_field g b c D rep size S whole card e motion board
    ((Int.castRingHom L) ∘ slopePoint) (fun x hx ↦ slope_support x hx)
  have rank₁ : (a^3).rank=5 := inf.2 (slope_rank L)
  let h := algebraMap L[X] (RatFunc L)
  have mapped := map_test h g D e u
  have gen := (strip_over_field (h.comp (C.comp g)) b c D rep size S whole card e motion board
    (plane (h X) (h (C u))) (plane_support _ _)).1
  have nil : A^4=0 := by
    have eq : h.mapMatrix (A^4)=h.mapMatrix 0 := by
      rw [map_pow,map_zero]
      change (A.map h)^4=0
      rw [show A.map h = _ from mapped]
      exact gen
    apply Matrix.ext
    intro i j
    apply IsFractionRing.injective L[X] (RatFunc L)
    exact congrFun (congrFun eq i) j
  obtain ⟨p,hp,d,loss⟩ := PencilLayers.four_step_small_prime A a size top nil inf.1 rank₁
  let _ : Fact (Irreducible p) := ⟨hp⟩
  let m := AdjoinRoot.mk p
  change ((A.map m)^3).rank ≠ 5 at loss
  apply loss
  rw [show A.map m = _ from map_test m g D e u]
  apply (strip_over_field (m.comp (C.comp g)) b c D rep size S whole card e motion board
    (plane (m X) (m (C u))) (plane_support _ _)).2
  exact prime_rank K p hp d

theorem endpoint_dimension_interval [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20) :
    5 ≤ finrank K (endpoints b c).ker ∧ finrank K (endpoints b c).ker ≤ 11 := by
  have cases := kernel_dimension_cases b c D rep size.le
  have omit15 := fifteen_impossible b c D rep size
  simp only [endpointDimensions,Finset.mem_insert,Finset.mem_singleton] at cases
  omega

#print axioms fifteen_impossible
#print axioms endpoint_dimension_interval
end PermanentFive
