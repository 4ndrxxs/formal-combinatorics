import PermanentFifteenKernel
import PermanentTenBlock
import PencilNilpotentMoments
import PolynomialRankOpen

/-! At endpoint dimension fifteen every internal transfer along the
fifteen-dimensional parameter space has fourth power zero. Full-rank Hessian centres exist
in the actual kernel because it equals a three-row or three-column space. -/

noncomputable section
open Matrix Module Equiv MvPolynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

omit [CharZero K] in
theorem SameBoard.ambient {M S : Finset Cell} {r : ℕ} (h : SameBoard M S)
    (seed : AmbientWitness K M r) : AmbientWitness K S r := by
  induction h with
  | refl => exact seed
  | move e act _ ih =>
    apply ih.relabel e (act.rename K)
    intro u hu
    simpa using hu

theorem fifteen_kernel_has_rank_ten (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20)
    (dim : finrank K (endpoints b c).ker = 15) :
    ∃ w ∈ (endpoints b c).ker, 10 ≤ (hessian (per K Idx) w).rank := by
  obtain ⟨S,orb,eq⟩ := fifteen_kernel_equals_strip b c D rep small dim
  have top (u : Cell) : u ∈ shapeModel 11 ↔ u.1.val < 3 := by
    obtain ⟨i,j⟩ := u
    fin_cases i <;> fin_cases j <;> decide +kernel
  have seed : AmbientWitness K (shapeModel 11) 10 := by
    refine ⟨(Int.castRingHom K) ∘ rowHole,?_,row_hole_rank_ten K⟩
    intro u hu
    have outside : ¬u.1.val < 3 := fun h ↦ hu ((top u).mpr h)
    by_cases at0 : u = (0,0) <;> simp [rowHole,rowPoint,outside,at0]
  obtain ⟨w,h,rk⟩ := orb.ambient seed
  exact ⟨w,eq ▸ h,rk⟩

/-- All internal transfers along the actual dimension-fifteen kernel have
fourth power zero. The statement is uniform over the whole kernel. -/
theorem fifteen_transfer_fourth_zero (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20)
    (dim : finrank K (endpoints b c).ker = 15) (z : Cell → K) (hz : z ∈ (endpoints b c).ker) :
    (transfer D z)^4 = 0 := by
  let L := (endpoints b c).ker
  have ranks := (endpoints b c).finrank_range_add_finrank_ker
  rw [dim,Module.finrank_pi] at ranks
  change _ + 15 = 25 at ranks
  have point (x : Cell → K) (hx : x ∈ L) (large : 9 < (hessian (per K Idx) x).rank) :
      (transfer D x)^4 = 0 := by
    apply transfer_power_of_full_rank (s:=3) (per_homogeneous K Idx) b c D rep x hx
      (endpoint_transfer_nilpotent b c D rep x hx)
    omega
  obtain ⟨w,hw,large⟩ := fifteen_kernel_has_rank_ten b c D rep small dim
  let G : Matrix Cell Cell (MvPolynomial Cell K) :=
    Matrix.of fun i j ↦ pderiv i (pderiv j (per K Idx))
  let T : Matrix n n (MvPolynomial Cell K) := Matrix.of fun i j ↦ linearForm (D i j)
  have evalT (x : Cell → K) : (MvPolynomial.eval x).mapMatrix T = transfer D x := by
    ext i j
    simp [T,linearForm,transfer,value,RingHom.mapMatrix_apply]
  ext i j
  have at_entry (x : Cell → K) : MvPolynomial.eval x ((T^4) i j) = ((transfer D x)^4) i j := by
    change ((MvPolynomial.eval x).mapMatrix (T^4)) i j = _
    rw [map_pow,evalT]
  have van (x : Cell → K) (hx : x ∈ L) (rk : 9 < ((MvPolynomial.eval x).mapMatrix G).rank) :
      MvPolynomial.eval x ((T^4) i j) = 0 := by rw [at_entry,point x hx rk]; rfl
  exact (at_entry z).symm.trans
    (PolynomialRankOpen.vanish_on_linear_space L G 9 w hw large ((T^4) i j) van z hz)

#print axioms fifteen_kernel_has_rank_ten
#print axioms fifteen_transfer_fourth_zero
end PermanentFive
