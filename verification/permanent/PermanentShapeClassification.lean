import PermanentShapeGraph
import PermanentShapeMinor0
import PermanentShapeMinor1
import PermanentShapeMinor2
import PermanentShapeMinor3
import PermanentCross
import PermanentTransferNilpotent

/-! Necessary conditions on every coordinate degeneration and on the actual
endpoint kernel of an affine determinantal representation of the five-by-five
permanent of size at most twenty-one. -/

noncomputable section
open Matrix Module MvPolynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

private theorem shape_minors (K : Type*) [Field K] [CharZero K] (i : Fin 4) :
    AmbientWitness K (shapePattern i) (shapeRank i) := by
  fin_cases i
  · exact shape_minor_0 K
  · exact shape_minor_1 K
  · exact shape_minor_2 K
  · exact shape_minor_3 K

/-- Every additive-weight pivot board belongs to one of twelve grid orbits. -/
theorem normalized_pivot_shape (weights : GridWeights) (b c : n → Cell → K)
    (D : n → n → Cell → K) (rep : per K Idx = regularDet b c D)
    (small : Fintype.card n ≤ 20) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weights.cell S) :
    ShapeAllowed S := by
  let L := (endpoints b c).ker
  have sym (t : K) (_ : t ≠ 0) : ∃ a : K, twist (fun i ↦ t^(weights.cell i)) (per K Idx) =
      C a * per K Idx := weights.twist_character t
  have prop (z : Cell → K) (hz : z ∈ L) :
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
      Fintype.card Cell + (hessian (per K Idx) z).rank + 1 ≤ (Fintype.card n+1) + finrank K L := by
    obtain ⟨g,h⟩ := normalized_partial_kernel (per_homogeneous K Idx) b c D rep z hz
    have bound : Fintype.card Cell + (hessian (per K Idx) z).rank ≤ Fintype.card n + finrank K L := h
    exact ⟨g,(Nat.add_le_add_right bound 1).trans_eq (by omega)⟩
  have ambient (z : Cell → K) (hz : ∀ j ∉ S, z j = 0) :
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
        26 + (hessian (per K Idx) z).rank ≤ (Fintype.card n+1) + S.card := by
    obtain ⟨g,h⟩ := coordinate_kernel_at_support (Fintype.card n+1) L prop weights.cell sym S card paths z hz
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ _ at h
    exact ⟨g,by omega⟩
  have full := normalized_full_line_weighted weights b c D rep small S card lift paths
  rcases shape_graph_tests S (coordinate_matching_bound S _ ambient) (shape_minors K) full with
    allowed | ⟨r,⟨z,hz,rk⟩,sz⟩
  · exact allowed
  · have h := (ambient z hz).2
    omega

/-- The remaining numerical possibilities for the dimension of the actual kernel. -/
def endpointDimensions : Finset ℕ := {5,6,7,8,9,10,11,15}

private theorem model_size (i : Fin 12) : (shapeModel i).card ∈ endpointDimensions := by
  fin_cases i <;> decide +kernel

theorem kernel_dimension_cases (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) :
    finrank K (endpoints b c).ker ∈ endpointDimensions := by
  obtain ⟨S,card,lift,paths⟩ := PermanentDegeneration.coordinate_paths (endpoints b c).ker weight weight_injective
  obtain ⟨i,orb⟩ := normalized_pivot_shape standardGridWeights b c D rep small S card lift paths
  rw [← card,orb.card_eq]
  exact model_size i

/-- Every affine representation of the specified size admits a normal form
satisfying the dimension restriction, all row-column intersection inequalities,
and nilpotence in every endpoint-kernel direction. -/
theorem affine_endpoint_shape_conditions (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) (small : Fintype.card n ≤ 21) :
    ∃ (b c : Fin A.rank → Cell → K) (D : Fin A.rank → Fin A.rank → Cell → K),
      per K Idx = regularDet b c D ∧ finrank K (endpoints b c).ker ∈ endpointDimensions ∧
      (∀ R T, min R.card T.card ≤ finrank K ↥((endpoints b c).ker ⊓ rowsColsSpace K R T)) ∧
      (∀ z ∈ (endpoints b c).ker, IsNilpotent (transfer D z)) := by
  have reg := polynomial_regularity (affineMatrix A F) rep
  have atOrigin : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [atOrigin] at reg
  obtain ⟨b,c,D,normal⟩ := normalize_regular A F reg rep (d:=3) (per_homogeneous K Idx)
  have size : Fintype.card (Fin A.rank) ≤ 20 := by rw [Fintype.card_fin]; omega
  exact ⟨b,c,D,normal,kernel_dimension_cases b c D normal size,
    kernel_rows_cols_dimension b c D normal size,endpoint_transfer_nilpotent b c D normal⟩

#print axioms normalized_pivot_shape
#print axioms kernel_dimension_cases
#print axioms affine_endpoint_shape_conditions
end PermanentFive
