import PermanentLineTests
import QuinticPivotExtension
import PermanentUnrestricted
import PermanentSaturatedLine


/-! Every coordinate degeneration of the endpoint kernel of a hypothetical
size-twenty-one permanent pencil contains a full row or column. In the actual
kernel the projection onto that line is therefore surjective. -/

noncomputable section
open Matrix Module MvPolynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

private theorem line_over_parameters (b c : n → Cell → Rectangle.Ext K)
    (D : n → n → Cell → Rectangle.Ext K) (rep : per (Rectangle.Ext K) Idx = regularDet b c D)
    (small : Fintype.card n ≤ 20) (S : Finset Cell)
    (card : S.card = finrank (Rectangle.Ext K) (endpoints b c).ker)
    (lift : ∀ z : Cell → Rectangle.Ext K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) : ContainsFullLine S := by
  let E := Rectangle.Ext K
  let L := (endpoints b c).ker
  have sym (t : E) (_ : t ≠ 0) : ∃ a : E, twist (fun i ↦ t^(weight i)) (per E Idx) =
      C a * per E Idx := weight_twist t
  have prop (z : Cell → E) (hz : z ∈ L) :
      (∀ i, MvPolynomial.eval z (pderiv i (per E Idx)) = 0) ∧
      Fintype.card Cell + (hessian (per E Idx) z).rank + 1 ≤ (Fintype.card n+1) + finrank E L := by
    obtain ⟨g,h⟩ := normalized_partial_kernel (per_homogeneous E Idx) b c D rep z hz
    have bound : Fintype.card Cell + (hessian (per E Idx) z).rank ≤ Fintype.card n + finrank E L := h
    exact ⟨g,(Nat.add_le_add_right bound 1).trans_eq (by omega)⟩
  have ambient (z : Cell → E) (hz : ∀ j ∉ S, z j = 0) :
      (∀ i, MvPolynomial.eval z (pderiv i (per E Idx)) = 0) ∧
        26 + (hessian (per E Idx) z).rank ≤ (Fintype.card n+1) + S.card := by
    obtain ⟨g,h⟩ := coordinate_kernel_at_support (Fintype.card n+1) L prop weight sym S card paths z hz
    change 25 + (hessian (per E Idx) z).rank + 1 ≤ _ at h
    exact ⟨g,by omega⟩
  rcases line_tests_over_extension K S (coordinate_matching_bound S _ ambient) with full|witt|ten|⟨rank,bound⟩
  · exact full
  · exact (normalized_excludes_index_four b c D rep small S card lift paths witt).elim
  · exact (normalized_excludes_simple_zero 5 b c D rep (by omega) S card lift paths ten).elim
  · obtain ⟨z,hz,eight⟩ := rank
    have h := (ambient z hz).2
    have eight' : 8 ≤ (hessian (per E Idx) z).rank := eight
    omega

private theorem normalized_data_over (E : Type*) [Field E] [Algebra K E] (b c : n → Cell → K)
    (D : n → n → Cell → K) (rep : per K Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) :
    ∃ (b' c' : n → Cell → E) (D' : n → n → Cell → E), per E Idx = regularDet b' c' D' ∧
      S.card = finrank E (endpoints b' c').ker ∧
      (∀ z : Cell → E, ∃ x ∈ (endpoints b' c').ker, ∀ i ∈ S, x i = z i) ∧
      PermanentDegeneration.HasCoordinatePaths (endpoints b' c').ker weight S := by
  let f := algebraMap K E
  have eq := congrArg (MvPolynomial.map f) rep
  rw [mapped_permanent,mapped_regular_det] at eq
  exact ⟨_,_,_,eq,extend_endpoint_pivots b c weight S card lift paths⟩

theorem normalized_full_line (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) : ContainsFullLine S := by
  obtain ⟨b₁,c₁,D₁,eq₁,card₁,lift₁,paths₁⟩ := normalized_data_over (RatFunc K) b c D rep S card lift paths
  obtain ⟨b₂,c₂,D₂,eq₂,card₂,lift₂,paths₂⟩ := normalized_data_over (Rectangle.Ext K) b₁ c₁ D₁ eq₁ S card₁ lift₁ paths₁
  exact line_over_parameters b₂ c₂ D₂ eq₂ small S card₂ lift₂ paths₂

theorem normalized_surjective_line (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) :
    ∃ axis i, ∀ y : Idx → K, ∃ x ∈ (endpoints b c).ker, ∀ j, x (linePoint axis i j) = y j := by
  obtain ⟨S,card,lift,paths⟩ := PermanentDegeneration.coordinate_paths (endpoints b c).ker weight weight_injective
  obtain ⟨axis,i,inside⟩ := normalized_full_line b c D rep small S card lift paths
  refine ⟨axis,i,?_⟩
  intro y
  let z (u : Cell) := if axis then y u.1 else y u.2
  obtain ⟨x,hx,eq⟩ := lift z
  refine ⟨x,hx,fun j ↦ (eq _ (inside j)).trans ?_⟩
  cases axis <;> rfl

/-- In a size-at-most-twenty-one affine representation, a regular normal form
admits all prescribed values on one whole input row or column inside its actual
endpoint kernel. -/
theorem affine_surjective_endpoint_line (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) (small : Fintype.card n ≤ 21) :
    ∃ (b c : Fin A.rank → Cell → K) (D : Fin A.rank → Fin A.rank → Cell → K),
      per K Idx = regularDet b c D ∧
      ∃ axis i, ∀ y : Idx → K, ∃ x ∈ (endpoints b c).ker, ∀ j, x (linePoint axis i j) = y j := by
  have regular := polynomial_regularity (affineMatrix A F) rep
  have eq : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [eq] at regular
  obtain ⟨b,c,D,normal⟩ := normalize_regular A F regular rep (d:=3) (per_homogeneous K Idx)
  exact ⟨b,c,D,normal,normalized_surjective_line b c D normal (by rw [Fintype.card_fin]; omega)⟩

/-- The coordinate space supported on a specified row or column. -/
def lineFill (K : Type*) [Field K] (axis : Bool) (i : Idx) :
    (Idx → K) →ₗ[K] (Cell → K) := LinearMap.pi fun u : Cell ↦
  if (if axis then u.2 else u.1) = i then LinearMap.proj (if axis then u.1 else u.2) else 0

/-- At endpoint-kernel dimension five the entire kernel is one coordinate line. -/
theorem five_kernel_equals_line (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n = 20)
    (dim : finrank K (endpoints b c).ker = 5) :
    ∃ axis i, (endpoints b c).ker = (lineFill K axis i).range := by
  have rk := (endpoints b c).finrank_range_add_finrank_ker
  rw [dim,Module.finrank_pi] at rk
  change _ + 5 = 25 at rk
  have sat : finrank K (endpoints b c).range = Fintype.card n := by omega
  have supported : ∃ (axis : Bool) (i : Idx), ∀ z ∈ (endpoints b c).ker, ∀ u : Cell,
      (if axis then u.2 else u.1) ≠ i → z u = 0 := by
    rcases saturated_kernel_on_line b c D rep sat dim.ge with ⟨i,h⟩|⟨i,h⟩
    · exact ⟨false,i,h⟩
    · exact ⟨true,i,h⟩
  obtain ⟨axis,i,h⟩ := supported
  refine ⟨axis,i,Submodule.eq_of_le_of_finrank_le ?_ ?_⟩
  · intro z hz
    refine ⟨fun j ↦ z (linePoint axis i j),?_⟩
    funext u
    rcases u with ⟨r,c'⟩
    cases axis with
    | false =>
      by_cases eq : r = i
      · subst r
        simp [lineFill,linePoint]
      · simp [lineFill,eq,h z hz (r,c') eq]
    | true =>
      by_cases eq : c' = i
      · subst c'
        simp [lineFill,linePoint]
      · simp [lineFill,eq,h z hz (r,c') eq]
  · rw [dim]
    simpa using (lineFill K axis i).finrank_range_le

#print axioms five_kernel_equals_line
#print axioms affine_surjective_endpoint_line
#print axioms normalized_full_line
#print axioms normalized_surjective_line
end PermanentFive
