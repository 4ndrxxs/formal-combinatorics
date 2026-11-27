import PermanentUnrestricted
import QuinticNormalized
import QuinticEvenTorus

/-! The saturation argument rules out dimension sixteen for an affine
determinantal expression of the generic five-by-five permanent. -/

noncomputable section
open MvPolynomial Matrix Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

/-- Every regular representation over a characteristic-zero field has
size at least seventeen. -/
theorem regular_bound_seventeen (A : Matrix n n K) (F : Cell → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) (rep : per K Idx = (affineMatrix A F).det) :
    17 ≤ Fintype.card n := by
  by_contra! small
  have prior := regular_bound A F regular rep
  have size : Fintype.card n = 16 := by omega
  have hsize : A.rank = 15 := by omega
  have hom : (per K Idx).IsHomogeneous 5 := per_homogeneous K Idx
  obtain ⟨b,c,D,hn⟩ := normalize_regular A F regular rep (d := 3) hom
  let P := endpoints b c
  let L := P.ker
  have conditions (z : Cell → K) (hz : z ∈ L) :
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
      Fintype.card Cell + (hessian (per K Idx) z).rank + 1 ≤ 16 + finrank K L := by
    obtain ⟨g,h⟩ := normalized_partial_kernel hom b c D hn z hz
    rw [Fintype.card_fin] at h
    change 25 + (hessian (per K Idx) z).rank ≤ A.rank + finrank K L at h
    refine ⟨g,?_⟩
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ 16 + finrank K L
    omega
  obtain ⟨S,card,special,properties⟩ := coordinate_kernel_of_subspace 16 L conditions weight
    weight_injective (fun t _ ↦ weight_twist t)
  have ten : S.card = 10 := size_sixteen_support S (K:=K) (fun z hz ↦ by
    obtain ⟨g,h⟩ := properties z hz
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ 16 + S.card at h
    exact ⟨g,by omega⟩)
  have full : finrank K (endpoints b c).range = Fintype.card (Fin A.rank) := by
    have dims := P.finrank_range_add_finrank_ker.trans (Module.finrank_pi K)
    change finrank K P.range + finrank K L = 25 at dims
    change finrank K P.range = Fintype.card (Fin A.rank)
    rw [Fintype.card_fin]
    omega
  have scale (t : K) (_ : t ≠ 0) : ∃ a : K, ∀ v : Cell → K,
      MvPolynomial.eval (fun i ↦ t^(weight i)*v i) (per K Idx) = a * MvPolynomial.eval v (per K Idx) := by
    obtain ⟨a,eq⟩ := weight_twist t
    refine ⟨a,fun v ↦ ?_⟩
    rw [← eval_twist,eq,map_mul,MvPolynomial.eval_C]
  have bound := even_support_bound S (K:=K) (specialize_even L S weight (per K Idx) scale special
    (fun z hz y ↦ normalized_even_difference hom b c D hn full z hz y))
  omega

/-- The generic permanent of order five has unrestricted affine determinantal
complexity at least seventeen over every field of characteristic zero. -/
theorem determinantal_lower_bound_seventeen (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) : 17 ≤ Fintype.card n := by
  have regular := polynomial_regularity (affineMatrix A F) rep
  have eq : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [eq] at regular
  exact regular_bound_seventeen A F regular rep

#print axioms regular_bound_seventeen
#print axioms determinantal_lower_bound_seventeen
end PermanentFive
