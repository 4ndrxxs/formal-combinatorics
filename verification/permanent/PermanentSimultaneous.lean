import PermanentUnrestricted
import QuinticRestrictedTorus

/-! The ambient and restricted Hessian inequalities hold simultaneously
on one coordinate degeneration of one common endpoint kernel. -/

noncomputable section
open Matrix MvPolynomial Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem simultaneous_coordinate_bounds (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) :
    ∃ S : Finset Cell,
      (∀ z : Cell → K, (∀ j ∉ S, z j = 0) →
        (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
        26 + (hessian (per K Idx) z).rank ≤ Fintype.card n + S.card) ∧
      (∀ y : Cell → K,
        ((hessian (per K Idx) y).submatrix ((↑) : S → Cell) ((↑) : S → Cell)).rank + 50 ≤
          2 * Fintype.card n + 2*S.card - 2) := by
  have regular := polynomial_regularity (affineMatrix A F) rep
  have eq : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [eq] at regular
  have hom : (per K Idx).IsHomogeneous 5 := per_homogeneous K Idx
  obtain ⟨b,c,D,hn⟩ := normalize_regular A F regular rep (d := 3) hom
  let P := endpoints b c
  let L := P.ker
  obtain ⟨S,card,_,paths⟩ := PermanentDegeneration.coordinate_paths L weight weight_injective
  have sym (t : K) (_ : t ≠ 0) : ∃ a : K, twist (fun i ↦ t^(weight i)) (per K Idx) =
      C a * per K Idx := weight_twist t
  have prop (z : Cell → K) (hz : z ∈ L) :
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
        Fintype.card Cell + (hessian (per K Idx) z).rank + 1 ≤ Fintype.card n + finrank K L := by
    obtain ⟨g,h⟩ := normalized_partial_kernel hom b c D hn z hz
    rw [Fintype.card_fin] at h
    change 25 + (hessian (per K Idx) z).rank ≤ A.rank + finrank K L at h
    refine ⟨g,?_⟩
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ Fintype.card n + finrank K L
    omega
  refine ⟨S,?_,?_⟩
  · intro z hz
    obtain ⟨g,h⟩ := coordinate_kernel_at_support (Fintype.card n) L prop weight sym S card paths z hz
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ _ at h
    exact ⟨g,by omega⟩
  · let a := finrank K P.range
    have dim := P.finrank_range_add_finrank_ker.trans (Module.finrank_pi K)
    change a + finrank K L = 25 at dim
    have lo (y : Cell → K) : finrank K ((hessian (per K Idx) y).toBilin'.restrict L).range +
        2*a ≤ 2*A.rank := by
      have bnd := normalized_restricted_hessian hom b c D hn y
      simpa only [Fintype.card_fin] using bnd
    intro y
    have bound := restricted_rank_at_support L weight S paths sym (2*A.rank-2*a)
      (fun z ↦ Nat.le_sub_of_add_le (lo z)) y
    have base := lo y
    omega

#print axioms simultaneous_coordinate_bounds
end PermanentFive
