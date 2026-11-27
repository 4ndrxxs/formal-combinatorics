import PermanentOddObstruction
import PermanentTwelveCover
import PermanentSimultaneous
import PermanentTenBlock
import PermanentJetPureA
import PermanentJetPureB
import PermanentJetPureC
import PermanentJetPureD
import PermanentJetPureE
import PermanentJetPureF
import PermanentJetMixedA
import PermanentJetMixedB
import PermanentJetMixedC
import PermanentAmbientRowPair
import PermanentAmbientColPair
import PermanentAmbientCrossPair
import PermanentAmbientMixed

/-! A uniform lower bound of twenty-one for affine determinantal representations
of the permanent of order five. Each of the three size ranges uses the same
coordinate degeneration of the fixed endpoint kernel. -/

noncomputable section
open Matrix MvPolynomial Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

private theorem odd_shapes (i : Fin 9) : HasOddBlock K (twelveShape i) := by
  fin_cases i
  · exact twelve_odd_0 K
  · exact twelve_odd_1 K
  · exact twelve_odd_2 K
  · exact twelve_odd_3 K
  · exact twelve_odd_4 K
  · exact twelve_odd_5 K
  · exact twelve_odd_6 K
  · exact twelve_odd_7 K
  · exact twelve_odd_8 K

private theorem ambient_shapes (i : Fin 4) : HasAmbientEight K (thirteenShape i) := by
  fin_cases i
  · exact thirteen_ambient_0 K
  · exact thirteen_ambient_1 K
  · exact thirteen_ambient_2 K
  · exact thirteen_ambient_3 K

theorem determinantal_lower_bound_twenty_one (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) : 21 ≤ Fintype.card n := by
  by_contra! small
  have regular := polynomial_regularity (affineMatrix A F) rep
  have eq : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [eq] at regular
  have hom : (per K Idx).IsHomogeneous 5 := per_homogeneous K Idx
  obtain ⟨b,c,D,hn⟩ := normalize_regular A F regular rep (d := 3) hom
  let L := (endpoints b c).ker
  obtain ⟨S,card,lift,paths⟩ := PermanentDegeneration.coordinate_paths L weight weight_injective
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
  have ambient (z : Cell → K) (hz : ∀ j ∉ S, z j = 0) :
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
        26 + (hessian (per K Idx) z).rank ≤ Fintype.card n + S.card := by
    obtain ⟨g,h⟩ := coordinate_kernel_at_support (Fintype.card n) L prop weight sym S card paths z hz
    change 25 + (hessian (per K Idx) z).rank + 1 ≤ _ at h
    exact ⟨g,by omega⟩
  by_cases limit : S.card ≤ 13
  · obtain ⟨odd,rank⟩ := small_twenty_tests S limit (coordinate_matching_bound S _ ambient)
      (odd_shapes (K:=K)) (ambient_shapes (K:=K))
    by_cases twelve : S.card ≤ 12
    · exact normalized_excludes_odd_block b c D hn (by rw [Fintype.card_fin]; omega)
        S card lift paths (odd twelve)
    · obtain ⟨z,hz,eight⟩ := rank (by omega)
      have bound := (ambient z hz).2
      omega
  · obtain ⟨bound,maxsize⟩ := large_coordinate_test S _ ambient (by omega)
    have ten := row_hole_rank_ten K
    omega

#print axioms determinantal_lower_bound_twenty_one
end PermanentFive
