import PermanentLineDeletions
import PermanentRectangleBound
import PermanentRectangleDuplicate
import PermanentLineJet00
import PermanentLineJet01
import PermanentLineJet02
import PermanentLineJet03
import PermanentLineJet04
import PermanentLineJet05
import PermanentLineJet06
import PermanentLineJet07
import PermanentLineJet08
import PermanentLineJet09
import PermanentLineAmbient00
import PermanentLineAmbient01
import PermanentLineAmbient02
import PermanentLineAmbient03

/-! The explicit small-index, simple-zero and ambient-rank certificates
for the finite full-line classification. -/

noncomputable section
open Matrix Module QuinticPencil
namespace PermanentFive
namespace Rectangle

private def pick : Fin 2 → Fin 12 → Fin 15 :=
  ![![0,1,2,3,5,6,7,8,10,11,12,13],![0,1,2,3,5,6,7,8,10,11,12,14]]

private theorem right_section (i : Fin 2) : merge ∘ pick i = id := by
  fin_cases i <;> decide +kernel

private theorem covers (i : Fin 2) : ∀ j ∈ lineWitt i, ∃ a, (extendedDirections ∘ pick i) a = j := by
  fin_cases i <;> decide +kernel

theorem folded_blocks (K : Type*) [Field K] [CharZero K] (i : Fin 2) : HasIndexFourBlock (Ext K) (lineWitt i) := by
  let s := paramS K
  let t := paramT K
  let z := value s t ∘ extendedCentre
  refine ⟨extendedDirections ∘ pick i,z,covers i,?_⟩
  intro J iso
  apply rectangle_index_le_four J
  rw [hessian_original]
  have eq : ((hessian (per (Ext K) Idx) z).submatrix (extendedDirections ∘ pick i)
      (extendedDirections ∘ pick i)) = original s t := by
    rw [← Matrix.submatrix_submatrix,show (hessian (per (Ext K) Idx) z).submatrix
      extendedDirections extendedDirections = _ from duplicated_hessian s t,Matrix.submatrix_submatrix,
      right_section]
    rfl
  rw [eq] at iso
  exact iso

end Rectangle

private theorem line_jets (K : Type*) [Field K] [CharZero K] (i : Fin 10) : HasSimpleZeroBlock K 10 (lineTen i) := by
  fin_cases i
  · exact line_ten_odd_0 K
  · exact line_ten_odd_1 K
  · exact line_ten_odd_2 K
  · exact line_ten_odd_3 K
  · exact line_ten_odd_4 K
  · exact line_ten_odd_5 K
  · exact line_ten_odd_6 K
  · exact line_ten_odd_7 K
  · exact line_ten_odd_8 K
  · exact line_ten_odd_9 K

private theorem line_ambient (K : Type*) [Field K] [CharZero K] (i : Fin 4) : HasAmbientEight K (lineAmbient i) := by
  fin_cases i
  · exact line_ambient_0 K
  · exact line_ambient_1 K
  · exact line_ambient_2 K
  · exact line_ambient_3 K

theorem line_tests_over_extension (K : Type*) [Field K] [CharZero K] (S : Finset Cell)
    (matching : ∀ p : Equiv.Perm Idx, (Finset.univ.filter
      (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3) : LineTest (Rectangle.Ext K) S :=
  line_graph_tests S matching (Rectangle.folded_blocks K) (line_jets _) (line_ambient _)

#print axioms line_tests_over_extension
end PermanentFive
