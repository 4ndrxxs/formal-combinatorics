import PermanentFive

/-! The diagonal row and column scalings associated to arbitrary nonnegative weights. -/
namespace PermanentFive
structure GridWeights where
  row : Idx → ℕ
  col : Idx → ℕ

def GridWeights.cell (q : GridWeights) (u : Cell) : ℕ := q.row u.1 + q.col u.2

def standardGridWeights : GridWeights := ⟨fun i ↦ 5*i.val, fun j ↦ j.val⟩

theorem GridWeights.twist_character (q : GridWeights) {K : Type*} [Field K] (t : K) :
    ∃ a : K, QuinticPencil.twist (fun u ↦ t ^ q.cell u) (per K Idx) =
      MvPolynomial.C a * per K Idx := by
  refine ⟨(∏ i, t ^ q.row i) * (∏ j, t ^ q.col j),?_⟩
  simpa [GridWeights.cell,pow_add] using
    row_column_twist (fun i ↦ t ^ q.row i) (fun j ↦ t ^ q.col j)

#print axioms GridWeights.twist_character
end PermanentFive
