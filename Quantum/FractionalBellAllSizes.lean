module
public import Quantum.FractionalBellThreeClassical
public import Mathlib.Analysis.Convex.Topology

/-! For every size at least two, a real rational SudoQ has nonclassical
coordinate probabilities. Size three uses its ternary product construction.
Other sizes insert the four-dimensional binary counterexample into an
intercalate-bearing Latin square. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalIntercalate
  FractionalPolygons.Sudoku Complex Finset
open scoped BigOperators ComplexConjugate Topology

def coordinateReadout {I : Type*} [Fintype I] (v : Grid I) : BigProb I :=
  fun q k => normSq (v q.1 q.2 k)

theorem coordinate_measured {I : Type*} [Fintype I] [DecidableEq I] (v : Grid I) (h : Valid v) :
    Measured (coordinateReadout v) :=
  ⟨v,EuclideanSpace.basisFun _ ℂ,h,fun q k => by simp [coordinateReadout]⟩

theorem classical_finite {I : Type*} [Fintype I] [DecidableEq I] :
    {p : BigProb I | Classical p}.Finite := by
  let f (m : Site I → Index I) : BigProb I := fun q k => if m q=k then 1 else 0
  apply (Set.finite_range f).subset
  rintro p ⟨m,_,h⟩
  exact ⟨m,(funext fun q => funext (h q)).symm⟩

theorem classical_hull_closed {I : Type*} [Fintype I] [DecidableEq I] :
    IsClosed (convexHull ℝ {p : BigProb I | Classical p}) :=
  classical_finite.isClosed_convexHull ℝ

theorem coordinate_nonclassical (N : ℕ) (hN : 2≤N) :
    ∃ v : Grid (Fin N), Valid v ∧ RationalEntries v ∧
      coordinateReadout v∉convexHull ℝ {p | Classical p} := by
  by_cases eq : N=3
  · subst N
    refine ⟨FractionalBellThree.v,FractionalBellThree.v_valid,FractionalBellThree.v_rational,?_⟩
    have h : coordinateReadout FractionalBellThree.v=FractionalBellThree.data :=
      funext fun q => funext (FractionalBellThree.born q)
    rw [h]
    exact FractionalBellThree.outside
  · let L := FractionalIntercalate.ofOrders N (by omega)
    let w := FractionalBellWitness.smallVector
    let v : Grid (Fin N) := fun r c => inserted L w (r,c)
    refine ⟨v,inserted_valid L w FractionalBellWitness.small_grid,
      rational_inserted L w rational_small,?_⟩
    intro h
    have small := trim_classical_hull L h (bare_supported L w)
    have val : trim L (coordinateReadout v)=FractionalBellWitness.smallTable := by
      funext q k
      change bareTable L w (position L q) (coordinate L k)=_
      rw [trim_bare]
      exact FractionalBellWitness.small_born q k
    rw [val] at small
    exact FractionalBellWitness.outside small

#print axioms coordinate_nonclassical
end FractionalBlockBell

