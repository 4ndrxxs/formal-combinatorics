module
public import Quantum.FractionalBellAllSizes
public import Quantum.FractionalRationalRotation

/-! Every size N ≥ 2 has a strictly positive measured fractional Sudoku
outside the scalar classical polytope. All amplitudes are normalized real
rational numbers in the coordinate measuring basis. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumCertificate QuantumSudoku FractionalPolygons.Sudoku Complex Finset
open scoped BigOperators ComplexConjugate Topology

private theorem transformed_valid {I : Type*} [Fintype I] [DecidableEq I]
    {v : Grid I} (hv : Valid v) (U : H I ≃ₗᵢ[ℂ] H I) : Valid (fun r c => U (v r c)) := by
  have lift {w : Index I → H I} (line : BasisLine w) : BasisLine (fun k => U (w k)) := by
    obtain ⟨B,he⟩ := line
    exact ⟨B.map U,funext fun k => by simp [he]⟩
  exact ⟨fun r => lift (hv.row r),fun c => lift (hv.column c),fun x y => lift (hv.block x y)⟩

theorem rational_full_perturbation {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (v : Grid I) (valid : Valid v) (rat : RationalEntries v) (G : Set (BigProb I)) (hG : IsOpen G)
    (member : coordinateReadout v∈G) :
    ∃ w : Grid I, Valid w ∧ RationalEntries w ∧ (∀ q k, 0<coordinateReadout w q k) ∧
      coordinateReadout w∈G := by
  choose z hz using rat
  let a (q : Site I) := z q.1 q.2
  have as_vec (q : Site I) : FractionalRationalRotation.state (a q)=v q.1 q.2 := by
    ext k
    exact (hz q.1 q.2 k).symm
  have nonzero (q : Site I) : ∃ k, a q k≠0 := by
    by_contra! allz
    have eq : v q.1 q.2=0 := by
      ext k
      rw [hz]
      simpa [a] using congrArg (fun w : ℚ => (w:ℂ)) (allz k)
    obtain ⟨B,e⟩ := valid.row q.1
    have n := B.orthonormal.norm_eq_one q.2
    rw [congrFun e q.2,eq,norm_zero] at n
    norm_num at n
  have init : FractionalRationalRotation.probabilities a=coordinateReadout v := by
    funext q k
    rw [coordinateReadout,hz]
    norm_num [FractionalRationalRotation.probabilities,a,Complex.normSq_ratCast,pow_two]
  obtain ⟨U,b,eq,nz,inside⟩ := FractionalRationalRotation.perturb a nonzero G hG (init ▸ member)
  let w : Grid I := fun r c => U (v r c)
  have eqb (q : Site I) (k : Index I) : w q.1 q.2 k=(b q k:ℂ) := by
    change U (v q.1 q.2) k=_
    rw [←as_vec q,eq]
  have out : coordinateReadout w=FractionalRationalRotation.probabilities b := by
    funext q k
    rw [coordinateReadout,eqb]
    norm_num [FractionalRationalRotation.probabilities,Complex.normSq_ratCast,pow_two]
  refine ⟨w,transformed_valid valid U,fun r c k => ⟨b (r,c) k,eqb (r,c) k⟩,?_,out ▸ inside⟩
  intro q k
  rw [out]
  apply sq_pos_of_ne_zero
  exact_mod_cast nz q k

/-- A strictly positive rational real coordinate measurement lies beyond all
classical convex mixtures, in every nontrivial Sudoku size. -/
theorem positive_coordinate_nonclassical (N : ℕ) (hN : 2≤N) :
    ∃ v : Grid (Fin N), Valid v ∧ RationalEntries v ∧
      (∀ q k,0<coordinateReadout v q k) ∧ coordinateReadout v∉convexHull ℝ {p | Classical p} := by
  let : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  obtain ⟨v,hv,hr,out⟩ := coordinate_nonclassical N hN
  exact rational_full_perturbation v hv hr _ classical_hull_closed.isOpen_compl out

#print axioms positive_coordinate_nonclassical
end FractionalBlockBell

