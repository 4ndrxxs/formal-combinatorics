module
public import Quantum.FractionalPuzzleQuotient
public import Quantum.SudokuMeasurements

/-! The diagonal unitary group fixes all computational clue rays. A single
two-coordinate cell yields a circle's worth of distinct projective solutions. -/
@[expose] public section
noncomputable section
namespace SudokuContinuum
open Function QuantumSudoku Measurements PartialSudoku SudokuEmbedding FractionalLayouts

variable {n : ℕ} [NeZero n]

def rotate (a : Sites n) (z : Circle) (v : Grid (Fin n)) : Grid (Fin n) :=
  fun r c => phaseAt a z (v r c)

theorem rotate_valid (a : Sites n) (z : Circle) {v : Grid (Fin n)} (h : Valid v) :
    Valid (rotate a z v) := by
  have gram (d : Direction) (k i j : Sites n) :
      inner ℂ (line d (rotate a z v) k i) (line d (rotate a z v) k j)=if i=j then 1 else 0 := by
    exact (phase_gram a z _ _).trans (valid_gram h d k i j)
  exact ⟨fun r => basis_of_gram _ (gram .row r),fun c => basis_of_gram _ (gram .column c),
    fun x y => basis_of_gram _ (gram .block (x,y))⟩

theorem rotate_axis (a k : Sites n) (z t : Circle) :
    phaseAt a z ((t:ℂ) • unitAxis k) = ((if a=k then z*t else t : Circle):ℂ) • unitAxis k := by
  ext j
  by_cases ha : j=a <;> by_cases hk : j=k <;> by_cases eq : a=k <;>
    simp_all [phaseAt,unitAxis,PiLp.single_apply]

theorem rotate_completes (a : Sites n) (z : Circle) {p : Puzzle n} {v : Grid (Fin n)}
    (h : QuantumCompletes p v) : QuantumCompletes p (rotate a z v) := by
  refine ⟨rotate_valid a z h.1,?_⟩
  intro r c k printed
  obtain ⟨t,ht⟩:=h.2 r c k printed
  refine ⟨if a=k then z*t else t,?_⟩
  change phaseAt a z (v r c)=_
  rw [ht,rotate_axis]

theorem phase_identified {r c a b : Sites n} {v : Grid (Fin n)} (hab : a≠b)
    (ha : v r c a≠0) (hb : v r c b≠0) {z w : Circle}
    (eq : SameRays (rotate a z v) (rotate a w v)) : z=w := by
  obtain ⟨t,ht⟩:=eq r c
  have fixed := congrArg (fun k : H (Fin n) => k b) ht
  change (if b=a then (z:ℂ)*v r c b else v r c b)=
    (t:ℂ)*(if b=a then (w:ℂ)*v r c b else v r c b) at fixed
  simp only [if_neg hab.symm] at fixed
  have one : (t:ℂ)=1 := mul_right_cancel₀ hb (fixed.symm.trans (one_mul _).symm)
  have moving := congrArg (fun k : H (Fin n) => k a) ht
  change (if a=a then (z:ℂ)*v r c a else v r c a)=
    (t:ℂ)*(if a=a then (w:ℂ)*v r c a else v r c a) at moving
  simp only [if_true,one,one_mul] at moving
  exact Circle.ext (mul_right_cancel₀ ha moving)

def circleEmbedding {p : Puzzle n} {v : Grid (Fin n)} (h : QuantumCompletes p v)
    {r c a b : Sites n} (hab : a≠b) (ha : v r c a≠0) (hb : v r c b≠0) :
    Circle ↪ QSolutions p where
  toFun z := Quotient.mk _ ⟨rotate a z v,rotate_completes a z h⟩
  inj' := fun _ _ eq => phase_identified hab ha hb (Quotient.exact eq)

#print axioms circleEmbedding
end SudokuContinuum
