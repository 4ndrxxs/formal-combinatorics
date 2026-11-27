import PermanentUnrestricted
import QuinticScalarExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Global corank one on the hypersurface implies nilpotence of every
internal transfer in the common endpoint kernel. -/
noncomputable section
open Matrix Module Polynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

omit [CharZero K] in
private theorem padded_rank (A : Matrix n n K) :
    (Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0 A).rank ≤ A.rank := by
  let put : Matrix (Unit ⊕ n) n K := Matrix.of fun u j ↦
    Sum.elim (fun _ ↦ 0) (fun i ↦ (1 : Matrix n n K) i j) u
  have eq : Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0 A = put * A * put.transpose := by
    ext u v
    cases u <;> cases v <;> simp [put,Matrix.mul_apply,Function.swap,Matrix.one_apply]
  rw [eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- At every scalar multiple of an endpoint-kernel input the internal
block is invertible. The condition holds over every characteristic-zero field. -/
theorem endpoint_internal_det_ne_zero (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (z : Cell → K) (hz : z ∈ (endpoints b c).ker) (t : K) :
    (1 - t • transfer D z).det ≠ 0 := by
  let P := Matrix.fromBlocks (0 : Matrix Unit Unit (MvPolynomial Cell K))
    (-(Matrix.of fun (_ : Unit) i ↦ linearForm (b i)))
    (Matrix.of fun j (_ : Unit) ↦ linearForm (c j))
    (1 - Matrix.of fun i j ↦ linearForm (D i j))
  let ev := MvPolynomial.eval (fun j ↦ t*z j)
  have val (l : Cell → K) : ev (linearForm l) = t * value l z := by
    change (MvPolynomial.eval (fun j ↦ t*z j)) (linearForm l) = _
    simp [linearForm,value,Finset.mul_sum,mul_left_comm]
  obtain ⟨hb,hc⟩ := (endpoint_zero_iff b c z).mp hz
  let A := 1 - t • transfer D z
  have eq : ev.mapMatrix P = Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0 A := by
    ext u v
    cases u <;> cases v <;> simp [P,A,RingHom.mapMatrix_apply,Matrix.one_apply,apply_ite,
      Matrix.fromBlocks,val,hb,hc,transfer]
  have rank := polynomial_corank_le_one P rep (fun j ↦ t*z j)
  change Fintype.card (Unit ⊕ n) ≤ (ev.mapMatrix P).rank+1 at rank
  rw [eq,Fintype.card_sum,Fintype.card_unit] at rank
  have lower := padded_rank A
  have full : A.rank = Fintype.card n := (Matrix.rank_le_card_width _).antisymm (by omega)
  have top : LinearMap.range A.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq (by
    simpa [Matrix.rank] using full)
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp top))).ne_zero

omit [CharZero K] in
private theorem charpoly_of_reverse_one (A : Matrix n n K) (h : A.charpolyRev = 1) :
    A.charpoly = Polynomial.X ^ Fintype.card n := by
  ext j
  by_cases le : j ≤ Fintype.card n
  · let k := Fintype.card n-j
    have coeff := congrArg (fun p : K[X] ↦ p.coeff k) (A.reverse_charpoly.trans h)
    change A.charpoly.reverse.coeff k = (1 : K[X]).coeff k at coeff
    rw [Polynomial.coeff_reverse,A.charpoly_natDegree_eq_dim,Polynomial.revAt_le (by dsimp [k]; omega),
      show Fintype.card n-k = j by dsimp [k]; omega] at coeff
    by_cases top : j = Fintype.card n
    · subst j
      simpa [k] using coeff
    · have pos : k ≠ 0 := by dsimp [k]; omega
      simpa only [Polynomial.coeff_one,Polynomial.coeff_X_pow,ite_eq_right pos,ite_eq_right top] using coeff
  · have zero := Polynomial.coeff_eq_zero_of_natDegree_lt (p:=A.charpoly)
        (by rw [A.charpoly_natDegree_eq_dim]; omega : A.charpoly.natDegree < j)
    have ne : Fintype.card n ≠ j := by omega
    simpa [Polynomial.coeff_X_pow,Ne.symm ne] using zero

/-- Every linear combination of internal coefficient matrices along the common
endpoint kernel is nilpotent, for any size of a representation of per_5. -/
theorem endpoint_transfer_nilpotent (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (z : Cell → K) (hz : z ∈ (endpoints b c).ker) :
    IsNilpotent (transfer D z) := by
  let A := transfer D z
  let E := AlgebraicClosure K
  let f := algebraMap K E
  let b' (i : n) := f ∘ b i
  let c' (i : n) := f ∘ c i
  let D' (i j : n) := f ∘ D i j
  have base := congrArg (MvPolynomial.map f) rep
  rw [mapped_permanent,mapped_regular_det] at base
  have hz' : (f ∘ z) ∈ (endpoints b' c').ker := by
    obtain ⟨a,bv⟩ := (endpoint_zero_iff b c z).mp hz
    apply (endpoint_zero_iff _ _ _).mpr
    constructor <;> intro i
    · simpa [b',value,Function.comp_def] using congrArg f (a i)
    · simpa [c',value,Function.comp_def] using congrArg f (bv i)
  have mapA : f.mapMatrix A = transfer D' (f ∘ z) := by
    ext i j
    simp [A,D',transfer,value,Function.comp_def]
  have rev : A.charpolyRev = 1 := by
    by_contra ne
    have deg : A.charpolyRev.degree ≠ 0 := by
      intro d
      have constant := Polynomial.eq_C_of_degree_eq_zero d
      have val := A.eval_charpolyRev
      rw [constant,Polynomial.eval_C] at val
      exact ne (constant.trans (by rw [val,Polynomial.C_1]))
    obtain ⟨t,zero⟩ := IsAlgClosed.exists_eval₂_eq_zero f A.charpolyRev deg
    let e := Polynomial.eval₂RingHom f t
    have mat : e.mapMatrix (1 - (Polynomial.X : K[X]) • A.map Polynomial.C) =
        1-t • f.mapMatrix A := by
      ext i j
      simp [e,Matrix.one_apply,apply_ite,RingHom.mapMatrix_apply]
      exact mul_comm _ _
    have bad : (1-t • transfer D' (f ∘ z)).det = 0 := by
      change e (Matrix.det (1 - (Polynomial.X : K[X]) • A.map Polynomial.C)) = 0 at zero
      rwa [RingHom.map_det,mat,mapA] at zero
    exact endpoint_internal_det_ne_zero b' c' D' base (f ∘ z) hz' t bad
  have cay := Matrix.aeval_self_charpoly A
  rw [charpoly_of_reverse_one A rev,Polynomial.aeval_X_pow] at cay
  exact ⟨Fintype.card n,cay⟩

#print axioms endpoint_internal_det_ne_zero
#print axioms endpoint_transfer_nilpotent
end PermanentFive
