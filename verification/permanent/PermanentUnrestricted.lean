import PermanentOrigin
import PermanentLowerBound

/-! Unrestricted affine determinantal complexity of the permanent of order
five. The proof derives regularity from the representation itself. -/
noncomputable section
namespace PermanentFive
open MvPolynomial Matrix Module QuinticPencil DeterminantalRegularity.RankParam
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

private lemma rank_lt_of_det_zero (A : Matrix n n K) (hz : A.det = 0) : A.rank < Fintype.card n := by
  apply lt_of_le_of_ne (Matrix.rank_le_card_width A)
  intro eq
  have full : LinearMap.range A.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq (by
    simpa [Matrix.rank] using eq)
  have sur : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp full
  exact ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_surjective_iff_isUnit.mp sur)).ne_zero hz

/-- Any polynomial matrix whose determinant is the generic permanent of
order five has corank exactly one at the origin in characteristic zero. -/
theorem polynomial_regularity [CharZero K] (P : Matrix n n (MvPolynomial Cell K))
    (rep : per K Idx = P.det) :
    Fintype.card n = ((MvPolynomial.eval 0).mapMatrix P).rank + 1 := by
  let A := (MvPolynomial.eval 0).mapMatrix P
  change Fintype.card n = A.rank + 1
  have zero : A.det = 0 := by
    rw [show A.det = (MvPolynomial.eval 0) P.det from (RingHom.map_det _ _).symm,← rep]
    simp [per,Matrix.permanent,PermanentCuts.generic]
  have lt := rank_lt_of_det_zero A zero
  by_contra ne
  have two : 2 ≤ Fintype.card n - A.rank := by omega
  obtain ⟨V,U,q,hV,hU,red⟩ := Matrix.exists_rank_normal_form A
  let H := Fin A.rank ⊕ Fin (Fintype.card n - A.rank - 2)
  let tail : Fin (Fintype.card n - A.rank - 2) ⊕ Fin 2 ≃ Fin (Fintype.card n - A.rank) :=
    Fintype.equivOfCardEq (by simp; omega)
  let z : Slot H ≃ Fin A.rank ⊕ Fin (Fintype.card n - A.rank) :=
    (Equiv.sumAssoc _ _ _).trans ((Equiv.refl _).sumCongr tail)
  let e := z.trans q.symm
  let T := (MvPolynomial.C.mapMatrix V * P * MvPolynomial.C.mapMatrix U).submatrix e e
  let top : Matrix H (Slot H) K := Matrix.of (fun i j ↦ (V*A*U) (e (.inl i)) (e j))
  have atT (i j : Slot H) : MvPolynomial.eval 0 (T i j) = (V*A*U) (e i) (e j) := by
    simp [T,A,Matrix.submatrix,Matrix.mul_apply]
  have rows (i j : Slot H) : MvPolynomial.eval 0 (T i j) = fullOrigin K H top i j := by
    rw [atT]
    cases i with
    | inl i => rfl
    | inr b =>
      rw [red]
      change (Matrix.fromBlocks 1 0 0 0 : Matrix _ _ K) (q (e (.inr b))) (q (e j)) = 0
      have right : q (e (.inr b)) = Sum.inr (tail (.inr b)) := by
        change q (q.symm (z (.inr b))) = _
        rw [q.apply_symm_apply]
        rfl
      rw [right]
      cases q (e j) <;> rfl
  let c := V.det*U.det
  have hc : c ≠ 0 := mul_ne_zero ((Matrix.isUnit_iff_isUnit_det V).mp hV).ne_zero
    ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  have detT : T.det = C c * per K Idx := by
    change ((MvPolynomial.C.mapMatrix V * P * MvPolynomial.C.mapMatrix U).submatrix e e).det = C c * per K Idx
    rw [Matrix.det_submatrix_equiv_self,Matrix.det_mul,Matrix.det_mul,
      ← RingHom.map_det,← RingHom.map_det,← rep]
    simp [c,mul_left_comm,mul_comm]
  exact no_two_zero_rows K H T top rows c hc detT

/-- Over every characteristic-zero field, every affine determinantal
representation of the generic permanent of order five has size at least 16. -/
theorem determinantal_lower_bound [CharZero K] (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) : 16 ≤ Fintype.card n := by
  have regular := polynomial_regularity (affineMatrix A F) rep
  have eq : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    apply Matrix.ext
    intro i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [eq] at regular
  exact regular_bound A F regular rep

#print axioms polynomial_regularity
#print axioms determinantal_lower_bound
end PermanentFive
