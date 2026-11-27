import PermanentSymmetry
import PermanentWitnesses
import QuinticRestrictedTorus

/-! Principal restrictions lose at most two ranks per deleted coordinate.
Integral inverse certificates yield nonsingular Hessian blocks over any
field of characteristic zero. -/

noncomputable section
open Matrix MvPolynomial Module Equiv
namespace PermanentFive
open QuinticPencil
variable {K : Type*} [Field K]

/-- Two applications of Sylvester's rank inequality to the coordinate
projection and its transpose. -/
theorem principal_dimension_bound {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (H : Matrix A A K) (f : B → A) (inj : Function.Injective f) :
    H.rank + 2 * Fintype.card B ≤ (H.submatrix f f).rank + 2 * Fintype.card A := by
  let E := (1 : Matrix A A K).submatrix f id
  let P := (1 : Matrix A A K).submatrix id f
  have left (M : Matrix A A K) : E * M = M.submatrix f id :=
    Matrix.one_submatrix_mul f (Equiv.refl A) M
  have right (M : Matrix B A K) : M * P = M.submatrix id f :=
    Matrix.mul_submatrix_one (Equiv.refl A) f M
  have eye : E * P = 1 := by
    rw [right]
    exact Matrix.submatrix_one f inj
  have eRank := Matrix.rank_mul_le_left E P
  have pRank := Matrix.rank_mul_le_right E P
  rw [eye,Matrix.rank_one] at eRank pRank
  have first := Matrix.rank_mul_ge E H
  have second := Matrix.rank_mul_ge (E*H) P
  have block : E * H * P = H.submatrix f f := by rw [right,left]; rfl
  rw [block] at second
  omega

theorem det_ne_zero_of_inverse_certificate {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℤ) (d : ℤ) (nz : d ≠ 0) (cert : A*B = d • (1 : Matrix n n ℤ)) :
    A.det ≠ 0 := by
  have e := congrArg Matrix.det cert
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one] at e
  intro zero
  rw [zero,zero_mul] at e
  exact (pow_ne_zero _ nz) e.symm

/-- The support lies inside thirteen coordinate directions on which a
Hessian at some centre is nonsingular. -/
def HasThirteenBlock (K : Type*) [Field K] (S : Finset Cell) : Prop :=
  ∃ (v : Fin 13 → Cell) (y : Cell → K),
    (∀ i ∈ S, ∃ j, v j = i) ∧ ((hessian (per K Idx) y).submatrix v v).rank = 13

theorem HasThirteenBlock.mono {S T : Finset Cell} (witness : HasThirteenBlock K T)
    (sub : S ⊆ T) : HasThirteenBlock K S := by
  obtain ⟨v,y,inside,full⟩ := witness
  exact ⟨v,y,fun i hi ↦ inside i (sub hi),full⟩

theorem hessian_relabel {p : MvPolynomial Cell K} (e : Perm Cell)
    (sym : rename e p = p) (y : Cell → K) :
    (hessian p (y ∘ e.symm)).submatrix e e = hessian p y := by
  have ev (b : MvPolynomial Cell K) : MvPolynomial.eval (y ∘ e.symm) (rename e b) =
      MvPolynomial.eval y b := by
    rw [MvPolynomial.eval_rename]
    simp [Function.comp_assoc]
  ext i j
  have h := MvPolynomial.pderiv_rename e.injective j p
  rw [sym] at h
  simp only [hessian,Matrix.submatrix_apply,Matrix.of_apply,h,
    MvPolynomial.pderiv_rename e.injective,ev]

theorem HasThirteenBlock.relabel {S T : Finset Cell} (witness : HasThirteenBlock K T)
    (e : Perm Cell) (sym : rename e (per K Idx) = per K Idx)
    (sub : ∀ i ∈ S, e.symm i ∈ T) : HasThirteenBlock K S := by
  obtain ⟨v,y,inside,full⟩ := witness
  refine ⟨e ∘ v,y ∘ e.symm,?_,?_⟩
  · intro i hi
    obtain ⟨j,eq⟩ := inside _ (sub i hi)
    exact ⟨j,by simp [eq]⟩
  · rw [← Matrix.submatrix_submatrix,hessian_relabel e sym]
    exact full

theorem HasThirteenBlock.bound {S : Finset Cell} (witness : HasThirteenBlock K S) (m : ℕ)
    (bound : ∀ y : Cell → K,
      ((hessian (per K Idx) y).submatrix ((↑) : S → Cell) ((↑) : S → Cell)).rank + 50 ≤
        2*m + 2*S.card - 2) : 20 ≤ m := by
  classical
  obtain ⟨v,y,inside,full⟩ := witness
  choose f hf using fun i : S ↦ inside i.val i.property
  have inj : Function.Injective f := fun a b h ↦ Subtype.ext ((hf a).symm.trans ((congrArg v h).trans (hf b)))
  let H := hessian (per K Idx) y
  have dims := principal_dimension_bound (H.submatrix v v) f inj
  have eq : (H.submatrix v v).submatrix f f = H.submatrix ((↑) : S → Cell) ((↑) : S → Cell) := by
    ext i j
    simp only [Matrix.submatrix_apply,hf]
  rw [eq,show (H.submatrix v v).rank = 13 from full,Fintype.card_fin,Fintype.card_coe] at dims
  have upper := bound y
  change (H.submatrix ((↑) : S → Cell) ((↑) : S → Cell)).rank + 50 ≤ _ at upper
  omega

/-- Lift a nonsingular integral principal minor to a thirteen-coordinate
block certificate for any characteristic-zero field. -/
theorem block_of_integer [CharZero K] (S : Finset Cell) (v : Fin 13 → Cell)
    (cover : ∀ i ∈ S, ∃ j, v j = i) (y : Cell → ℤ) (A : Matrix (Fin 13) (Fin 13) ℤ)
    (entries : ∀ i j, secondAt y (v i) (v j) = A i j) (nz : A.det ≠ 0) :
    HasThirteenBlock K S := by
  refine ⟨v,(Int.castRingHom K) ∘ y,cover,?_⟩
  have eq : (hessian (per K Idx) ((Int.castRingHom K) ∘ y)).submatrix v v =
      (Int.castRingHom K).mapMatrix A := by
    ext i j
    change hessian _ _ (v i) (v j) = (Int.castRingHom K) (A i j)
    rw [second_formula,second_map,entries]
  rw [eq,Matrix.rank_of_det_ne_zero,Fintype.card_fin]
  rw [← RingHom.map_det]
  change (A.det : K) ≠ 0
  exact_mod_cast nz

#print axioms principal_dimension_bound
#print axioms HasThirteenBlock.bound
#print axioms block_of_integer
end PermanentFive
