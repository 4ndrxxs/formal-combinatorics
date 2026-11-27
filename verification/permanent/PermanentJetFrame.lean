import PermanentWitnesses
import PermanentSymmetry
import QuinticFirstJet

/-! The form in a moving polynomial frame and a simple-zero obstruction
on twelve cells. The finite obstruction is expressed over dual numbers,
so its meaning is independent of the choice of a polynomial lift. -/

noncomputable section
open Matrix Module Polynomial Equiv QuinticPencil
namespace PermanentFive
variable {R B J : Type*} [CommRing R] [CommRing B]

def frameHessian (y : Cell → R) (u : J → Cell → R) : Matrix J J R :=
  Matrix.of fun i j ↦ (Matrix.of (secondAt y)).toBilin' (u i) (u j)

theorem frameHessian_map [Fintype J] [DecidableEq J] (f : R →+* B) (y : Cell → R) (u : J → Cell → R) :
    f.mapMatrix (frameHessian y u) = frameHessian (f ∘ y) (fun i ↦ f ∘ u i) := by
  ext i j
  change f ((Matrix.of (secondAt y)).toBilin' (u i) (u j)) =
    (Matrix.of (secondAt (f ∘ y))).toBilin' (f ∘ u i) (f ∘ u j)
  simp [Matrix.toBilin'_apply,second_map]

theorem frameHessian_units (y : Cell → R) (v : J → Cell) :
    frameHessian y (fun i ↦ Pi.single (v i) 1) =
      (QuinticPencil.hessian (per R Idx) y).submatrix v v := by
  ext i j
  change (Matrix.of (secondAt y)).toBilin' (Pi.single (v i) 1) (Pi.single (v j) 1) =
    QuinticPencil.hessian (per R Idx) y (v i) (v j)
  rw [Matrix.toBilin'_single,second_formula]
  rfl

theorem frameHessian_pairing (y : Cell → R) (u : J → Cell → R) (i j : J) :
    frameHessian y u i j = (QuinticPencil.hessian (per R Idx) y).toBilin' (u i) (u j) := by
  have eq : Matrix.of (secondAt y) = QuinticPencil.hessian (per R Idx) y := by
    ext a b
    exact (second_formula y a b).symm
  change (Matrix.of (secondAt y)).toBilin' _ _ = _
  rw [eq]

def HasOddBlock (K : Type*) [Field K] (S : Finset Cell) : Prop :=
  ∃ (v : Fin 12 → Cell) (y : Cell → DualNumber K),
    (∀ i ∈ S, ∃ j, v j = i) ∧
    (((hessian (per (DualNumber K) Idx) y).submatrix v v).det).fst = 0 ∧
    (((hessian (per (DualNumber K) Idx) y).submatrix v v).det).snd ≠ 0

variable {K : Type*} [Field K]
theorem HasOddBlock.mono {S T : Finset Cell} (witness : HasOddBlock K T)
    (sub : S ⊆ T) : HasOddBlock K S := by
  obtain ⟨v,y,inside,zero,slope⟩ := witness
  exact ⟨v,y,fun i hi ↦ inside i (sub hi),zero,slope⟩

theorem HasOddBlock.relabel {S T : Finset Cell} (witness : HasOddBlock K T)
    (e : Perm Cell) (sym : MvPolynomial.rename e (per (DualNumber K) Idx) = per (DualNumber K) Idx)
    (sub : ∀ i ∈ S, e.symm i ∈ T) : HasOddBlock K S := by
  obtain ⟨v,y,inside,zero,slope⟩ := witness
  let p := per (DualNumber K) Idx
  have ev (a : MvPolynomial Cell (DualNumber K)) :
      MvPolynomial.eval (y ∘ e.symm) (MvPolynomial.rename e a) = MvPolynomial.eval y a := by
    rw [MvPolynomial.eval_rename]
    simp [Function.comp_assoc]
  have he : (hessian p (y ∘ e.symm)).submatrix e e = hessian p y := by
    ext1 i j
    have h := MvPolynomial.pderiv_rename e.injective j p
    rw [show MvPolynomial.rename e p = p from sym] at h
    simp only [hessian,Matrix.submatrix_apply,Matrix.of_apply,h,
      MvPolynomial.pderiv_rename e.injective,ev]
  refine ⟨e ∘ v,y ∘ e.symm,?_,?_⟩
  · intro i hi
    obtain ⟨j,eq⟩ := inside _ (sub i hi)
    exact ⟨j,by simp [eq]⟩
  · change (((hessian p (y ∘ e.symm)).submatrix (e ∘ v) (e ∘ v)).det).fst = 0 ∧ _
    rw [← Matrix.submatrix_submatrix,he]
    exact ⟨zero,slope⟩

def liftJet (a : DualNumber K) : K[X] := Polynomial.C a.fst + X * Polynomial.C a.snd

theorem firstJet_lift (a : DualNumber K) : firstJet K (liftJet a) = a := by
  apply TrivSqZeroExt.ext <;> simp [liftJet,firstJet]

end PermanentFive
