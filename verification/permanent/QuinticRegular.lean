import QuinticCorner
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Normalization of an arbitrary affine matrix pencil of corank one at
the origin. Coordinate and basis changes are over the ground field. -/

noncomputable section
open Matrix Module
namespace QuinticPencil

variable {K n h σ : Type*} [Field K] [Fintype n] [DecidableEq n]
  [Fintype h] [DecidableEq h] [Fintype σ]

/-- An arbitrary matrix whose entries are affine linear polynomials. -/
def affineMatrix (A : Matrix n n K) (F : σ → Matrix n n K) : Matrix n n (MvPolynomial σ K) :=
  MvPolynomial.C.mapMatrix A + ∑ s, (MvPolynomial.X s : MvPolynomial σ K) •
    MvPolynomial.C.mapMatrix (F s)

private lemma affine_apply (A : Matrix n n K) (F : σ → Matrix n n K) (i j : n) :
    affineMatrix A F i j = MvPolynomial.C (A i j) + linearForm (fun s ↦ F s i j) := by
  simp [affineMatrix, linearForm, Matrix.sum_apply, mul_comm]

private lemma affine_change (A V U : Matrix n n K) (F : σ → Matrix n n K) :
    MvPolynomial.C.mapMatrix V * affineMatrix A F * MvPolynomial.C.mapMatrix U =
      affineMatrix (V*A*U) (fun s ↦ V*F s*U) := by
  simp [affineMatrix, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]

private lemma affine_submatrix (e : h ≃ n) (A : Matrix n n K) (F : σ → Matrix n n K) :
    (affineMatrix A F).submatrix e e =
      affineMatrix (A.submatrix e e) (fun s ↦ (F s).submatrix e e) := by
  ext i j
  simp [affine_apply]

private def normalConstant (K h : Type*) [Field K] [DecidableEq h] :
    Matrix (Unit ⊕ h) (Unit ⊕ h) K :=
  Matrix.fromBlocks (0 : Matrix Unit Unit K) 0 0 1

theorem normal_bases (A : Matrix n n K) (regular : Fintype.card n = A.rank+1) :
    ∃ (V U : Matrix n n K) (e : (Unit ⊕ Fin A.rank) ≃ n),
      IsUnit V ∧ IsUnit U ∧ (V*A*U).submatrix e e = normalConstant K (Fin A.rank) := by
  classical
  obtain ⟨V,U,q,hV,hU,red⟩ := Matrix.exists_rank_normal_form A
  let g : Unit ≃ Fin (Fintype.card n - A.rank) := Fintype.equivOfCardEq (by simp [regular])
  let swap := (g.sumCongr (Equiv.refl (Fin A.rank))).trans (Equiv.sumComm _ _)
  let e := swap.trans q.symm
  refine ⟨V,U,e,hV,hU,?_⟩
  rw [red]
  ext i j
  cases i <;> cases j <;> simp [e,swap,normalConstant,Matrix.fromBlocks,Matrix.submatrix]

private lemma linear_neg (x : σ → K) : linearForm (fun i ↦ -x i) = -linearForm x := by
  simp [linearForm, Finset.sum_neg_distrib]

private theorem read_blocks (F : σ → Matrix (Unit ⊕ h) (Unit ⊕ h) K) :
    ∃ (l : σ → K) (b c : h → σ → K) (D : h → h → σ → K),
      (affineMatrix (normalConstant K h) F).det = cornerDet l b c D := by
  refine ⟨fun s ↦ F s (.inl ()) (.inl ()),fun i s ↦ -F s (.inl ()) (.inr i),
    fun j s ↦ F s (.inr j) (.inl ()),fun i j s ↦ -F s (.inr i) (.inr j),?_⟩
  unfold cornerDet
  congr 1
  ext i j
  cases i <;> cases j <;> simp [affine_apply, normalConstant, Matrix.fromBlocks,
    lowerPoly, linear_neg, Matrix.one_apply]

private theorem scale_top (a : K) (b c : h → σ → K) (D : h → h → σ → K) :
    regularDet (fun i s ↦ a * b i s) c D = MvPolynomial.C a * regularDet b c D := by
  let s : Unit ⊕ h → MvPolynomial σ K := Sum.elim (fun _ ↦ MvPolynomial.C a) (fun _ ↦ 1)
  let A := Matrix.fromBlocks (0 : Matrix Unit Unit (MvPolynomial σ K))
    (-(Matrix.of fun (_ : Unit) i ↦ linearForm (b i)))
    (Matrix.of fun j (_ : Unit) ↦ linearForm (c j)) (lowerPoly D)
  have eq : regularDet (fun i s ↦ a * b i s) c D =
      (Matrix.of fun i j ↦ s i * A i j).det := by
    unfold regularDet
    congr 1
    ext i j
    cases i <;> cases j <;> simp [s,A,lowerPoly, Matrix.fromBlocks, linearForm,
      Finset.mul_sum, mul_assoc]
  rw [eq, Matrix.det_mul_column]
  simp [s,A,Fintype.prod_sum_type,regularDet,lowerPoly]

/-- Any regular affine determinantal representation of a homogeneous form
of degree at least two gives an equality with a normalized pencil of the
same size. The lower block has the rank of the original constant matrix. -/
theorem normalize_regular (A : Matrix n n K) (F : σ → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) {p : MvPolynomial σ K} {d : ℕ}
    (rep : p = (affineMatrix A F).det) (hp : p.IsHomogeneous (d+2)) :
    ∃ (b c : Fin A.rank → σ → K) (D : Fin A.rank → Fin A.rank → σ → K),
      p = regularDet b c D := by
  obtain ⟨V,U,e,hV,hU,normal⟩ := normal_bases A regular
  let G := fun s ↦ (V * F s * U).submatrix e e
  let a := V.det * U.det
  have nz : a ≠ 0 := mul_ne_zero ((Matrix.isUnit_iff_isUnit_det V).mp hV).ne_zero
    ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  have eq : (affineMatrix (normalConstant K (Fin A.rank)) G).det = MvPolynomial.C a * p := by
    rw [← normal, ← affine_submatrix, ← affine_change, Matrix.det_submatrix_equiv_self,
      Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det, rep]
    simp [a, mul_left_comm, mul_comm]
  obtain ⟨l,b,c,D,corner⟩ := read_blocks G
  have homog : (MvPolynomial.C a * p).IsHomogeneous (d+2) := by
    simpa only [zero_add] using (MvPolynomial.isHomogeneous_C σ a).mul hp
  have normalized := remove_corner homog (eq.symm.trans corner)
  refine ⟨fun i s ↦ a⁻¹ * b i s,c,D,?_⟩
  rw [scale_top, ← normalized, ← mul_assoc, ← map_mul, inv_mul_cancel₀ nz, map_one, one_mul]

/-- A regular affine pencil of size m representing a homogeneous quintic has
one common singular subspace on which m-1 bounds codimension plus Hessian rank. -/
theorem regular_quintic_kernel (A : Matrix n n K) (F : σ → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) {p : MvPolynomial σ K}
    (rep : p = (affineMatrix A F).det) (hp : p.IsHomogeneous 5) :
    ∃ L : Submodule K (σ → K), ∀ z ∈ L,
      (∀ v, (PowerSeries.X : PowerSeries K)^2 ∣ restrictLine z v p) ∧
      ∃ H : LinearMap.BilinForm K (σ → K),
        (∀ u v, H u v = mixed K (atPoint p z u v)) ∧
        Fintype.card σ + finrank K H.range + 1 ≤ Fintype.card n + finrank K L := by
  obtain ⟨b,c,D,hn⟩ := normalize_regular A F regular rep (d := 3) hp
  obtain ⟨L,hL⟩ := quintic_kernel hp b c D hn
  refine ⟨L,fun z hz ↦ ?_⟩
  obtain ⟨hs,H,hH,hr⟩ := hL z hz
  refine ⟨hs,H,hH,?_⟩
  rw [Fintype.card_fin] at hr
  omega

#print axioms normalize_regular
#print axioms regular_quintic_kernel
end QuinticPencil
