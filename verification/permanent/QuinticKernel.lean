import QuinticRank

/-! The common endpoint kernel consists of double zeros of the polynomial.
This argument also applies when the lower right block is singular at the
point of evaluation. -/

noncomputable section
open PowerSeries Matrix Module
namespace QuinticPencil

variable {R ι σ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype σ]

/-- Restriction of a multivariate polynomial to z+t v. -/
def restrictLine (z v : σ → R) : MvPolynomial σ R →+* R⟦X⟧ :=
  MvPolynomial.eval₂Hom C (fun i ↦ C (z i) + X * C (v i))

private theorem restrict_linear (l z v : σ → R) :
    restrictLine z v (linearForm l) = C (value l z) + X * C (value l v) := by
  simp [restrictLine, linearForm, value, MvPolynomial.coe_eval₂Hom, map_sum, Finset.mul_sum,
    Finset.sum_add_distrib, mul_add, mul_left_comm]

/-- Every determinant term uses both endpoints of the zero corner. -/
theorem scale_border (a : R) (B : Matrix Unit ι R) (C' : Matrix ι Unit R) (T : Matrix ι ι R) :
    (Matrix.fromBlocks (0 : Matrix Unit Unit R) (a • B) (a • C') T).det =
      a^2 * (Matrix.fromBlocks 0 B C' T).det := by
  let s : Unit ⊕ ι → R := Sum.elim (fun _ ↦ a) (fun _ ↦ 1)
  let A := Matrix.fromBlocks (0 : Matrix Unit Unit R) B C' T
  have eq : Matrix.fromBlocks (0 : Matrix Unit Unit R) (a • B) (a • C') T =
      Matrix.of (fun i j ↦ s i * (Matrix.of (fun i j ↦ s j * A i j)) i j) := by
    ext i j
    cases i <;> cases j <;> simp [A,s,Matrix.fromBlocks]
  rw [eq, Matrix.det_mul_column, Matrix.det_mul_row]
  simp [s, A, Fintype.prod_sum_type, pow_two, mul_assoc]

theorem square_dvd_line {p : MvPolynomial σ R}
    (b c : ι → σ → R) (D : ι → ι → σ → R) (rep : p = regularDet b c D)
    (z v : σ → R) (hb : ∀ i, value (b i) z = 0) (hc : ∀ i, value (c i) z = 0) :
    (X : R⟦X⟧)^2 ∣ restrictLine z v p := by
  let B : Matrix Unit ι R⟦X⟧ := -(Matrix.of fun _ i ↦ C (value (b i) v))
  let C' : Matrix ι Unit R⟦X⟧ := Matrix.of fun i _ ↦ C (value (c i) v)
  let T : Matrix ι ι R⟦X⟧ := 1 - Matrix.of fun i j ↦ restrictLine z v (linearForm (D i j))
  refine ⟨(Matrix.fromBlocks 0 B C' T).det,?_⟩
  rw [rep, regularDet, RingHom.map_det, ← scale_border X B C' T]
  congr 1
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, RingHom.mapMatrix_apply, B, C', T, Matrix.one_apply, restrict_linear,
      hb, hc]

variable {K : Type*} [Field K]

/-- A normalized quintic determinant admits one fixed subspace consisting of
singular points with the stated Hessian-rank bound everywhere. Singularity
is expressed by a double zero on every affine line through the point. -/
theorem quintic_kernel {p : MvPolynomial σ K} (hp : p.IsHomogeneous 5)
    (b c : ι → σ → K) (D : ι → ι → σ → K) (rep : p = regularDet b c D) :
    ∃ L : Submodule K (σ → K), ∀ z ∈ L,
      (∀ v, (X : K⟦X⟧)^2 ∣ restrictLine z v p) ∧
      ∃ H : LinearMap.BilinForm K (σ → K),
        (∀ u v, H u v = mixed K (atPoint p z u v)) ∧
        Fintype.card σ + finrank K H.range ≤ Fintype.card ι + finrank K L := by
  refine ⟨(endpoints b c).ker,?_⟩
  intro z hz
  refine ⟨?_,quintic_rank hp b c D rep z hz⟩
  intro v
  apply square_dvd_line b c D rep z v
  · have hz' : dotProductEquiv K ι ((Matrix.of b).mulVecLin z) = 0 :=
      congrArg Prod.fst (show endpoints b c z = 0 from hz)
    intro i
    exact congrFun ((dotProductEquiv K ι).map_eq_zero_iff.mp hz') i
  · intro i
    exact congrFun (congrArg Prod.snd (show endpoints b c z = 0 from hz)) i

#print axioms square_dvd_line
#print axioms quintic_kernel

end QuinticPencil
