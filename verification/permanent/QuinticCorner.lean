import QuinticKernel

/-! Removing the top left linear form by homogeneity. -/

noncomputable section
open PowerSeries Matrix
namespace QuinticPencil

variable {R ι σ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype σ]

theorem split_corner (a : R) (B : Matrix Unit ι R) (C' : Matrix ι Unit R) (T : Matrix ι ι R) :
    (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) ↦ a) B C' T).det =
      a * T.det + (Matrix.fromBlocks (0 : Matrix Unit Unit R) B C' T).det := by
  let i : Unit ⊕ ι := Sum.inl ()
  let A := Matrix.fromBlocks (0 : Matrix Unit Unit R) B C' T
  let E := Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) ↦ a) (0 : Matrix Unit ι R) C' T
  have orig : Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) ↦ a) B C' T =
      A.updateRow i (E i + A i) := by
    ext u v
    cases u with
    | inl u => cases u; cases v <;> simp [A,E,i,Matrix.fromBlocks,Matrix.updateRow, Function.update]
    | inr u => cases v <;> simp [A,E,i,Matrix.fromBlocks,Matrix.updateRow, Function.update]
  have first : A.updateRow i (E i) = E := by
    ext u v
    cases u with
    | inl u => cases u; simp [i,Matrix.updateRow, Function.update]
    | inr u => cases v <;> simp [A,E,i,Matrix.fromBlocks,Matrix.updateRow, Function.update]
  rw [orig, Matrix.det_updateRow_add, first, Matrix.updateRow_eq_self]
  dsimp only [E]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique (n := Unit)]
  rfl

def lowerPoly (D : ι → ι → σ → R) : Matrix ι ι (MvPolynomial σ R) :=
  1 - Matrix.of fun i j ↦ linearForm (D i j)

def cornerDet (l : σ → R) (b c : ι → σ → R) (D : ι → ι → σ → R) : MvPolynomial σ R :=
  (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) ↦ linearForm l)
    (-(Matrix.of fun (_ : Unit) i ↦ linearForm (b i)))
    (Matrix.of fun j (_ : Unit) ↦ linearForm (c j)) (lowerPoly D)).det

private theorem restrict_origin (l v : σ → R) :
    restrictLine 0 v (linearForm l) = X * C (value l v) := by
  simp [restrictLine, linearForm, value, MvPolynomial.coe_eval₂Hom, map_sum, Finset.mul_sum,
    mul_left_comm]

private theorem lower_origin (D : ι → ι → σ → R) (v : σ → R) :
    constantCoeff (restrictLine 0 v (lowerPoly D).det) = 1 := by
  let e := (constantCoeff (R := R)).comp (restrictLine 0 v)
  have entry : e.mapMatrix (lowerPoly D) = 1 := by
    rw [lowerPoly, map_sub, map_one, sub_eq_self]
    ext i j
    simp [e, RingHom.mapMatrix_apply, restrict_origin]
  change e (lowerPoly D).det = 1
  rw [RingHom.map_det, entry, Matrix.det_one]

omit [Fintype σ] in
private theorem homogeneous_origin {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (v : σ → R) :
    restrictLine 0 v p = X^n * C (MvPolynomial.eval v p) := by
  have h := (hp.map (C (R := R))).eval_smul X (C ∘ v)
  rw [MvPolynomial.eval₂_comp]
  simpa [restrictLine, MvPolynomial.eval_map, Pi.smul_def, smul_eq_mul,
    Function.comp_def] using h

/-- A homogeneous polynomial of degree at least two represented by a pencil
with scalar linear corner has the very same representation with zero corner. -/
theorem remove_corner {l : σ → R} {b c : ι → σ → R} {D : ι → ι → σ → R}
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous (n+2))
    (rep : p = cornerDet l b c D) : p = regularDet b c D := by
  have split : p = linearForm l * (lowerPoly D).det + regularDet b c D :=
    rep.trans (split_corner _ _ _ _)
  have val (v : σ → R) : value l v = 0 := by
    have h := congrArg (fun q ↦ coeff 1 (restrictLine 0 v q)) split
    have hz (w : σ → R) : value w 0 = 0 := by simp [value]
    have dvd := square_dvd_line b c D rfl 0 v (fun i ↦ hz _) (fun i ↦ hz _)
    have sq := X_pow_dvd_iff.mp dvd 1 (by decide)
    have hp0 : coeff 1 (restrictLine 0 v p) = 0 := by
      apply (X_pow_dvd_iff (n := 2)).mp _ 1 (by decide)
      rw [homogeneous_origin hp, pow_add, mul_comm (X^n), mul_assoc]
      exact dvd_mul_right _ _
    change coeff 1 (restrictLine 0 v p) = coeff 1 (restrictLine 0 v
      (linearForm l * (lowerPoly D).det + regularDet b c D)) at h
    rw [hp0, map_add, map_add, sq, add_zero, map_mul, restrict_origin, mul_assoc,
      show 1 = 0+1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_mul, constantCoeff_C, lower_origin, mul_one] at h
    exact h.symm
  classical
  have zero (i : σ) : l i = 0 := by simpa [value, Pi.single_apply, mul_ite] using val (Pi.single i 1)
  simpa [linearForm,zero] using split

#print axioms remove_corner
end QuinticPencil
