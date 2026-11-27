import QuinticHomogeneous

/-! The exact moment identity for a normalized affine determinantal
representation of a homogeneous form. A representation is equality of
multivariate polynomials. No formal-series identity is assumed. -/

noncomputable section
open PowerSeries Matrix
namespace QuinticPencil

variable {R ι σ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype σ]

/-- A coordinate linear form and its value on a vector. -/
def linearForm (l : σ → R) : MvPolynomial σ R :=
  ∑ i, MvPolynomial.C (l i) * MvPolynomial.X i

def value (l z : σ → R) : R := ∑ i, l i * z i

/-- Evaluate the transfer matrix of linear forms at a point. -/
def transfer (D : ι → ι → σ → R) (z : σ → R) : Matrix ι ι R :=
  Matrix.of fun i j ↦ value (D i j) z

/-- Determinant of the regular block pencil with zero linear corner. -/
def regularDet (b c : ι → σ → R) (D : ι → ι → σ → R) : MvPolynomial σ R :=
  (Matrix.fromBlocks (0 : Matrix Unit Unit (MvPolynomial σ R))
    (-(Matrix.of fun (_ : Unit) i ↦ linearForm (b i)))
    (Matrix.of fun j (_ : Unit) ↦ linearForm (c j))
    (1 - Matrix.of fun i j ↦ linearForm (D i j))).det

/-- Substitute the formal line through z and two independent directions. -/
def pathEval (z u v : σ → R) : MvPolynomial σ R →+* MixedSeries R⟦X⟧ :=
  MvPolynomial.eval₂Hom ((embed R⟦X⟧).comp C)
    (fun i ↦ directions (X * C (z i)) (C (u i)) (C (v i)))

private lemma coord_mul (a z u v : R) :
    embed R a * directions z u v = directions (a*z) (a*u) (a*v) := by
  simp [directions, embed, edge]
  ring

private lemma directions_sum (z u v : σ → R) :
    (∑ i, directions (z i) (u i) (v i)) = directions (∑ i, z i) (∑ i, u i) (∑ i, v i) := by
  simp [directions, embed, edge, map_sum, Finset.mul_sum, Finset.sum_add_distrib]

theorem path_linear (l z u v : σ → R) :
    pathEval z u v (linearForm l) =
      directions (X * C (value l z)) (C (value l u)) (C (value l v)) := by
  unfold pathEval linearForm
  rw [map_sum]
  simp only [map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    RingHom.comp_apply, coord_mul, directions_sum]
  congr 1 <;> simp [value, map_sum, Finset.mul_sum, mul_left_comm]

private def perturbed (D : ι → ι → σ → R) (z u v : σ → R) : Matrix ι ι (MixedSeries R⟦X⟧) :=
  1 - Matrix.of fun i j ↦ pathEval z u v (linearForm (D i j))

private lemma perturbed_base (D : ι → ι → σ → R) (z u v : σ → R) :
    (base R⟦X⟧).mapMatrix (perturbed D z u v) = lineBlock (transfer D z) := by
  rw [perturbed, map_sub, map_one, lineBlock]
  congr 1
  ext i j
  simp [path_linear, directions, base, edge, embed, transfer, RingHom.mapMatrix_apply]

private lemma path_det (b c : ι → σ → R) (D : ι → ι → σ → R) (z u v : σ → R)
    (hb : ∀ i, value (b i) z = 0) (hc : ∀ i, value (c i) z = 0) :
    pathEval z u v (regularDet b c D) =
      (border (C ∘ (fun i ↦ value (b i) u)) (C ∘ (fun i ↦ value (b i) v))
        (C ∘ (fun i ↦ value (c i) u)) (C ∘ (fun i ↦ value (c i) v)) (perturbed D z u v)).det := by
  rw [regularDet, RingHom.map_det]
  congr 1
  ext i j
  cases i <;> cases j <;>
    simp [border, perturbed, Matrix.fromBlocks, RingHom.mapMatrix_apply, path_linear,
      directions, hb, hc, Matrix.one_apply]

/-- The scalar determinant prefactor times the full moment series is one
monomial for any homogeneous polynomial represented by a normalized pencil.
The displayed mixed coefficient is taken from the polynomial itself. -/
theorem affine_pencil_series {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous (d+2)) (b c : ι → σ → R) (D : ι → ι → σ → R)
    (rep : p = regularDet b c D) (z u v : σ → R)
    (hb : ∀ i, value (b i) z = 0) (hc : ∀ i, value (c i) z = 0) :
    (lineBlock (transfer D z)).det * PowerSeries.mk (fun j ↦
      ∑ l, ∑ i, ((transfer D z)^j) i l *
        (value (b i) u * value (c l) v + value (b i) v * value (c l) u)) =
      monomial d (mixed R (atPoint p z u v)) := by
  have h := mixed_line (transfer D z) (fun i ↦ value (b i) u) (fun i ↦ value (b i) v)
    (fun i ↦ value (c i) u) (fun i ↦ value (c i) v) (perturbed D z u v) (perturbed_base D z u v)
  rw [← h, ← path_det b c D z u v hb hc, ← rep]
  have eval_eq : pathEval z u v p =
      atPoint (MvPolynomial.map C p) (fun i ↦ X * C (z i)) (C ∘ u) (C ∘ v) :=
    (MvPolynomial.eval₂Hom_map_hom _ _ _ _).symm
  rw [eval_eq]
  exact homogeneous_line hp z u v

#print axioms affine_pencil_series
end QuinticPencil
