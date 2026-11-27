import QuinticPencil
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Trunc

/-! The mixed second derivative of a homogeneous form on a formal line. -/

noncomputable section
open PowerSeries
namespace QuinticPencil

variable {R S σ : Type*} [CommRing R] [CommRing S]

/-- Embed the coefficient ring as constants in both direction variables. -/
def embed (R : Type*) [CommRing R] : R →+* MixedSeries R :=
  (C (R := R⟦X⟧)).comp (C (R := R))

def directions (z u v : R) : MixedSeries R := embed R z + edge u v

/-- Evaluate a polynomial at the base point plus two formal directions. -/
def atPoint (p : MvPolynomial σ R) (z u v : σ → R) : MixedSeries R :=
  MvPolynomial.eval₂Hom (embed R) (fun i ↦ directions (z i) (u i) (v i)) p

def liftCoeffs (f : R →+* S) : MixedSeries R →+* MixedSeries S :=
  PowerSeries.map (PowerSeries.map f)

def scaleDirections (a : R) : MixedSeries R →+* MixedSeries R :=
  (PowerSeries.rescale (C a)).comp (PowerSeries.map (PowerSeries.rescale a))

private lemma rescale_const (a b : R) : PowerSeries.rescale a (C b) = C b := by
  ext n
  cases n <;> simp [coeff_rescale, coeff_C]

private lemma scale_embed (a b : R) : scaleDirections a (embed R b) = embed R b := by
  simp [scaleDirections, embed, rescale_const]

private lemma scale_directions (a z u v : R) :
    scaleDirections a (directions (a*z) u v) = embed R a * directions z u v := by
  simp [directions, embed, edge, scaleDirections, rescale_const, PowerSeries.rescale_X]
  ring

private lemma mixed_scale (a : R) (v : MixedSeries R) :
    mixed R (scaleDirections a v) = a^2 * mixed R v := by
  change coeff 1 (coeff 1 ((rescale (C a)) (PowerSeries.map (rescale a) v))) =
    a^2 * coeff 1 (coeff 1 v)
  simp only [coeff_rescale, pow_one, coeff_C_mul, coeff_map]
  ring

private lemma mixed_embed_mul (a : R) (v : MixedSeries R) :
    mixed R (embed R a * v) = a * mixed R v := by
  change coeff 1 (coeff 1 (C (C a) * v)) = a * coeff 1 (coeff 1 v)
  simp [coeff_C_mul]

private lemma mixed_lift (f : R →+* S) (v : MixedSeries R) :
    mixed S (liftCoeffs f v) = f (mixed R v) := by
  change coeff 1 (coeff 1 (PowerSeries.map (PowerSeries.map f) v)) = f (coeff 1 (coeff 1 v))
  simp [coeff_map]

theorem atPoint_map (f : R →+* S) (p : MvPolynomial σ R) (z u v : σ → R) :
    atPoint (MvPolynomial.map f p) (f ∘ z) (f ∘ u) (f ∘ v) =
      liftCoeffs f (atPoint p z u v) := by
  unfold atPoint
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  apply MvPolynomial.eval₂Hom_congr _ _ rfl
  · ext x
    simp [liftCoeffs, embed]
  · funext i
    simp [liftCoeffs, directions, embed, edge]

/-- Scaling the base point and extracting the mixed coefficient reduces the
degree by two, over an arbitrary commutative ring. -/
theorem scaled_mixed {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d)
    (z u v : σ → R) (a : R) :
    a^2 * mixed R (atPoint p (fun i ↦ a*z i) u v) =
      a^d * mixed R (atPoint p z u v) := by
  have h : scaleDirections a (atPoint p (fun i ↦ a*z i) u v) =
      embed R (a^d) * atPoint p z u v := by
    unfold atPoint
    rw [MvPolynomial.map_eval₂Hom]
    have comp : (scaleDirections a).comp (embed R) = embed R := by
      apply RingHom.ext
      intro r
      exact scale_embed a r
    rw [comp]
    simpa only [scale_directions, MvPolynomial.coe_eval₂Hom, Pi.smul_def, smul_eq_mul] using
      hp.eval₂_smul (embed R) a (fun i ↦ directions (z i) (u i) (v i))
  simpa only [mixed_scale, mixed_embed_mul] using congrArg (mixed R) h

/-- On the line through the origin and the base point, the full series of
mixed derivatives of a form of degree d+2 is a single monomial of degree d. -/
theorem homogeneous_line {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous (d+2))
    (z u v : σ → R) :
    mixed R⟦X⟧ (atPoint (MvPolynomial.map C p) (fun i ↦ X * C (z i)) (C ∘ u) (C ∘ v)) =
      monomial d (mixed R (atPoint p z u v)) := by
  apply X_pow_mul_cancel (k := 2)
  have h := scaled_mixed (hp.map (C (R := R))) (C ∘ z) (C ∘ u) (C ∘ v) X
  rw [atPoint_map, mixed_lift] at h
  rw [show (fun i ↦ X * C (z i)) = (fun i ↦ X * (C ∘ z) i) from rfl, h]
  rw [monomial_eq_C_mul_X_pow, pow_add]
  ring

#print axioms scaled_mixed
#print axioms homogeneous_line

end QuinticPencil
