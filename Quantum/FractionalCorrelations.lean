module
public import Quantum.FractionalBinary

/-! A two-qubit algebraic obstruction for identical product-basis probabilities
of two orthogonal measurement states with zero local marginals. -/
@[expose] public section
noncomputable section
namespace FractionalCorrelations
open Complex
open scoped ComplexConjugate

theorem cross_norm (a d A D : ℂ) (h : a*conj d=A*conj D) :
    normSq (conj a*A+conj d*D) =
    normSq a*normSq A+normSq d*normSq D+2*(normSq a*normSq d) := by
  rw [Complex.normSq_add]
  have hh : conj a*A*conj (conj d*D) = ((normSq a*normSq d : ℝ) : ℂ) := by
    rw [map_mul,starRingEnd_self_apply]
    calc
      _ = (conj a*d)*(A*conj D) := by ring
      _ = (a*conj a)*(d*conj d) := by rw [←h]; ring
      _ = _ := by simp [Complex.mul_conj]
  rw [hh]
  simp [Complex.normSq_mul]

theorem shape {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (h1 : a*c=b*d) (h2 : a*b=c*d) :
    (a=d ∧ b=c) ∨ (a=0 ∧ d=0) ∨ (b=0 ∧ c=0) := by
  have h₁ : (a+d)*(b-c)=0 := by linarith only [h1,h2]
  have h₂ : (b+c)*(a-d)=0 := by linarith only [h1,h2]
  rcases mul_eq_zero.mp h₁ with z|z
  · right; left
    constructor <;> linarith
  rcases mul_eq_zero.mp h₂ with y|y
  · right; right
    constructor <;> linarith
  · left; constructor <;> linarith

private theorem corner_weights {a b c d A B C D : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (hD : 0≤D)
    (s : (a=d ∧ b=c) ∨ (a=0 ∧ d=0) ∨ (b=0 ∧ c=0))
    (t : (A=D ∧ B=C) ∨ (A=0 ∧ D=0) ∨ (B=0 ∧ C=0))
    (hu : a*d=A*D) (hv : b*c=B*C)
    (h : a*A+d*D+2*(a*d)=b*B+c*C+2*(b*c)) : a*d=b*c := by
  have h1 := mul_nonneg ha hA
  have h2 := mul_nonneg hb hB
  have h3 := mul_nonneg hc hC
  have h4 := mul_nonneg hd hD
  have h5 := mul_nonneg ha hd
  have h6 := mul_nonneg hb hc
  rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases t with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have eq1 : a=A := by nlinarith [sq_nonneg (a-A)]
    have eq2 : b=B := by nlinarith [sq_nonneg (b-B)]
    subst A; subst B
    linarith
  all_goals nlinarith

/-- In circular coordinates the two local marginal pairs vanish, while equality
of both pairs of planar correlation measurements fixes the two corner products.
Orthogonal states with this data necessarily have equal corner-product modulus. -/
theorem equal_corner_moduli {a b c d A B C D : ℂ}
    (fRow : a*conj c+b*conj d=0) (fCol : a*conj b+c*conj d=0)
    (gRow : A*conj C+B*conj D=0) (gCol : A*conj B+C*conj D=0)
    (hu : a*conj d=A*conj D) (hv : b*conj c=B*conj C)
    (orth : conj a*A+conj b*B+conj c*C+conj d*D=0) :
    normSq (a*conj d)=normSq (b*conj c) := by
  have equation {x y z w : ℂ} (h : x*conj y+z*conj w=0) :
      normSq x*normSq y=normSq z*normSq w := by
    have hh := congrArg Complex.normSq (eq_neg_of_add_eq_zero_left h)
    simpa [Complex.normSq_mul] using hh
  have complete : conj a*A+conj d*D = -(conj b*B+conj c*C) := by linear_combination orth
  have h := congrArg Complex.normSq complete
  rw [cross_norm _ _ _ _ hu,Complex.normSq_neg,cross_norm _ _ _ _ hv] at h
  simp only [Complex.normSq_mul,Complex.normSq_conj]
  apply corner_weights (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (shape (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (equation fRow) (equation fCol))
    (shape (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (equation gRow) (equation gCol))
    _ _ h
  · simpa [Complex.normSq_mul] using congrArg Complex.normSq hu
  · simpa [Complex.normSq_mul] using congrArg Complex.normSq hv

/-- The correlation of two binary planar observables in circular coordinates. -/
def correlation (x y p q : ℂ) : ℝ := 2*(x*(y*p+conj y*q)).re

private theorem complex_eq_of_two_real_parts {x p q : ℂ} (hx : x.im≠0)
    (h : p.re=q.re) (ht : (x*p).re=(x*q).re) : p=q := by
  apply Complex.ext h
  simp only [Complex.mul_re,h] at ht
  exact mul_left_cancel₀ hx (by linarith only [ht] : x.im*p.im=x.im*q.im)

theorem corners_of_correlations {x y p q P Q : ℂ} (hx : x.im≠0) (hy : y.im≠0)
    (h00 : correlation 1 1 p q=correlation 1 1 P Q)
    (h01 : correlation 1 y p q=correlation 1 y P Q)
    (h10 : correlation x 1 p q=correlation x 1 P Q)
    (h11 : correlation x y p q=correlation x y P Q) : p=P ∧ q=Q := by
  have hs : p+q=P+Q := complex_eq_of_two_real_parts hx
    (by simpa [correlation] using h00) (by simpa [correlation] using h10)
  have hr : y*p+conj y*q=y*P+conj y*Q := complex_eq_of_two_real_parts hx
    (by simpa [correlation] using h01) (by simpa [correlation] using h11)
  have nz : y-conj y≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy hi
  have hP : (y-conj y)*(p-P)=0 := by linear_combination hr - conj y * hs
  have he : p=P := sub_eq_zero.mp ((mul_eq_zero.mp hP).resolve_left nz)
  exact ⟨he,add_left_cancel (he ▸ hs)⟩

theorem correlation_determinant (x y p q : ℂ) :
    correlation 1 1 p q * correlation x y p q -
      correlation 1 y p q * correlation x 1 p q =
        4*x.im*y.im*(normSq q-normSq p) := by
  simp [correlation,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

/-- Identical zero-marginal data from orthogonal two-qubit states have a
singular two-by-two matrix of product correlations. The two settings per
factor can be any distinct non-antipodal equatorial axes. -/
theorem singular_of_equal_correlations {x y a b c d A B C D : ℂ}
    (hx : x.im≠0) (hy : y.im≠0)
    (fRow : a*conj c+b*conj d=0) (fCol : a*conj b+c*conj d=0)
    (gRow : A*conj C+B*conj D=0) (gCol : A*conj B+C*conj D=0)
    (orth : conj a*A+conj b*B+conj c*C+conj d*D=0)
    (h : ∀ s ∈ ({1,x} : Set ℂ), ∀ t ∈ ({1,y} : Set ℂ),
      correlation s t (a*conj d) (b*conj c)=correlation s t (A*conj D) (B*conj C)) :
    correlation 1 1 (a*conj d) (b*conj c) * correlation x y (a*conj d) (b*conj c) =
      correlation 1 y (a*conj d) (b*conj c) * correlation x 1 (a*conj d) (b*conj c) := by
  obtain ⟨hu,hv⟩ := corners_of_correlations hx hy
    (h 1 (by simp) 1 (by simp)) (h 1 (by simp) y (by simp))
    (h x (by simp) 1 (by simp)) (h x (by simp) y (by simp))
  have hh := equal_corner_moduli fRow fCol gRow gCol hu hv orth
  apply sub_eq_zero.mp
  rw [correlation_determinant,hh,sub_self,mul_zero]

#print axioms equal_corner_moduli
#print axioms singular_of_equal_correlations
end FractionalCorrelations
