import Mathlib

/-! Exact determinant averages for diagonal sign completions of real symmetric
conference matrices. Each sign is selected independently in the column
expansion; the final polynomial records all fixed sign counts. -/

open scoped BigOperators Matrix
open Finset Matrix

namespace Hadamard.ConferenceAverage

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An independently weighted choice in each column commutes with the determinant. -/
theorem determinant_column_choices {B R : Type*} [Fintype B] [CommRing R]
    (A : B → Matrix I I R) (w : I → B → R) :
    (∑ f : I → B, (∏ j, w j (f j)) * (Matrix.of (fun i j ↦ A (f j) i j)).det) =
    (Matrix.of (fun i j ↦ ∑ b, w j b * A b i j)).det := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib]
  ring

def signValue {R : Type*} [Ring R] (b : Bool) : R := if b then 1 else -1

/-- The scalar variable gives a weight of `z` to each positive sign and a
weight of one to each negative sign. This identity works over any commutative ring. -/
theorem signed_generating {R : Type*} [CommRing R] (C : Matrix I I R) (z : R) :
    (∑ f : I → Bool, (∏ i, if f i then z else 1) *
      (C + diagonal (fun i ↦ signValue (f i))).det) =
      ((1+z) • C + (z-1) • (1 : Matrix I I R)).det := by
  classical
  let A (b : Bool) := C + (signValue b : R) • (1 : Matrix I I R)
  let w (_ : I) (b : Bool) : R := if b then z else 1
  have selected (f : I → Bool) : Matrix.of (fun i j ↦ A (f j) i j) =
      C + diagonal (fun i ↦ signValue (f i)) := by
    ext i j
    by_cases ij : i=j <;> simp [A, ij, Matrix.one_apply]
  have total : Matrix.of (fun i j ↦ ∑ b, w j b * A b i j) =
      (1+z) • C + (z-1) • (1 : Matrix I I R) := by
    ext i j
    by_cases ij : i=j <;> simp [A, w, signValue, ij, Matrix.one_apply] <;> ring
  simpa only [selected, total, w] using determinant_column_choices A w

/-- A traceless symmetric matrix whose square is a positive scalar has an
equal number of positive and negative eigenvalues. -/
theorem pencil_determinant (C : Matrix I I ℝ) (v : ℕ) (q a b : ℝ)
    (card : Fintype.card I = 2*v) (hq : 0 < q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix I I ℝ)) (trace : C.trace=0) :
    (a • C + b • (1 : Matrix I I ℝ)).det = (b^2-q*a^2)^v := by
  classical
  let s := Real.sqrt q
  let e := hc.eigenvalues
  let u := hc.eigenvectorUnitary
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) u
  let D := diagonal e
  have hd : C = α D := hc.spectral_theorem
  have ss : s^2=q := Real.sq_sqrt hq.le
  have sp : 0<s := Real.sqrt_pos.mpr hq
  have ds : D*D=q • (1 : Matrix I I ℝ) := by
    apply α.injective
    change α (D*D) = α (q • (1 : Matrix I I ℝ))
    rw [map_mul α, map_smul α, map_one α, ←hd, square]
  have sqe (i : I) : e i ^ 2 = s ^ 2 := by
    have h := congrArg (fun M : Matrix I I ℝ ↦ M i i) ds
    rw [ss, pow_two]
    simpa [D, Matrix.diagonal_mul_diagonal] using h
  have val (i : I) : e i = if e i=s then s else -s := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (sqe i) with h|h <;> simp [h]
  let P := Finset.univ.filter (fun i : I ↦ e i = s)
  let N := Finset.univ.filter (fun i : I ↦ ¬e i = s)
  have sumCard : P.card+N.card=2*v := by
    simpa [P,N,card] using (Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i : I ↦ e i=s))
  have zeros : (P.card:ℝ)*s+(N.card:ℝ)*(-s)=0 := by
    have h : (∑ i, e i)=0 := hc.trace_eq_sum_eigenvalues.symm.trans trace
    calc
      _ = ∑ i, if e i=s then s else -s := by simp [Finset.sum_ite, P, N]
      _ = _ := (Finset.sum_congr rfl (fun i _ ↦ (val i).symm)).trans h
  have same : P.card=N.card := by
    have h : (P.card:ℝ)=(N.card:ℝ) := by
      apply (mul_right_cancel₀ sp.ne')
      linarith
    exact_mod_cast h
  have pc : P.card=v := by omega
  have nc : N.card=v := by omega
  have detp : (a • C + b • (1 : Matrix I I ℝ)).det = ∏ i, (a*e i+b) := by
    calc
      _ = (α (a • D + b • (1 : Matrix I I ℝ))).det := by
        rw [map_add,map_smul,map_smul,map_one,←hd]
      _ = (a • D + b • (1 : Matrix I I ℝ)).det := det_units_conj (Unitary.toUnits u) _
      _ = _ := by simp [D, Matrix.smul_one_eq_diagonal, Matrix.diagonal_add, ← Matrix.diagonal_smul]
  rw [detp]
  calc
    _ = ∏ i, (if e i=s then a*s+b else a*(-s)+b) := by
      apply Finset.prod_congr rfl
      intro i _
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (sqe i) with h|h <;> simp [h, show -s≠s by linarith]
    _ = (a*s+b)^v*(a*(-s)+b)^v := by
      simpa [Finset.prod_ite, P, N] using congrArg₂ (·*·)
        (congrArg (fun k : ℕ ↦ (a*s+b)^k) pc)
        (congrArg (fun k : ℕ ↦ (a*(-s)+b)^k) nc)
    _ = _ := by rw [←mul_pow, ←ss]; ring

private theorem dot_gram_scalar (A : Matrix I I ℝ) {r : ℝ}
    (gram : A.transpose*A = r • (1 : Matrix I I ℝ)) (x : I → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = r * (x ⬝ᵥ x) := by
  calc
    _ = (x ᵥ* A.transpose) ⬝ᵥ (A *ᵥ x) := by rw [vecMul_transpose]
    _ = x ⬝ᵥ (A.transpose *ᵥ (A *ᵥ x)) := (dotProduct_mulVec _ _ _).symm
    _ = _ := by rw [mulVec_mulVec, gram]; simp [Matrix.smul_mulVec, dotProduct_smul]

private theorem nonsingular_segment (C : Matrix I I ℝ) (q : ℝ) (hq : 1<q)
    (hc : C.transpose=C) (square : C*C=q • (1 : Matrix I I ℝ))
    (f : I → Bool) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (C+t • diagonal (fun i ↦ signValue (f i))).det ≠ 0 := by
  let D : Matrix I I ℝ := diagonal (fun i ↦ signValue (f i))
  have orth : D.transpose*D=1 := by
    have one (i : I) : (signValue (f i) : ℝ) * signValue (f i) = 1 := by cases f i <;> simp [signValue]
    simp [D, diagonal_mul_diagonal, one]
  have scaled : (t • D).transpose*(t • D) = t^2 • (1 : Matrix I I ℝ) := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, orth, smul_smul, sq]
  intro hz
  obtain ⟨x,hx,ker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have kill : C *ᵥ x = -((t • D) *ᵥ x) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [D, add_mulVec] using ker
  have eqn := congrArg (fun y : I → ℝ ↦ y ⬝ᵥ y) kill
  change (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = (-((t • D) *ᵥ x)) ⬝ᵥ (-((t • D) *ᵥ x)) at eqn
  rw [neg_dotProduct, dotProduct_neg, neg_neg, dot_gram_scalar C (by rw [hc, square]),
    dot_gram_scalar (t • D) scaled] at eqn
  have s : q=t^2 := mul_right_cancel₀ (dotProduct_self_eq_zero.not.mpr hx) eqn
  have bounded := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  nlinarith [ht.2]

/-- Along the path from the zero diagonal to any sign diagonal the determinant
keeps the sign of the original conference matrix. -/
theorem absolute_completion (C : Matrix I I ℝ) (v : ℕ) (q : ℝ)
    (card : Fintype.card I=2*v) (hq : 1<q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix I I ℝ)) (trace : C.trace=0) (f : I → Bool) :
    |(C+diagonal (fun i ↦ signValue (f i))).det| =
      (-1:ℝ)^v * (C+diagonal (fun i ↦ signValue (f i))).det := by
  let D : Matrix I I ℝ := diagonal (fun i ↦ signValue (f i))
  let F (t : ℝ) := (-1:ℝ)^v * (C+t • D).det
  have qpos : 0<q := by linarith
  have cd : C.det=(-q)^v := by
    simpa using pencil_determinant C v q 1 0 card qpos hc square trace
  have fzero : 0<F 0 := by
    simp only [F, zero_smul, add_zero, cd, ←mul_pow]
    simpa using pow_pos qpos v
  have cont : Continuous F := by unfold F; fun_prop
  have tr : C.transpose=C := by ext i j; simpa using hc.apply i j
  have good : 0≤F 1 := by
    by_contra! h
    obtain ⟨t,ht,htzero⟩ := intermediate_value_Icc' zero_le_one cont.continuousOn
      (show (0:ℝ)∈Set.Icc (F 1) (F 0) from ⟨h.le, fzero.le⟩)
    have ne := nonsingular_segment C q hq tr square f ht
    exact (mul_ne_zero (pow_ne_zero v (by norm_num : (-1:ℝ) ≠ 0)) ne) htzero
  have h : 0 ≤ (-1:ℝ)^v*(C+D).det := by simpa [F] using good
  calc
    _ = |(-1:ℝ)^v*(C+D).det| := by simp [abs_mul, abs_pow, D]
    _ = _ := abs_of_nonneg h

/-- The coefficient of degree k is the sum of absolute determinants over all
diagonals with exactly k positive signs. The right side depends only on q and v. -/
theorem absolute_generating (C : Matrix I I ℝ) (v : ℕ) (q z : ℝ)
    (card : Fintype.card I=2*v) (hq : 1<q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix I I ℝ)) (trace : C.trace=0) :
    (∑ f : I → Bool, z^(Finset.univ.filter (fun i ↦ f i = true)).card *
      |(C+diagonal (fun i ↦ signValue (f i))).det|) =
      ((q-1)*(1+z)^2+4*z)^v := by
  classical
  have weight (f : I → Bool) :
      (∏ i, if f i then z else 1) = z^(Finset.univ.filter (fun i ↦ f i = true)).card := by
    simp [Finset.prod_ite]
  calc
    _ = (-1:ℝ)^v * ∑ f : I → Bool, (∏ i, if f i then z else 1) *
        (C+diagonal (fun i ↦ signValue (f i))).det := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      rw [weight, absolute_completion C v q card hq hc square trace]
      ring
    _ = _ := by
      rw [signed_generating, pencil_determinant C v q (1+z) (z-1) card (by linarith) hc square trace, ← mul_pow]
      congr 1
      ring

#print axioms signed_generating
#print axioms absolute_generating
#print axioms pencil_determinant

end Hadamard.ConferenceAverage
