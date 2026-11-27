import QuinticDerivatives
import PermanentDegeneration

/-! Diagonal symmetries preserve singularity and Hessian rank. The rank
condition persists under the polynomial specialization to a coordinate plane. -/

noncomputable section
open Matrix Module MvPolynomial
namespace QuinticPencil

variable {K I n : Type*} [Field K] [DecidableEq I] [Fintype I] [DecidableEq n] [Fintype n]

/-- Substitute a scalar multiple of each variable into a polynomial. -/
def twist (v : I → K) : MvPolynomial I K →+* MvPolynomial I K :=
  MvPolynomial.eval₂Hom C (fun i ↦ C (v i) * X i)

omit [Fintype I] in
private theorem deriv_twist (v : I → K) (i : I) (p : MvPolynomial I K) :
    pderiv i (twist v p) = C (v i) * twist v (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [twist,MvPolynomial.coe_eval₂Hom]
  | add a b ha hb => simp [map_add,ha,hb,mul_add]
  | mul_X a j ha =>
    simp only [map_mul, pderiv_mul, ha, map_add]
    by_cases h : j = i
    · subst j
      simp [twist,MvPolynomial.coe_eval₂Hom]
      ring
    · simp [twist,MvPolynomial.coe_eval₂Hom,pderiv_X_of_ne h]
      ring

omit [Fintype I] [DecidableEq I] in
private theorem eval_twist (v z : I → K) (p : MvPolynomial I K) :
    MvPolynomial.eval z (twist v p) = MvPolynomial.eval (fun i ↦ v i * z i) p := by
  unfold twist
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr _ _ rfl
  · apply RingHom.ext; intro x; simp
  · simp

omit [Fintype I] in
private theorem scaled_first {p : MvPolynomial I K} {v : I → K} {a : K}
    (sym : twist v p = C a * p) (z : I → K) (i : I) :
    v i * MvPolynomial.eval (fun j ↦ v j * z j) (pderiv i p) =
      a * MvPolynomial.eval z (pderiv i p) := by
  have h := congrArg (pderiv i) sym
  rw [deriv_twist,pderiv_C_mul] at h
  simpa only [map_mul, MvPolynomial.eval_C,eval_twist] using congrArg (MvPolynomial.eval z) h

omit [Fintype I] in
private theorem scaled_second {p : MvPolynomial I K} {v : I → K} {a : K}
    (sym : twist v p = C a * p) (z : I → K) (i j : I) :
    v i * v j * hessian p (fun k ↦ v k*z k) i j = a * hessian p z i j := by
  have h := congrArg (pderiv j) sym
  rw [deriv_twist,pderiv_C_mul] at h
  have h' := congrArg (pderiv i) h
  rw [pderiv_C_mul,pderiv_C_mul,deriv_twist] at h'
  have h'' := congrArg (MvPolynomial.eval z) h'
  simpa [hessian,map_mul,eval_twist,mul_assoc,mul_left_comm,mul_comm] using h''

private theorem scaled_rank_le {p : MvPolynomial I K} {v : I → K} {a : K}
    (sym : twist v p = C a * p) (nv : ∀ i, v i ≠ 0) (z : I → K) :
    (hessian p (fun j ↦ v j*z j)).rank ≤ (hessian p z).rank := by
  let L := diagonal (fun i ↦ a / v i)
  let U := diagonal (fun i ↦ (v i)⁻¹)
  have eq : hessian p (fun j ↦ v j*z j) = L * hessian p z * U := by
    ext i j
    simp only [L,U,Matrix.mul_diagonal,Matrix.diagonal_mul]
    have h := scaled_second sym z i j
    field_simp [nv]
    linear_combination h
  rw [eq]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

omit [DecidableEq I] [Fintype I] in
/-- A matrix of multivariate polynomials cannot gain rank at a point where
every polynomial equation of a set still vanishes. A rank normal form
selects a determinant that would detect any proposed rank increase. -/
theorem rank_specialization (A : Matrix n n (MvPolynomial I K)) (S : Set (I → K)) (z : I → K)
    (spec : ∀ q : MvPolynomial I K, (∀ x ∈ S, MvPolynomial.eval x q = 0) →
      MvPolynomial.eval z q = 0) (r : ℕ)
    (small : ∀ x ∈ S, ((MvPolynomial.eval x).mapMatrix A).rank ≤ r) :
    ((MvPolynomial.eval z).mapMatrix A).rank ≤ r := by
  classical
  let H := (MvPolynomial.eval z).mapMatrix A
  by_contra! large
  obtain ⟨V,U,e,_,_,red⟩ := Matrix.exists_rank_normal_form H
  let f : Fin H.rank → n := fun i ↦ e.symm (.inl i)
  let q := ((MvPolynomial.C.mapMatrix V * A * MvPolynomial.C.mapMatrix U).submatrix f f).det
  have eval_q (x : I → K) : MvPolynomial.eval x q =
      ((V * (MvPolynomial.eval x).mapMatrix A * U).submatrix f f).det := by
    dsimp only [q]
    have const (B : Matrix n n K) : (MvPolynomial.eval x).mapMatrix (MvPolynomial.C.mapMatrix B) = B := by
      ext i j
      simp
    rw [RingHom.map_det_submatrix]
    change (((MvPolynomial.eval x).mapMatrix (MvPolynomial.C.mapMatrix V * A *
      MvPolynomial.C.mapMatrix U)).submatrix f f).det = _
    rw [map_mul, map_mul, const, const]
  have van (x) (hx : x ∈ S) : MvPolynomial.eval x q = 0 := by
    rw [eval_q]
    by_contra nz
    have full := Matrix.rank_of_det_ne_zero nz
    have lo := Matrix.rank_submatrix_le (V * (MvPolynomial.eval x).mapMatrix A * U) f f
    have upper := ((rank_mul_le_left (V * (MvPolynomial.eval x).mapMatrix A) U).trans
      (rank_mul_le_right V ((MvPolynomial.eval x).mapMatrix A))).trans (small x hx)
    rw [full,Fintype.card_fin] at lo
    exact (not_le_of_gt large) (lo.trans upper)
  have one : (V * H * U).submatrix f f = 1 := by
    rw [red]
    ext i j
    simp [f,Matrix.submatrix,Matrix.fromBlocks]
  have h := spec q van
  rw [eval_q] at h
  change ((V * H * U).submatrix f f).det = 0 at h
  simp [one] at h

private def hessianPoly (p : MvPolynomial I K) : Matrix I I (MvPolynomial I K) :=
  Matrix.of fun i j ↦ pderiv i (pderiv j p)

private theorem eval_hessian (p : MvPolynomial I K) (z : I → K) :
    (MvPolynomial.eval z).mapMatrix (hessianPoly p) = hessian p z := rfl

/-- Every invariant homogeneous quintic with a regular affine determinant
has a coordinate singular plane satisfying the Hessian inequality, provided
the diagonal weights are distinct. -/
theorem coordinate_kernel [Infinite K] (A : Matrix n n K) (F : I → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) {p : MvPolynomial I K}
    (rep : p = (affineMatrix A F).det) (hp : p.IsHomogeneous 5)
    (w : I → ℕ) (injective : Function.Injective w)
    (sym : ∀ t : K, t ≠ 0 → ∃ a : K, twist (fun i ↦ t^(w i)) p = C a * p) :
    ∃ S : Finset I, ∀ z : I → K, (∀ j ∉ S, z j = 0) →
      (∀ i, MvPolynomial.eval z (pderiv i p) = 0) ∧
      Fintype.card I + (hessian p z).rank + 1 ≤ Fintype.card n + S.card := by
  obtain ⟨L,prop⟩ := regular_partial_kernel A F regular rep hp
  obtain ⟨S,card,special⟩ := PermanentDegeneration.coordinate_specialization L w injective
  refine ⟨S,fun z hz ↦ ?_⟩
  let orbit : Set (I → K) := {y | ∃ x ∈ L, ∃ t : K, t ≠ 0 ∧ y = fun j ↦ t^(w j)*x j}
  have spec (q : MvPolynomial I K) (h : ∀ x ∈ orbit, MvPolynomial.eval x q = 0) :
      MvPolynomial.eval z q = 0 :=
    special q (fun x hx t nt ↦ h _ ⟨x,hx,t,nt,rfl⟩) z hz
  constructor
  · intro i
    apply spec
    rintro _ ⟨x,hx,t,nt,rfl⟩
    obtain ⟨a,eq⟩ := sym t nt
    have h := scaled_first eq x i
    rw [(prop x hx).1 i,mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ nt)
  · let r := Fintype.card n + finrank K L - (Fintype.card I + 1)
    have small (x) (hx : x ∈ orbit) : ((MvPolynomial.eval x).mapMatrix (hessianPoly p)).rank ≤ r := by
      obtain ⟨y,hy,t,nt,rfl⟩ := hx
      obtain ⟨a,eq⟩ := sym t nt
      rw [eval_hessian]
      apply (scaled_rank_le eq (fun j ↦ pow_ne_zero _ nt) y).trans
      have b := (prop y hy).2
      dsimp only [r]
      omega
    have b := rank_specialization (hessianPoly p) orbit z spec r small
    rw [eval_hessian] at b
    have base := (prop 0 L.zero_mem).2
    dsimp only [r] at b
    rw [card]
    omega

#print axioms rank_specialization
#print axioms coordinate_kernel
end QuinticPencil
