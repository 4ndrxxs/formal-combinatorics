import PermanentTwoRowTemplate

/-! Extending a cubic-minor certificate to an entire linear family. Along
a polynomial line the third row is divisible by the parameter. Dividing
its three-by-three minor by the resulting third power recovers the third
row of the direction at the certified two-row point. -/

noncomputable section
open Matrix Equiv Finset QuinticPencil
namespace PermanentFive

private def lowerUsing {R : Type*} [CommRing R] (z : Cell → R) (d : Idx → R) : Matrix Idx Idx R :=
  Matrix.of fun j k ↦ ∑ l, thirdWeight z j k l * d l

private theorem lower_minor_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : Cell → R) (d : Idx → R) (r c : Fin 3 → Idx) :
    f (((lowerUsing z d).submatrix r c).det) =
      ((lowerUsing (f ∘ z) (f ∘ d)).submatrix r c).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [lowerUsing,Matrix.submatrix,RingHom.mapMatrix_apply,thirdWeight_map]

private theorem lower_using_row {K : Type*} [Field K] (z : Cell → K)
    (rank : (hessian (per K Idx) z).rank ≤ 5) (r c : Fin 3 → Idx) :
    ((lowerUsing z (fun l ↦ z (2,l))).submatrix r c).det = 0 := by
  have eq : (lowerUsing z (fun l ↦ z (2,l))).submatrix r c =
      Matrix.of (fun a b ↦ secondAt z (3,r a) (4,c b)) := by
    ext i j
    exact (expand_lower_block z _ _).symm
  rw [eq]
  exact lower_three_minors z rank r c

private theorem template_at {K : Type*} [Field K] (w : Cell → K)
    (top : ∀ i j : Idx, i.val < 2 → w (i,j) = (twoRowPoint (i,j) : K)) (d : Idx → K) :
    lowerUsing w d = twoRowBlock d := by
  ext j k
  rw [twoRowBlock_sum]
  change (∑ l, thirdWeight w j k l * d l) = _
  apply Finset.sum_congr rfl
  intro l _
  rw [thirdWeight_top w ((Int.castRingHom K) ∘ twoRowPoint) top,thirdWeight_map,twoRowCoeff_correct]
  rfl

private theorem scaled_lower {R : Type*} [CommRing R] (z : Cell → R) (d : Idx → R) (t : R) :
    lowerUsing z (fun l ↦ t*d l) = t • lowerUsing z d := by
  ext j k
  simp [lowerUsing,Finset.mul_sum,mul_left_comm]

attribute [local irreducible] lowerUsing twoRowBlock twoRowPoint thirdWeight

set_option maxHeartbeats 450000 in
private theorem row_two_zero {K : Type*} [Field K] [CharZero K] (w x : Cell → K)
    (top : ∀ i j : Idx, i.val < 2 → w (i,j) = (twoRowPoint (i,j) : K))
    (rank : ∀ t : K, (hessian (per K Idx) (w+t • x)).rank ≤ 5) :
    ∀ j, x (2,j) = 0 := by
  have rank0 : (hessian (per K Idx) w).rank ≤ 5 := by simpa using rank 0
  have zw : ∀ j, w (2,j) = 0 := by
    apply twoRowBlock_rigid
    intro r c
    rw [← template_at w top]
    exact lower_using_row w rank0 r c
  let v (u : Cell) : Polynomial K := Polynomial.C (w u) + Polynomial.X * Polynomial.C (x u)
  let d (j : Idx) := Polynomial.C (x (2,j))
  have ev (t : K) : (Polynomial.evalRingHom t) ∘ v = w+t • x := by
    ext j
    simp [v,smul_eq_mul]
    exact mul_comm _ _
  have row : (fun l ↦ v (2,l)) = fun l ↦ Polynomial.X*d l := by
    funext l
    simp [v,d,zw]
  apply twoRowBlock_rigid
  intro r c
  have zero : ((lowerUsing v (fun l ↦ v (2,l))).submatrix r c).det = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero]
    change Polynomial.evalRingHom t _ = 0
    rw [lower_minor_map,ev]
    have evRow : (Polynomial.evalRingHom t) ∘ (fun l ↦ v (2,l)) =
        fun l ↦ (w+t • x) (2,l) := funext (fun l ↦ congrFun (ev t) (2,l))
    rw [evRow]
    exact lower_using_row _ (rank t) r c
  rw [row,scaled_lower] at zero
  have smul_sub (f : Matrix Idx Idx (Polynomial K)) :
      ((Polynomial.X : Polynomial K) • f).submatrix r c = (Polynomial.X : Polynomial K) • f.submatrix r c := by
    ext a b
    simp only [Matrix.submatrix_apply,Matrix.smul_apply]
  rw [smul_sub] at zero
  rw [Matrix.det_smul] at zero
  have smaller := (mul_eq_zero.mp zero).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  have spec := congrArg (Polynomial.evalRingHom (0 : K)) smaller
  rw [lower_minor_map,ev,zero_smul,add_zero,template_at w top] at spec
  have evD : (Polynomial.evalRingHom (0 : K)) ∘ d = fun l ↦ x (2,l) := by ext; simp [d]
  simpa only [evD,map_zero] using spec

/-- A rank-five Hessian bound along a line forces every direction entry
outside the two certified rows to vanish. -/
theorem two_rows_rank_rigid {K : Type*} [Field K] [CharZero K] (w x : Cell → K)
    (top : ∀ i j : Idx, i.val < 2 → w (i,j) = (twoRowPoint (i,j) : K))
    (rank : ∀ t : K, (hessian (per K Idx) (w+t • x)).rank ≤ 5)
    (i j : Idx) (outside : 2 ≤ i.val) : x (i,j) = 0 := by
  let g := Equiv.swap (2 : Idx) i
  let e := g.prodCongr (Equiv.refl Idx)
  have top' (u k : Idx) (hu : u.val < 2) : (w ∘ e.symm) (u,k) = (twoRowPoint (u,k) : K) := by
    have first : u ≠ 2 := by intro eq; subst u; contradiction
    have second : u ≠ i := by intro eq; subst u; omega
    simpa [e,g,Equiv.swap_apply_of_ne_of_ne first second] using top u k hu
  have rank' (t : K) : (hessian (per K Idx) (w ∘ e.symm + t • (x ∘ e.symm))).rank ≤ 5 := by
    change (hessian (per K Idx) ((w+t • x) ∘ e.symm)).rank ≤ 5
    rw [(transport e (row_column_rename g (Equiv.refl Idx)) _).2]
    exact rank t
  simpa [e,g] using row_two_zero (w ∘ e.symm) (x ∘ e.symm) top' rank' j

#print axioms two_rows_rank_rigid
end PermanentFive
