import PermanentLineSpace
import PermanentSymmetry
import PermanentWitnesses
import QuinticDirectional
import QuinticNormalized

/-! At size twenty-one, a five-dimensional endpoint kernel must be supported
on an actual row or column. The argument applies the second directional
derivative at complementary three-edge matchings before taking any limit. -/

noncomputable section
open Matrix Equiv MvPolynomial QuinticPencil Module
namespace PermanentFive
variable {K : Type*} [Field K] [CharZero K]

private def fourTerms (R : Type*) [CommRing R] : Matrix Cell Cell R :=
  Matrix.single (3,3) (4,4) 1 + Matrix.single (4,4) (3,3) 1 +
  Matrix.single (3,4) (4,3) 1 + Matrix.single (4,3) (3,4) 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
private theorem fourTerms_integer : ∀ a b : Cell, secondAt (matchPoint 3) a b = fourTerms ℤ a b := by
  rintro ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

omit [CharZero K] in
private theorem single_pair (a b : Cell) (v : Cell → K) :
    (Matrix.single a b (1 : K)).toBilin' v v = v a * v b := by
  simp [Matrix.toBilin'_apply,Matrix.single_apply,ite_and,mul_ite,ite_mul]

omit [CharZero K] in
private theorem canonical_pair (v : Cell → K) :
    (hessian (per K Idx) ((Int.castRingHom K) ∘ matchPoint 3)).toBilin' v v =
      2*(v (3,3)*v (4,4)+v (3,4)*v (4,3)) := by
  have eq : hessian (per K Idx) ((Int.castRingHom K) ∘ matchPoint 3) = fourTerms K := by
    ext a b
    rw [second_formula,second_map,fourTerms_integer]
    simp [fourTerms,Matrix.single_apply]
  rw [eq]
  simp only [fourTerms,map_add,LinearMap.add_apply,single_pair]
  ring

private def movePair (r s : Idx) : Perm Idx :=
  (Equiv.swap 3 r).trans (Equiv.swap ((Equiv.swap 3 r) 4) s)
private theorem movePair_ok : ∀ r s : Idx, r ≠ s → movePair r s 3 = r ∧ movePair r s 4 = s :=
  by decide +kernel

private def evenDir (v : Cell → K) : Prop :=
  ∀ (y : Cell → K) (t : K), MvPolynomial.eval (y+t•v) (per K Idx) +
    MvPolynomial.eval (y-t•v) (per K Idx) = 2 * MvPolynomial.eval y (per K Idx)

omit [CharZero K] in
private theorem even_relabel (r c : Perm Idx) (v : Cell → K) (h : evenDir v) :
    evenDir (v ∘ (r.prodCongr c)) := by
  let e := r.prodCongr c
  have ev (x : Cell → K) : MvPolynomial.eval (x ∘ e) (per K Idx) = MvPolynomial.eval x (per K Idx) := by
    rw [← MvPolynomial.eval_rename]
    rw [show rename e (per K Idx) = _ from row_column_rename r c]
  intro y t
  let y' := y ∘ e.symm
  have he : y' ∘ e = y := by ext i; simp [y']
  have plus : (y' + t•v) ∘ e = y + t•(v ∘ e) := by ext i; simp [y',Function.comp_apply]
  have minus : (y' - t•v) ∘ e = y - t•(v ∘ e) := by ext i; simp [y',Function.comp_apply]
  change MvPolynomial.eval (y+t•(v ∘ e)) _ + MvPolynomial.eval (y-t•(v ∘ e)) _ = _
  rw [← plus,← minus,ev,ev,h y' t,← ev y',he]

private theorem two_zero_of_even (v : Cell → K) (h : evenDir v) : AllTwoZero v := by
  intro r s i j rs ij
  let R := movePair r s
  let C := movePair i j
  let w := v ∘ (R.prodCongr C)
  have hw := even_relabel R C v h
  let y := (Int.castRingHom K) ∘ matchPoint 3
  have ha := hessian_zero_of_even (per K Idx) y w (hw y)
  rw [canonical_pair] at ha
  have zero := (mul_eq_zero.mp ha).resolve_left (by norm_num)
  have rr := movePair_ok r s rs
  have cc := movePair_ok i j ij
  simpa [w,R,C,rr.1,rr.2,cc.1,cc.2] using zero

theorem saturated_kernel_on_line {n : Type*} [Fintype n] [DecidableEq n]
    (b c : n → Cell → K) (D : n → n → Cell → K) (rep : per K Idx = regularDet b c D)
    (saturated : finrank K (endpoints b c).range = Fintype.card n)
    (large : 5 ≤ finrank K (endpoints b c).ker) :
    (∃ r : Idx, ∀ z ∈ (endpoints b c).ker, ∀ j : Cell, j.1 ≠ r → z j = 0) ∨
    (∃ c' : Idx, ∀ z ∈ (endpoints b c).ker, ∀ j : Cell, j.2 ≠ c' → z j = 0) := by
  apply large_space_on_one_line _ large
  intro z hz
  apply two_zero_of_even
  intro y t
  exact normalized_even_difference (per_homogeneous K Idx) b c D rep saturated (t•z)
    ((endpoints b c).ker.smul_mem t hz) y

#print axioms saturated_kernel_on_line
end PermanentFive
