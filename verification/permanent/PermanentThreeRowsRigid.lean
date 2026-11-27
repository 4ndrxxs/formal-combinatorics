import PermanentShapeClassification
import Mathlib.Algebra.Polynomial.Roots

/-! A linear family of singular five-by-five matrices which projects freely
onto three complete rows actually has no entries outside those rows.
The proof follows an arbitrary line in the family, and inverts a matrix
of complementary cubic permanents over the polynomial fraction field. -/

noncomputable section
open Matrix Module Equiv Finset QuinticPencil
namespace PermanentFive
variable {K : Type*} [Field K] [CharZero K]

/-- Laplace expansion of a first partial in a different row. -/
theorem grad_expand_row {R : Type*} [CommRing R] {r s : Idx} (ne : s ≠ r)
    (z : Cell → R) (j : Idx) :
    gradAt z (r,j) = ∑ k, secondAt z (s,k) (r,j) * z (s,k) := by
  simp only [gradAt,secondAt,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases a : p j = r
  · let l := p.symm s
    have b : p l = s := p.apply_symm_apply s
    have lj : l ≠ j := fun eq ↦ ne ((b.symm.trans (congrArg p eq)).trans a)
    rw [Finset.sum_eq_single l]
    · rw [ite_eq_left a,ite_eq_left ⟨a,lj,b⟩]
      rw [← b,mul_comm]
      exact Finset.mul_prod_erase (univ.erase j) (fun k ↦ z (p k,k)) (by simpa using lj)
        |>.symm
    · intro k _ kl
      have nk : p k ≠ s := fun h ↦ kl (p.injective (h.trans b.symm))
      simp [nk]
    · simp
  · simp [a]

private def lowerA (flip : Bool) : Idx := if flip then 4 else 3
private def lowerB (flip : Bool) : Idx := if flip then 3 else 4

private theorem lower_distinct (flip : Bool) : lowerB flip ≠ lowerA flip := by
  cases flip <;> decide

private theorem remaining_top (flip : Bool) (i : Idx)
    (a : i ≠ lowerA flip) (b : i ≠ lowerB flip) : i.val < 3 := by
  cases flip <;> fin_cases i <;> first | decide | contradiction

/-- The lower cross-block of the Hessian uses only the first three rows. -/
private theorem block_uses_top {R : Type*} [CommRing R] (flip : Bool)
    (w z : Cell → R) (same : ∀ i j : Idx, i.val < 3 → w (i,j) = z (i,j)) (k j : Idx) :
    secondAt w (lowerB flip,k) (lowerA flip,j) =
    secondAt z (lowerB flip,k) (lowerA flip,j) := by
  unfold secondAt
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p j = lowerA flip ∧ k ≠ j ∧ p k = lowerB flip
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro l hl
    have lk : l ≠ k := (Finset.mem_erase.mp hl).1
    have lj : l ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    exact same (p l) l (remaining_top flip (p l)
      (fun q ↦ lj (p.injective (q.trans h.1.symm)))
      (fun q ↦ lk (p.injective (q.trans h.2.2.symm))))
  · simp [h]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 12000000 in
private theorem row_block (flip : Bool) (k j : Idx) :
    secondAt rowPoint (lowerB flip,k) (lowerA flip,j) = fiveMinor j k := by
  cases flip <;> fin_cases k <;> fin_cases j <;> decide +kernel

private theorem row_det : fiveMinor.det = 31104 := by decide +kernel

/-- A single member equal to one on the first three rows suffices for the
entire singular family to be supported on them. -/
theorem three_rows_rigid (L : Submodule K (Cell → K))
    (sing : ∀ x ∈ L, ∀ i, gradAt x i = 0) (w : Cell → K) (hw : w ∈ L)
    (ones : ∀ i j : Idx, i.val < 3 → w (i,j) = 1)
    (x : Cell → K) (hx : x ∈ L) (i j : Idx) (outside : 3 ≤ i.val) : x (i,j) = 0 := by
  let v (u : Cell) : Polynomial K := Polynomial.C (w u) + Polynomial.X * Polynomial.C (x u)
  have ev (t : K) : (Polynomial.evalRingHom t) ∘ v = w + t • x := by
    ext q
    simp [v,smul_eq_mul]
    exact mul_comm _ _
  have grad (e : Cell) : gradAt v e = 0 := by
    apply Polynomial.funext
    intro t
    have zero := sing (w+t • x) (L.add_mem hw (L.smul_mem t hx)) e
    have val := grad_map (Polynomial.evalRingHom t) v e
    rw [ev,zero] at val
    simpa using val.symm
  have bottom (flip : Bool) (k : Idx) : x (lowerB flip,k) = 0 := by
    let A : Matrix Idx Idx (Polynomial K) := Matrix.of fun c l ↦
      secondAt v (lowerB flip,l) (lowerA flip,c)
    have mat : (Polynomial.evalRingHom (0 : K)).mapMatrix A = (Int.castRingHom K).mapMatrix fiveMinor := by
      ext c l
      change (Polynomial.evalRingHom (0 : K)) (secondAt v _ _) = (Int.castRingHom K) (fiveMinor c l)
      rw [←second_map,ev,zero_smul,add_zero]
      rw [block_uses_top flip w ((Int.castRingHom K) ∘ rowPoint) (fun i j hi ↦ by
        simp [ones i j hi,rowPoint,hi]), second_map,row_block]
    have nz : A.det ≠ 0 := by
      intro bad
      have zero := congrArg (Polynomial.evalRingHom (0 : K)) bad
      rw [RingHom.map_det,mat,← RingHom.map_det,row_det] at zero
      norm_num at zero
    have vec : A *ᵥ (fun l ↦ v (lowerB flip,l)) = 0 := by
      funext c
      exact (grad_expand_row (lower_distinct flip) v c).symm.trans (grad _)
    have zvec : (fun l ↦ v (lowerB flip,l)) = 0 :=
      Matrix.mulVec_injective_of_det_ne_zero nz (vec.trans (Matrix.mulVec_zero A).symm)
    have zero := congrArg (fun q : Polynomial K ↦ q.coeff 1) (congrFun zvec k)
    simpa [v,Polynomial.coeff_X_mul] using zero
  have either : i = 3 ∨ i = 4 := by fin_cases i <;> first | decide | contradiction
  rcases either with rfl|rfl
  · exact bottom true j
  · exact bottom false j

#print axioms grad_expand_row
#print axioms three_rows_rigid
end PermanentFive
