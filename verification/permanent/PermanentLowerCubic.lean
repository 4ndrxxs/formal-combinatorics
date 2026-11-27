import PermanentThreeRowsRigid

/-! Cubic complementary permanents in the lower Hessian block. Expanding in
the third row expresses every entry as a linear form whose coefficients depend
only on the first two rows. A Hessian of rank at most five forces every
three-by-three minor of that block to vanish. -/
noncomputable section
open Matrix Module Equiv Finset QuinticPencil
namespace PermanentFive

/-- Coefficients of third-row entries in the Hessian pairing of rows three and four. -/
def thirdWeight {R : Type*} [CommRing R] (z : Cell → R) (j k l : Idx) : R :=
  ∑ p : Perm Idx, if (p k = 4 ∧ j ≠ k ∧ p j = 3) ∧ l ≠ j ∧ l ≠ k ∧ p l = 2
    then ∏ h ∈ ((univ.erase k).erase j).erase l, z (p h,h) else 0

theorem expand_lower_block {R : Type*} [CommRing R] (z : Cell → R) (j k : Idx) :
    secondAt z (3,j) (4,k) = ∑ l, thirdWeight z j k l * z (2,l) := by
  simp only [secondAt,thirdWeight,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases a : p k = 4 ∧ j ≠ k ∧ p j = 3
  · let l := p.symm 2
    have b : p l = 2 := p.apply_symm_apply _
    have lj : l ≠ j := fun eq ↦ (by decide : (2 : Idx) ≠ 3) ((b.symm.trans (congrArg p eq)).trans a.2.2)
    have lk : l ≠ k := fun eq ↦ (by decide : (2 : Idx) ≠ 4) ((b.symm.trans (congrArg p eq)).trans a.1)
    rw [Finset.sum_eq_single l]
    · rw [ite_eq_left a,ite_eq_left ⟨a,lj,lk,b⟩,← b,mul_comm]
      exact (Finset.mul_prod_erase ((univ.erase k).erase j) (fun h ↦ z (p h,h))
        (Finset.mem_erase.mpr ⟨lj,Finset.mem_erase.mpr ⟨lk,Finset.mem_univ _⟩⟩)).symm
    · intro h _ ne
      have nh : p h ≠ 2 := fun eq ↦ ne (p.injective (eq.trans b.symm))
      simp [nh]
    · simp
  · simp [a]

theorem thirdWeight_top {R : Type*} [CommRing R] (w z : Cell → R)
    (same : ∀ i j : Idx, i.val < 2 → w (i,j) = z (i,j)) (j k l : Idx) :
    thirdWeight w j k l = thirdWeight z j k l := by
  unfold thirdWeight
  apply Finset.sum_congr rfl
  intro p _
  by_cases e : (p k = 4 ∧ j ≠ k ∧ p j = 3) ∧ l ≠ j ∧ l ≠ k ∧ p l = 2
  · simp only [ite_eq_left e]
    apply Finset.prod_congr rfl
    intro h hh
    obtain ⟨hl,h₁⟩ := Finset.mem_erase.mp hh
    obtain ⟨hj,h₂⟩ := Finset.mem_erase.mp h₁
    have hk := (Finset.mem_erase.mp h₂).1
    have a : p h ≠ 2 := fun eq ↦ hl (p.injective (eq.trans e.2.2.2.symm))
    have b : p h ≠ 3 := fun eq ↦ hj (p.injective (eq.trans e.1.2.2.symm))
    have c : p h ≠ 4 := fun eq ↦ hk (p.injective (eq.trans e.1.1.symm))
    apply same
    generalize p h = i at *
    fin_cases i <;> first | decide | contradiction
  · simp [e]

theorem thirdWeight_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : Cell → R)
    (j k l : Idx) : thirdWeight (f ∘ z) j k l = f (thirdWeight z j k l) := by
  simp [thirdWeight,apply_ite f]

private theorem within_row {R : Type*} [CommRing R] (z : Cell → R) (r j k : Idx) :
    secondAt z (r,j) (r,k) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  intro h
  exact h.2.1 (p.injective (h.2.2.trans h.1.symm))

/-- A nonzero three-by-three minor would give a nonsingular six-by-six
Hessian minor by interchanging the two column blocks. -/
theorem lower_three_minors {K : Type*} [Field K] (z : Cell → K)
    (rank : (hessian (per K Idx) z).rank ≤ 5) (rows cols : Fin 3 → Idx) :
    (Matrix.of (fun a b ↦ secondAt z (3,rows a) (4,cols b))).det = 0 := by
  let H := hessian (per K Idx) z
  let A : Matrix (Fin 3) (Fin 3) K := Matrix.of fun a b ↦ secondAt z (3,rows a) (4,cols b)
  let up (a : Fin 3) : Cell := (3,rows a)
  let dn (a : Fin 3) : Cell := (4,cols a)
  have sym (u v : Cell) : H u v = H v u := by
    change MvPolynomial.eval z (MvPolynomial.pderiv u (MvPolynomial.pderiv v _)) = _
    rw [MvPolynomial.pderiv_comm]
    rfl
  have eq : H.submatrix (Sum.elim up dn) (Sum.elim dn up) = Matrix.fromBlocks A 0 0 A.transpose := by
    ext i j
    cases i with
    | inl a =>
      cases j with
      | inl b => exact second_formula z _ _
      | inr b => exact (second_formula z _ _).trans (within_row z 3 _ _)
    | inr a =>
      cases j with
      | inl b => exact (second_formula z _ _).trans (within_row z 4 _ _)
      | inr b => exact (sym _ _).trans (second_formula z _ _)
  by_contra bad
  have nz : (H.submatrix (Sum.elim up dn) (Sum.elim dn up)).det ≠ 0 := by
    rw [eq,Matrix.det_fromBlocks_zero₂₁,Matrix.det_transpose]
    exact mul_ne_zero bad bad
  have full := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz))
  have le := Matrix.rank_submatrix_le H (Sum.elim up dn) (Sum.elim dn up)
  rw [full] at le
  change 6 ≤ (hessian (per K Idx) z).rank at le
  omega

#print axioms expand_lower_block
#print axioms lower_three_minors
end PermanentFive
