import DeterminantHessianAction
import PermanentOrderThreeSpectrum

/-! In characteristic two the permanent equals the determinant. Its
smooth zeros have corank one and form one two-sided matrix orbit.
The previously constructed diagonal representative gives Hessian rank
twice the order at every smooth zero of order at least two. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive PermanentBorder QuinticPencil
namespace DeterminantHessian
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem grad_zero_two_rows (z : I × I → K) (a b : I) (ne : a≠b)
    (za : ∀ j, z (a,j)=0) (zb : ∀ j, z (b,j)=0) (e : I × I) : gradAt z e=0 := by
  rw [gradAt]
  apply Finset.sum_eq_zero
  intro p _
  split
  · by_cases h : p.symm a=e.2
    · have hn : p.symm b≠e.2 := fun q ↦ ne (p.symm.injective (h.trans q.symm))
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hn,Finset.mem_univ _⟩)
      simp [zb]
    · apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h,Finset.mem_univ _⟩)
      simp [za]
  · rfl

private theorem nonzero_cofactor {z : I × I → K} (h : cofactor z≠0) :
    ∃ e, eval z (pderiv e (per K I))≠0 := by
  by_contra! all
  apply h
  ext i j
  exact (grad_formula z (i,j)).symm.trans (all _)

theorem binary_corank_one (binary : (2:K)=0) (z : I × I → K) (flat : PermanentBorder.value z=0)
    (smooth : cofactor z≠0) : Fintype.card I=(board z).rank+1 := by
  let A := board z
  have detzero : A.det=0 := by
    rw [PermanentBorder.value,binary_per_eq_det binary,determinant_eval] at flat
    exact flat
  have lt : A.rank<Fintype.card I := by
    apply lt_of_le_of_ne (Matrix.rank_le_card_width A)
    intro top
    have unit := Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr top)
    exact ((Matrix.isUnit_iff_isUnit_det A).mp unit).ne_zero detzero
  by_contra bad
  change Fintype.card I≠A.rank+1 at bad
  have gap : 2≤Fintype.card I-A.rank := by omega
  obtain ⟨V,U,e,hv,hu,red⟩ := Matrix.exists_rank_normal_form A
  have first := nonzero_cofactor smooth
  rw [binary_per_eq_det binary] at first
  obtain ⟨cell,hit⟩ := nonzero_grad_transport V U hv hu z first
  rw [←binary_per_eq_det binary,grad_formula] at hit
  let y := vec (V*(A*U))
  let i : Fin (Fintype.card I-A.rank) := ⟨0,by omega⟩
  let j : Fin (Fintype.card I-A.rank) := ⟨1,by omega⟩
  have neq : e.symm (Sum.inr i)≠e.symm (Sum.inr j) := by
    intro x
    have v : i=j := Sum.inr.inj (e.symm.injective x)
    have := congrArg Fin.val v
    contradiction
  have zr (t : Fin (Fintype.card I-A.rank)) (s : I) : y (e.symm (Sum.inr t),s)=0 := by
    change (V*(A*U)) (e.symm (Sum.inr t)) s=0
    rw [←Matrix.mul_assoc,red]
    simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
    cases e s <;> rfl
  exact hit (grad_zero_two_rows y _ _ neq (zr i) (zr j) cell)

def standard (K : Type*) [Field K] (r t : ℕ) : CellOf (Fin r ⊕ Fin t) → K :=
  vec (Matrix.fromBlocks (1:Matrix (Fin r) (Fin r) K) 0 0 (0:Matrix (Fin t) (Fin t) K))
def standardRank (K : Type*) [Field K] (r t : ℕ) :=
  (hessian (per K (Fin r ⊕ Fin t)) (standard K r t)).rank

theorem binary_rank_invariant (binary : (2:K)=0) (z : I × I → K) :
    (hessian (per K I) z).rank=standardRank K (board z).rank (Fintype.card I-(board z).rank) := by
  let A := board z
  obtain ⟨V,U,e,hv,hu,red⟩ := Matrix.exists_rank_normal_form A
  have rk := determinant_rank_eq V U hv hu z
  rw [←binary_per_eq_det binary] at rk
  change (hessian (per K I) z).rank=(hessian (per K I) (vec (V*(A*U)))).rank at rk
  rw [←Matrix.mul_assoc,red] at rk
  have eq : vec ((Matrix.fromBlocks (1:Matrix (Fin A.rank) (Fin A.rank) K) 0 0
      (0:Matrix (Fin (Fintype.card I-A.rank)) (Fin (Fintype.card I-A.rank)) K)).submatrix e e)=
      standard K A.rank (Fintype.card I-A.rank) ∘ (e.symm.prodCongr e.symm).symm := by
    funext ⟨i,j⟩
    rfl
  rw [eq] at rk
  exact rk.trans (transport_rank e.symm _)

theorem fixed_binary_smooth (binary : (2:K)=0) (n s : ℕ) (size : 2≤n) :
    PermanentOrderThree.AtOrder K n s ↔ s=2*n := by
  obtain ⟨t,rfl⟩ : ∃ t, n=2+t := ⟨n-2,by omega⟩
  obtain ⟨w,pw,gw,rw'⟩ := even_witness (K:=K) t
  have nw : cofactor w≠0 := by
    intro h
    rw [h,Matrix.rank_zero] at gw
    omega
  constructor
  · rintro ⟨z,pz,gz,rz⟩
    have x := binary_corank_one binary z pz gz
    have y := binary_corank_one binary w pw nw
    have xy : (board z).rank=(board w).rank := by omega
    have ranks : (hessian (per K _) z).rank=(hessian (per K _) w).rank := by
      rw [binary_rank_invariant binary z,binary_rank_invariant binary w,xy]
    omega
  · intro h
    exact ⟨w,pw,nw,by omega⟩

#print axioms binary_corank_one
#print axioms fixed_binary_smooth
end DeterminantHessian
