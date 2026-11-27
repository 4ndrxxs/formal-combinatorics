import AlternatingMatrixRank
import PermanentHessianSpectrum

/-! The spectrum in characteristic two, and both spectra on the smooth
locus in orders at least two. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private theorem partial_expansion {R : Type*} [CommRing R] {r s : I} (ne : s≠r)
    (z : CellOf I → R) (j : I) :
    gradAt z (r,j)=∑ k, secondAt z (s,k) (r,j)*z (s,k) := by
  simp only [gradAt,secondAt,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases a : p j=r
  · let l := p.symm s
    have b : p l=s := p.apply_symm_apply s
    have lj : l≠j := fun eq ↦ ne ((b.symm.trans (congrArg p eq)).trans a)
    rw [Finset.sum_eq_single l]
    · rw [ite_eq_left a,ite_eq_left ⟨a,lj,b⟩,←b,mul_comm]
      exact (Finset.mul_prod_erase (univ.erase j) (fun k ↦ z (p k,k)) (by simpa using lj)).symm
    · intro k _ kl
      have nk : p k≠s := fun h ↦ kl (p.injective (h.trans b.symm))
      simp [nk]
    · simp
  · simp [a]

theorem smooth_positive [Nontrivial I] (z : CellOf I → K) (smooth : cofactor z≠0) :
    (hessian (per K I) z).rank≠0 := by
  intro zero
  have vanish : hessian (per K I) z=0 := by
    by_contra hn
    have rank := (permanent_hessian_small z hn (by omega)).1
    omega
  apply smooth
  ext r j
  obtain ⟨s,ne⟩ := exists_ne r
  change gradAt z (r,j)=0
  rw [partial_expansion ne]
  apply Finset.sum_eq_zero
  intro k _
  rw [←second_formula,vanish]
  simp

theorem even_hessian (two : (2:K)=0) (z : CellOf I → K) : Even (hessian (per K I) z).rank := by
  let H := hessian (per K I) z
  have P := hessian_grid_symmetry z
  have neg (x : K) : x= -x := by
    apply eq_neg_of_add_eq_zero_left
    rw [←two_mul,two,zero_mul]
  apply AlternatingMatrix.even_rank H
  · intro u v
    exact (P.sym u v).trans (neg _)
  · rintro ⟨r,i⟩
    exact P.rows r i i

theorem spectrum_of_two_eq_zero (two : (2:K)=0) (s : ℕ) :
    Occurs K s ↔ s=0 ∨ 4≤s ∧ Even s := by
  constructor
  · rintro ⟨n,z,_,rank⟩
    have gap := permanent_hessian_rank_gap z
    have even := even_hessian two z
    rw [rank] at gap even
    rcases gap with h|h|h
    · exact Or.inl h
    · exact Or.inr ⟨by omega,even⟩
    · exact Or.inr ⟨by omega,even⟩
  · rintro (rfl|⟨bound,t,eq⟩)
    · exact zero_occurs
    · have e : s=4+2*(t-2) := by omega
      exact e ▸ (even_smooth (K:=K) (t-2)).occurs

private theorem smooth_ne_zero {s : ℕ} (h : SmoothOccurs K s) : s≠0 := by
  obtain ⟨n,hn,z,_,smooth,rank⟩ := h
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact rank ▸ smooth_positive z smooth

theorem smooth_spectrum_of_two_ne_zero (two : (2:K)≠0) (s : ℕ) :
    SmoothOccurs K s ↔ s=4 ∨ 6≤s := by
  constructor
  · intro h
    exact ((spectrum_of_two_ne_zero two s).mp h.occurs).resolve_left (smooth_ne_zero h)
  · exact positive_smooth two s

theorem smooth_spectrum_of_two_eq_zero (two : (2:K)=0) (s : ℕ) :
    SmoothOccurs K s ↔ 4≤s ∧ Even s := by
  constructor
  · intro h
    exact ((spectrum_of_two_eq_zero two s).mp h.occurs).resolve_left (smooth_ne_zero h)
  · rintro ⟨hs,t,eq⟩
    have e : s=4+2*(t-2) := by omega
    exact e ▸ even_smooth (t-2)

#print axioms even_hessian
#print axioms spectrum_of_two_eq_zero
#print axioms smooth_spectrum_of_two_ne_zero
#print axioms smooth_spectrum_of_two_eq_zero
end PermanentBorder
