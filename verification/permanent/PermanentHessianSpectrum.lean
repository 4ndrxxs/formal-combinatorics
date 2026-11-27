import PermanentOrderTransport
import PermanentSpectrumSeeds
import PermanentHessianRankGap

/-! Exact Hessian ranks occurring on permanent hypersurfaces, with the
order allowed to vary. Even witnesses use order two plus the number of
borders. Odd witnesses start in order three. -/
noncomputable section
open Matrix Module Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {K : Type*} [Field K]

theorem grow (t : ℕ) {I : Type} [Fintype I] [DecidableEq I] {z : CellOf I → K} {s : ℕ}
    (start : Marked z s) : ∃ n, n=Fintype.card I+t ∧ ∃ y : CellOf (Fin n) → K,
      value y=0 ∧ (cofactor y).rank=1 ∧ (hessian (per K (Fin n)) y).rank=s+2*t := by
  induction t generalizing I s with
  | zero =>
    let e := Fintype.equivFin I
    refine ⟨_,by omega,z ∘ (e.prodCongr e).symm,(transport_value e z).trans start.1,
      (transport_cofactor_rank e z).trans start.2.1,?_⟩
    simpa using (transport_rank e z).trans start.2.2.1
  | succ t ih =>
    obtain ⟨n,card,y,zero,one,rank⟩ := ih start.extend
    rw [Fintype.card_option] at card
    exact ⟨n,by omega,y,zero,one,by omega⟩

theorem even_witness (t : ℕ) : ∃ z : CellOf (Fin (2+t)) → K,
    value z=0 ∧ (cofactor z).rank=1 ∧ (hessian (per K (Fin (2+t))) z).rank=4+2*t := by
  obtain ⟨n,card,z,h⟩ := grow t (even_marked (K:=K))
  rw [Fintype.card_fin] at card
  exact card ▸ ⟨z,h⟩

theorem odd_witness (two : (2:K)≠0) (t : ℕ) : ∃ z : CellOf (Fin (3+t)) → K,
    value z=0 ∧ (cofactor z).rank=1 ∧ (hessian (per K (Fin (3+t))) z).rank=7+2*t := by
  obtain ⟨n,card,z,h⟩ := grow t (odd_marked two)
  rw [Fintype.card_fin] at card
  exact card ▸ ⟨z,h⟩

def Occurs (K : Type*) [Field K] (s : ℕ) : Prop :=
  ∃ n, ∃ z : CellOf (Fin n) → K, value z=0 ∧ (hessian (per K (Fin n)) z).rank=s

def SmoothOccurs (K : Type*) [Field K] (s : ℕ) : Prop :=
  ∃ n, 2≤n ∧ ∃ z : CellOf (Fin n) → K, value z=0 ∧ cofactor z≠0 ∧
    (hessian (per K (Fin n)) z).rank=s

theorem SmoothOccurs.occurs {s : ℕ} (h : SmoothOccurs K s) : Occurs K s := by
  obtain ⟨n,_,z,hp,_,hr⟩ := h
  exact ⟨n,z,hp,hr⟩

theorem zero_occurs : Occurs K 0 := by
  let z : CellOf (Fin 3) → ℤ := 0
  have value : integralValue z=0 := by decide +kernel
  have hess : table z=0 := by decide +kernel
  refine ⟨3,castPoint K z,by rw [cast_value,value,Int.cast_zero],?_⟩
  rw [cast_hessian,hess]
  simp

private theorem nonzero_of_one {I : Type*} [Fintype I] {A : Matrix I I K} (h : A.rank=1) :
    A≠0 := by
  intro zero
  rw [zero,Matrix.rank_zero] at h
  omega

theorem even_smooth (t : ℕ) : SmoothOccurs K (4+2*t) := by
  obtain ⟨z,zero,one,rank⟩ := even_witness (K:=K) t
  exact ⟨2+t,by omega,z,zero,nonzero_of_one one,rank⟩

theorem odd_smooth (two : (2:K)≠0) (t : ℕ) : SmoothOccurs K (7+2*t) := by
  obtain ⟨z,zero,one,rank⟩ := odd_witness two t
  exact ⟨3+t,by omega,z,zero,nonzero_of_one one,rank⟩

theorem positive_smooth (two : (2:K)≠0) (s : ℕ) (pos : s=4 ∨ 6≤s) : SmoothOccurs K s := by
  by_cases even : s%2=0
  · have e : s=4+2*((s-4)/2) := by omega
    exact e ▸ even_smooth ((s-4)/2)
  · have e : s=7+2*((s-7)/2) := by omega
    exact e ▸ odd_smooth two ((s-7)/2)

theorem spectrum_of_two_ne_zero (two : (2:K)≠0) (s : ℕ) :
    Occurs K s ↔ s=0 ∨ s=4 ∨ 6≤s := by
  constructor
  · rintro ⟨n,z,_,rank⟩
    exact rank ▸ permanent_hessian_rank_gap z
  · rintro (rfl|pos)
    · exact zero_occurs
    · exact (positive_smooth two s pos).occurs

#print axioms even_witness
#print axioms odd_witness
#print axioms spectrum_of_two_ne_zero
end PermanentBorder
