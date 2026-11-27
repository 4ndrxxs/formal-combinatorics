import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! A set-theoretic form of the support classification for vanishing
two-by-two permanents (Laubenbacher and Swanson, Theorem 4.1). -/
noncomputable section
namespace PermanentSupport
variable {K I J : Type*} [Field K]

def NullPairs (A : I → J → K) : Prop :=
  ∀ r s i j, r≠s → i≠j → A r i*A s j+A r j*A s i=0

theorem NullPairs.transpose {A : I → J → K} (h : NullPairs A) :
    NullPairs (fun i r ↦ A r i) := by
  intro i j r s ij rs
  calc A r i*A s j+A s i*A r j=A r i*A s j+A r j*A s i := by ring
       _=0 := h r s i j rs ij

theorem three_kill (a b : J → K) (two : (2:K)≠0)
    (h : ∀ i j, i≠j → a i*b j+a j*b i=0) {p q l : J}
    (pq : p≠q) (pl : p≠l) (ql : q≠l) (ap : a p≠0) (aq : a q≠0) (al : a l≠0) :
    ∀ j, b j=0 := by
  have aux : (2*a q*a l)*b p=0 := by
    linear_combination a l*h p q pq+a q*h p l pl-a p*h q l ql
  have bp := (mul_eq_zero.mp aux).resolve_left (mul_ne_zero (mul_ne_zero two aq) al)
  intro j
  by_cases eq : p=j
  · exact eq ▸ bp
  have v := h p j eq
  rw [bp,mul_zero,add_zero] at v
  exact (mul_eq_zero.mp v).resolve_left ap

private theorem two_columns (A : I → J → K) (h : NullPairs A) (two : (2:K)≠0)
    {r s : I} {p q : J} (rs : r≠s) (pq : p≠q)
    (rp : A r p≠0) (rq : A r q≠0) (sq : A s q≠0) :
    ∀ t j, j≠p → j≠q → A t j=0 := by
  intro t j jp jq
  have nj : A r j=0 := by
    by_contra nz
    exact sq (three_kill (A r) (A s) two (fun i j ij ↦ h r s i j rs ij)
      pq (Ne.symm jp) (Ne.symm jq) rp rq nz q)
  by_cases eq : r=t
  · exact eq ▸ nj
  have hit := h r t p j eq (Ne.symm jp)
  rw [nj,zero_mul,add_zero] at hit
  exact (mul_eq_zero.mp hit).resolve_left rp

/-- The support is contained in a single row, a single column, or one
two-by-two rectangle. -/
theorem pair_support [Nonempty I] (A : I → J → K) (h : NullPairs A) (two : (2:K)≠0) :
    (∃ r, ∀ t j, t≠r → A t j=0) ∨ (∃ p, ∀ t j, j≠p → A t j=0) ∨
      ∃ (r s : I) (p q : J), r≠s ∧ p≠q ∧
        ∀ t j, (t≠r ∧ t≠s) ∨ (j≠p ∧ j≠q) → A t j=0 := by
  classical
  by_cases dis : ∃ r s p q, r≠s ∧ p≠q ∧ A r p≠0 ∧ A s q≠0
  · obtain ⟨r,s,p,q,rs,pq,rp,sq⟩ := dis
    have eq := h r s p q rs pq
    have more : A r q*A s p≠0 := by
      intro z
      rw [z,add_zero] at eq
      exact mul_ne_zero rp sq eq
    have rq := left_ne_zero_of_mul more
    have sp := right_ne_zero_of_mul more
    have cols := two_columns A h two rs pq rp rq sq
    have rows := two_columns (fun j t ↦ A t j) h.transpose two pq rs rp sp sq
    refine Or.inr (Or.inr ⟨r,s,p,q,rs,pq,?_⟩)
    rintro t j (hr|hc)
    · exact rows j t hr.1 hr.2
    · exact cols t j hc.1 hc.2
  by_cases hit : ∃ r p, A r p≠0
  · obtain ⟨r,p,rp⟩ := hit
    by_cases outside : ∃ s q, s≠r ∧ A s q≠0
    · obtain ⟨s,q,sr,sq⟩ := outside
      have qp : q=p := by
        by_contra ne
        exact dis ⟨r,s,p,q,Ne.symm sr,Ne.symm ne,rp,sq⟩
      subst q
      refine Or.inr (Or.inl ⟨p,?_⟩)
      intro t j jp
      by_contra bad
      by_cases tr : t=r
      · subst t
        exact dis ⟨s,r,p,j,sr,Ne.symm jp,sq,bad⟩
      · exact dis ⟨r,t,p,j,Ne.symm tr,Ne.symm jp,rp,bad⟩
    · exact Or.inl ⟨r,fun t j tr ↦ by
        by_contra bad
        exact outside ⟨t,j,tr,bad⟩⟩
  · push Not at hit
    exact Or.inl ⟨Classical.arbitrary I,fun t j _ ↦ hit t j⟩

#print axioms pair_support
end PermanentSupport
