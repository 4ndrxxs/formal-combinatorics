import Quantum.Hadamard.Basic

/-! Sign matrices of odd square order from parallel classes of an affine plane. -/
noncomputable section
namespace Hadamard.FiniteFieldAffine
open Finset HadamardMod
variable {p : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
abbrev Point (F : Type*) := F × F

private def line (p : ℕ) (s : F) (i j : Point F) : ZMod p :=
  if j.2 = i.2+s*(j.1-i.1) then 1 else 0

private theorem line_sym (s : F) (i j : Point F) : line p s i j = line p s j i := by
  have eq : j.2=i.2+s*(j.1-i.1) ↔ i.2=j.2+s*(i.1-j.1) := by constructor <;> intro h <;> linear_combination -h
  simp only [line,eq]

private theorem along (s : F) (i : Point F) (f : Point F → ZMod p) :
    (∑ j, line p s i j*f j)=∑ x, f (x,i.2+s*(x-i.1)) := by
  rw [Fintype.sum_prod_type]
  simp only [line,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem line_sum (s : F) (i : Point F) : (∑ j, line p s i j)=(Fintype.card F : ZMod p) := by
  simpa using along s i (fun _ => (1:ZMod p))

private theorem two_lines (s t : F) (i k : Point F) :
    (∑ j, line p s i j*line p t k j)=if s=t then (Fintype.card F : ZMod p)*line p s i k else 1 := by
  rw [along]
  by_cases st : s=t
  · subst t
    have eq (x : F) : i.2+s*(x-i.1)=k.2+s*(x-k.1) ↔ k.2=i.2+s*(k.1-i.1) := by
      constructor <;> intro h <;> linear_combination -h
    simp [line,eq]
  · have nz : s-t≠0 := sub_ne_zero.mpr st
    have eq (x : F) : i.2+s*(x-i.1)=k.2+t*(x-k.1) ↔
        x=(k.2-i.2+s*i.1-t*k.1)/(s-t) := by
      rw [eq_div_iff nz]
      constructor <;> intro h <;> linear_combination h
    simp [line,eq,st]

private def bundle (p : ℕ) (T : Finset F) (i j : Point F) : ZMod p :=
  ∑ s ∈ T, line p s i j

private theorem bundle_sym (T : Finset F) (i j : Point F) :
    bundle p T i j=bundle p T j i := by simp only [bundle,line_sym (i:=i) (j:=j)]

private theorem bundle_sum (T : Finset F) (i : Point F) :
    (∑ j, bundle p T i j)=(T.card:ZMod p)*(Fintype.card F : ZMod p) := by
  unfold bundle
  rw [Finset.sum_comm]
  simp [line_sum]

private theorem bundle_dot (T : Finset F) (i k : Point F) :
    (∑ j, bundle p T i j*bundle p T k j) =
      (Fintype.card F : ZMod p)*bundle p T i k+(T.card:ZMod p)*((T.card:ZMod p)-1) := by
  unfold bundle
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  have inner (s : F) (hs : s∈T) :
      (∑ j, ∑ t ∈ T, line p t i j*line p s k j)= (Fintype.card F : ZMod p)*line p s i k+((T.card:ZMod p)-1) := by
    rw [Finset.sum_comm]
    simp only [two_lines]
    have eq (t : F) : (if t=s then (Fintype.card F : ZMod p)*line p t i k else 1)=
        (if t=s then (Fintype.card F : ZMod p)*line p s i k-1 else 0)+1 := by
      by_cases h : t=s <;> simp [h]
    simp [eq,Finset.sum_add_distrib,hs]
    ring
  rw [Finset.sum_congr rfl inner,Finset.sum_add_distrib]
  simp
  ring

def signEntry (p : ℕ) (T : Finset F) (i j : Point F) : ZMod p :=
  1-2*bundle p T i j+(if i=j then 2*(T.card:ZMod p) else 0)

private theorem sign_entry (T : Finset F) (i j : Point F) : Sign (signEntry p T i j) := by
  by_cases eq : i=j
  · subst j
    simp [signEntry,bundle,line,Sign]
  · by_cases hx : j.1=i.1
    · have hy : j.2≠i.2 := fun h => eq (Prod.ext hx.symm h.symm)
      simp [signEntry,bundle,line,eq,hx,hy,Sign]
    · have cond (s : F) : j.2=i.2+s*(j.1-i.1) ↔ s=(j.2-i.2)/(j.1-i.1) := by
        rw [eq_div_iff (sub_ne_zero.mpr hx)]
        constructor <;> intro h <;> linear_combination -h
      unfold signEntry bundle line
      simp only [cond,Finset.sum_ite_eq',if_neg eq,add_zero]
      split
      · exact Or.inr (by ring)
      · exact Or.inl (by ring)

theorem affine_good (T : Finset F) (chosen : 2*(T.card:ZMod p)=(Fintype.card F : ZMod p)) :
    Good (signEntry p T) := by
  refine ⟨sign_entry T,?_⟩
  intro i k ne
  have dot := bundle_dot (p:=p) T i k
  have rowi := bundle_sum (p:=p) T i
  have rowk := bundle_sum (p:=p) T k
  let a := 2*(T.card:ZMod p)
  have factor (j : Point F) :
      signEntry p T i j*signEntry p T k j =
      (1 - 2*bundle p T i j - 2*bundle p T k j + 4*(bundle p T i j*bundle p T k j))+
      (if i=j then a*(1-2*bundle p T k i) else 0)+
      (if k=j then a*(1-2*bundle p T i k) else 0) := by
    by_cases h : i=j <;> by_cases e : k=j
    · exact (ne (h.trans e.symm)).elim
    · subst j; simp [signEntry,e,a]; ring
    · subst j; simp [signEntry,h,a]; ring
    · simp [signEntry,h,e]; ring
  simp only [factor,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_prod,
    nsmul_eq_mul,Nat.cast_mul,mul_one,rowi,rowk,dot]
  rw [bundle_sym T k i]
  dsimp [a]
  rw [←chosen]
  ring

theorem at_square_order (T : Finset F) (chosen : 2*(T.card:ZMod p)=(Fintype.card F : ZMod p)) :
    AtOrder p ((Fintype.card F)^2) := of_card (affine_good T chosen) (by simp [Point,pow_two])

#print axioms at_square_order
end Hadamard.FiniteFieldAffine
