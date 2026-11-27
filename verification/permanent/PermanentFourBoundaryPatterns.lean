import PermanentFourTemplates

/-! The three terminal support patterns, with explicit row and column
multipliers. The last entry is uniquely fixed by the zero-permanent equation. -/
noncomputable section
open Matrix Equiv Finset PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]

def blockPoint (a i u v d : K) : Cell4 → K :=
  grid ![![a,a,0,0],![a,a,0,0],![0,0,i,u],![0,0,v,d]]
def crossedPoint (a c s g t d : K) : Cell4 → K :=
  grid ![![a,a,c,s],![a,a,c,-s],![g,g,0,0],![t,-t,0,d]]
def upperPoint (a c s i u t d : K) : Cell4 → K :=
  grid ![![a,a,c,s],![a,a,0,0],![0,0,i,u],![0,0,t,d]]
def swappedUpper (a c s i u t d : K) : Cell4 → K :=
  grid ![![a,a,0,0],![a,a,c,s],![0,0,i,u],![0,0,t,d]]

theorem exclude_block (two_ne : (2:K)≠0) (a i u v d : K)
    (ha : a≠0) (hi : i≠0) (hu : u≠0) (hv : v≠0)
    (h : SmallChart (blockPoint a i u v d)) : False := by
  let r : F → K := ![a⁻¹,a⁻¹,i⁻¹,v⁻¹]
  let c : F → K := ![1,1,1,i/u]
  have hr (j : F) : r j≠0 := by fin_cases j <;> simp [r,ha,hi,hv]
  have hc (j : F) : c j≠0 := by fin_cases j <;> simp [c,hi,hu]
  apply away_excludes two_ne 0 _ (h.scale r c hr hc)
  rintro ⟨x,y⟩ away
  fin_cases x <;> fin_cases y <;> first | exact (away rfl).elim |
    simp [scale,r,c,blockPoint,grid,castPoint,model,ha,hi,hv]
  field_simp

theorem exclude_crossed (two_ne : (2:K)≠0) (a c s g t d : K)
    (ha : a≠0) (hc : c≠0) (hs : s≠0) (hg : g≠0) (ht : t≠0)
    (h : SmallChart (crossedPoint a c s g t d)) : False := by
  let r : F → K := ![1,1,a/g,a/t]
  let b : F → K := ![a⁻¹,a⁻¹,c⁻¹,s⁻¹]
  have hr (j : F) : r j≠0 := by fin_cases j <;> simp [r,ha,hg,ht]
  have hb (j : F) : b j≠0 := by fin_cases j <;> simp [b,ha,hc,hs]
  apply away_excludes two_ne 1 _ (h.scale r b hr hb)
  rintro ⟨x,y⟩ away
  fin_cases x <;> fin_cases y <;> first | exact (away rfl).elim |
    simp [scale,r,b,crossedPoint,grid,castPoint,model,ha,hc,hs]
  all_goals field_simp

theorem exclude_upper (two_ne : (2:K)≠0) (a c s i u t d : K)
    (ha : a≠0) (hc : c≠0) (hs : s≠0) (hi : i≠0) (ht : t≠0)
    (opposite : c*u+i*s=0) (h : SmallChart (upperPoint a c s i u t d)) : False := by
  let r : F → K := ![1,1,c/i,c/t]
  let b : F → K := ![a⁻¹,a⁻¹,c⁻¹,s⁻¹]
  have hr (j : F) : r j≠0 := by fin_cases j <;> simp [r,hc,hi,ht]
  have hb (j : F) : b j≠0 := by fin_cases j <;> simp [b,ha,hc,hs]
  apply away_excludes two_ne 2 _ (h.scale r b hr hb)
  rintro ⟨x,y⟩ away
  fin_cases x <;> fin_cases y <;> first | exact (away rfl).elim |
    simp [scale,r,b,upperPoint,grid,castPoint,model,ha,hc,hs]
  all_goals field_simp
  linear_combination opposite

theorem exclude_swapped (two_ne : (2:K)≠0) (a c s i u t d : K)
    (ha : a≠0) (hc : c≠0) (hs : s≠0) (hi : i≠0) (ht : t≠0)
    (opposite : c*u+i*s=0) (h : SmallChart (swappedUpper a c s i u t d)) : False := by
  let e : Perm F := Equiv.swap 0 1
  have eq : swappedUpper a c s i u t d ∘ e.prodCongr (Equiv.refl F)=upperPoint a c s i u t d := by
    funext ⟨x,y⟩
    fin_cases x <;> fin_cases y <;> rfl
  have hh := h.reindex e (Equiv.refl _) (by decide) rfl
  rw [eq] at hh
  exact exclude_upper two_ne a c s i u t d ha hc hs hi ht opposite hh

#print axioms exclude_upper
end PermanentOrderFour
