import PermanentFourProfiles

/-! Classification when the first two core columns agree. All zero tests
hold over arbitrary fields in which two is nonzero. -/
noncomputable section
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]
def equalPoint (a c s b f t g i u v w l d : K) : Cell4 → K :=
  grid ![![a,a,c,s],![b,b,f,t],![g,g,i,u],![v,w,l,d]]

private theorem cancel_pair (c x y : K) (hc : c≠0) (eq : c*x+c*y=0) : x= -y := by
  apply eq_neg_of_add_eq_zero_left
  apply (mul_eq_zero.mp (show c*(x+y)=0 from ?_)).resolve_left hc
  linear_combination eq

theorem equal_point_impossible (two_ne : (2:K)≠0) (a c s b f t g i u v w l d m n : K)
    (h : SmallChart (equalPoint a c s b f t g i u v w l d))
    (cp : Profile (equalPoint a c s b f t g i u v w l d) m)
    (rp : Profile (transposePoint (equalPoint a c s b f t g i u v w l d)) n) : False := by
  have cs : c=0 ↔ s=0 := cp.same 0
  have ft : f=0 ↔ t=0 := cp.same 1
  have iu : i=0 ↔ u=0 := cp.same 2
  have gv : g=0 ↔ v=0 := rp.same 0
  have gw : g=0 ↔ w=0 := rp.same 1
  have il : i=0 ↔ l=0 := rp.same 2
  have cb : c=0 ∨ f=0 ∨ i=0 := by
    obtain ⟨j,hj⟩ := cp.missing
    fin_cases j <;> first | exact Or.inl hj | exact Or.inr (Or.inl hj) | exact Or.inr (Or.inr hj)
  have rb : g=0 ∨ i=0 := by
    obtain ⟨j,hj⟩ := rp.missing
    fin_cases j <;> first | exact Or.inl hj | exact Or.inr hj
  have ab : a-b=n*g := rp.diff 0
  have cf : c-f=n*i := rp.diff 2
  have sparse : n*g*g=0 := rp.sparse 0 1 (by decide)
  have p := h.smooth
  simp [grad,otherThree,three,equalPoint,grid] at p
  by_cases hi : i=0
  · have hg : g≠0 := by intro eq; simp [eq,hi] at p
    have nn : n=0 := by simpa [hg] using sparse
    have ba : b=a := (sub_eq_zero.mp (by simpa [nn] using ab)).symm
    have fc : f=c := (sub_eq_zero.mp (by simpa [nn] using cf)).symm
    have hc : c≠0 := by intro eq; simp [fc,eq,hi] at p
    have ha : a≠0 := by intro eq; simp [ba,eq,hi] at p
    have hs : s≠0 := fun e ↦ hc (cs.mpr e)
    have hv : v≠0 := fun e ↦ hg (gv.mpr e)
    have edge : c*t+f*s=0 := cp.edge 0 1 (by decide)
    have ts := cancel_pair c t s hc (by simpa [fc] using edge)
    have wv := cancel_pair g w v hg (rp.edge 0 1 (by decide))
    have form : equalPoint a c s b f t g i u v w l d=crossedPoint a c s g v d := by
      rw [ba,fc,ts,iu.mp hi,il.mp hi,hi,wv]
      rfl
    rw [form] at h
    exact exclude_crossed two_ne a c s g v d ha hc hs hg hv h
  · have hg : g=0 := rb.resolve_right hi
    have ba : b=a := (sub_eq_zero.mp (by simpa [hg] using ab)).symm
    have ha : a≠0 := by intro eq; simp [ba,eq,hg] at p
    have hl : l≠0 := fun eq ↦ hi (il.mpr eq)
    have hu : u≠0 := fun eq ↦ hi (iu.mpr eq)
    by_cases hc : c=0
    · by_cases hf : f=0
      · have form : equalPoint a c s b f t g i u v w l d=blockPoint a i u l d := by
          rw [ba,cs.mp hc,ft.mp hf,gv.mp hg,gw.mp hg,hc,hf,hg]
          rfl
        rw [form] at h
        exact exclude_block two_ne a i u l d ha hi hu hl h
      · have ht : t≠0 := fun eq ↦ hf (ft.mpr eq)
        have op : f*u+i*t=0 := cp.edge 1 2 (by decide)
        have form : equalPoint a c s b f t g i u v w l d=swappedUpper a f t i u l d := by
          rw [ba,cs.mp hc,gv.mp hg,gw.mp hg,hc,hg]
          rfl
        rw [form] at h
        exact exclude_swapped two_ne a f t i u l d ha hf ht hi hl op h
    · have hf : f=0 := (cb.resolve_left hc).resolve_right hi
      have hs : s≠0 := fun eq ↦ hc (cs.mpr eq)
      have op : c*u+i*s=0 := cp.edge 0 2 (by decide)
      have form : equalPoint a c s b f t g i u v w l d=upperPoint a c s i u l d := by
        rw [ba,ft.mp hf,gv.mp hg,gw.mp hg,hf,hg]
        rfl
      rw [form] at h
      exact exclude_upper two_ne a c s i u l d ha hc hs hi hl op h

theorem equal_columns_exclude (two_ne : (2:K)≠0) (z : Cell4 → K) (n : K)
    (h : SmallChart z) (c : Profile z 0) (r : Profile (transposePoint z) n) : False := by
  have eq (i : T) : z (i.castSucc,1)=z (i.castSucc,0) :=
    (sub_eq_zero.mp (by simpa using c.diff i)).symm
  let y := equalPoint (z (0,0)) (z (0,2)) (z (0,3)) (z (1,0)) (z (1,2)) (z (1,3))
    (z (2,0)) (z (2,2)) (z (2,3)) (z (3,0)) (z (3,1)) (z (3,2)) (z (3,3))
  have xy : z=y := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> first | rfl | exact eq 0 | exact eq 1 | exact eq 2
  exact equal_point_impossible two_ne _ _ _ _ _ _ _ _ _ _ _ _ _ 0 n (xy ▸ h) (xy ▸ c) (xy ▸ r)

theorem no_small_chart (two_ne : (2:K)≠0) (z : Cell4 → K) (h : SmallChart z) : False := by
  obtain ⟨x,i,j,chart,col,row⟩ := normalized_chart h
  have ji := two_support x chart two_ne j row
  have ii := two_support (transposePoint x) chart.transpose two_ne i (col_to_row x _ col)
  subst i
  subst j
  obtain ⟨m,c⟩ := make_profile two_ne chart (column_pairs x row)
  obtain ⟨n,r⟩ := make_profile two_ne chart.transpose (column_pairs _ (col_to_row x _ col))
  rcases one_zero x chart.smooth m n c r with hm|hn
  · subst m
    exact equal_columns_exclude two_ne x n chart c r
  · subst n
    exact equal_columns_exclude two_ne (transposePoint x) m chart.transpose r c

theorem seven_excluded (two_ne : (2:K)≠0) (z : Cell4 → K) (flat : PermanentBorder.value z=0)
    (smooth : cofactor z≠0) : (hessian (per K F) z).rank≠7 := by
  intro seven
  obtain ⟨x,h⟩ := chart_of_seven z flat smooth seven
  exact no_small_chart two_ne x h

#print axioms no_small_chart
#print axioms seven_excluded
end PermanentOrderFour
