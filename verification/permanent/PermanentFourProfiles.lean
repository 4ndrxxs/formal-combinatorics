import PermanentFourBoundaryPatterns

/-! The two border columns have equal supports. The difference of the
first two columns is proportional to the third, and a nonzero coefficient
forces the third column to have a singleton support. -/
noncomputable section
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]
structure Profile (z : Cell4 → K) (m : K) : Prop where
  diff (i : T) : z (i.castSucc,0)-z (i.castSucc,1)=m*z (i.castSucc,2)
  sparse (i j : T) : i≠j → m*z (i.castSucc,2)*z (j.castSucc,2)=0
  edge (i j : T) : i≠j → z (i.castSucc,2)*z (j.castSucc,3)+z (j.castSucc,2)*z (i.castSucc,3)=0
  same (i : T) : z (i.castSucc,2)=0 ↔ z (i.castSucc,3)=0
  missing : ∃ i : T, z (i.castSucc,2)=0

theorem make_profile (two_ne : (2:K)≠0) {z : Cell4 → K} (h : SmallChart z)
    (p : ColumnPairs z) : ∃ m, Profile z m := by
  have vn : column z 2≠0 := core_column_nonzero z h.smooth 2
  have un := side_column_nonzero h.side
  obtain ⟨m,hm⟩ := Paired.dependent p.outerDiff p.edge.symm un vn
  refine ⟨m,⟨hm,?_,p.edge,?_,?_⟩⟩
  · intro i j ij
    have q := p.innerDiff i j ij
    change column z 2 i*deltaColumn z j+column z 2 j*deltaColumn z i=0 at q
    rw [hm i,hm j] at q
    change m*column z 2 i*column z 2 j=0
    apply (mul_eq_zero.mp (show 2*(m*column z 2 i*column z 2 j)=0 from ?_)).resolve_left two_ne
    linear_combination q
  · intro i
    exact ⟨p.edge.zero_at vn,p.edge.symm.zero_at un⟩
  · by_contra! full
    have e := PermanentSupport.three_kill (column z 2) (column z 3) two_ne p.edge
      (show (0:T)≠1 by decide) (show (0:T)≠2 by decide) (show (1:T)≠2 by decide)
      (full _) (full _) (full _)
    exact un (funext e)

theorem one_zero (z : Cell4 → K) (smooth : grad z (3,3)≠0) (m n : K)
    (c : Profile z m) (r : Profile (transposePoint z) n) : m=0 ∨ n=0 := by
  by_contra! both
  obtain ⟨hm,hn⟩ := both
  by_cases hi : z (2,2)=0
  · have x : z (0,2)-z (1,2)=n*z (2,2) := r.diff 2
    rw [hi,mul_zero] at x
    have cf := sub_eq_zero.mp x
    have y : m*z (0,2)*z (1,2)=0 := c.sparse 0 1 (by decide)
    rw [cf] at y
    have f : z (1,2)=0 := by simpa [hm] using y
    have v0 := core_column_nonzero z smooth 2
    apply v0
    funext j
    fin_cases j <;> first | exact cf.trans f | exact f | exact hi
  · have g : n*z (2,0)*z (2,2)=0 := r.sparse 0 2 (by decide)
    have j : n*z (2,1)*z (2,2)=0 := r.sparse 1 2 (by decide)
    have g0 : z (2,0)=0 := by simpa [hn,hi] using g
    have j0 : z (2,1)=0 := by simpa [hn,hi] using j
    have last : z (2,0)-z (2,1)=m*z (2,2) := c.diff 2
    rw [g0,j0,sub_self] at last
    exact (mul_ne_zero hm hi) last.symm

#print axioms make_profile
#print axioms one_zero
end PermanentOrderFour
