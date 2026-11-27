import SignedSevenCover

namespace Signed39.Profiles

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem miss1 : ∀ w∈orders 7 [-8,-2,0,1,3,3,3], ¬flatSixteen w := by decide +kernel
private theorem miss2 : ∀ w∈orders 7 [-8,-2,0,2,2,2,4], ¬flatSixteen w := by decide +kernel
private theorem miss3 : ∀ w∈orders 7 [-8,-2,1,1,1,3,4], ¬flatSixteen w := by decide +kernel
private theorem miss4 : ∀ w∈orders 7 [-8,-1,-1,1,2,3,4], ¬flatSixteen w := by decide +kernel
private theorem miss5 : ∀ w∈orders 7 [-8,-1,0,1,1,2,5], ¬flatSixteen w := by decide +kernel
private theorem miss6 : ∀ w∈orders 7 [-8,0,0,0,0,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss7 : ∀ w∈orders 7 [-7,-4,0,2,3,3,3], ¬flatSixteen w := by decide +kernel
private theorem miss8 : ∀ w∈orders 7 [-7,-4,1,1,2,3,4], ¬flatSixteen w := by decide +kernel
private theorem miss9 : ∀ w∈orders 7 [-7,-3,-1,1,2,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss10 : ∀ w∈orders 7 [-7,-3,-1,2,2,2,5], ¬flatSixteen w := by decide +kernel
private theorem miss11 : ∀ w∈orders 7 [-7,-3,0,0,2,3,5], ¬flatSixteen w := by decide +kernel
private theorem miss12 : ∀ w∈orders 7 [-7,-2,-2,1,2,3,5], ¬flatSixteen w := by decide +kernel
private theorem miss13 : ∀ w∈orders 7 [-7,-2,-1,-1,3,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss14 : ∀ w∈orders 7 [-7,-2,-1,0,1,4,5], ¬flatSixteen w := by decide +kernel
private theorem miss15 : ∀ w∈orders 7 [-7,-2,-1,1,1,2,6], ¬flatSixteen w := by decide +kernel
private theorem miss16 : ∀ w∈orders 7 [-7,-1,-1,-1,2,2,6], ¬flatSixteen w := by decide +kernel
private theorem miss17 : ∀ w∈orders 7 [-7,-1,-1,0,0,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss18 : ∀ w∈orders 7 [-6,-5,0,1,3,3,4], ¬flatSixteen w := by decide +kernel
private theorem miss19 : ∀ w∈orders 7 [-6,-5,1,1,1,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss20 : ∀ w∈orders 7 [-6,-5,1,1,2,2,5], ¬flatSixteen w := by decide +kernel
private theorem miss21 : ∀ w∈orders 7 [-6,-4,-2,2,2,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss22 : ∀ w∈orders 7 [-6,-4,-1,0,3,3,5], ¬flatSixteen w := by decide +kernel
private theorem miss23 : ∀ w∈orders 7 [-6,-4,-1,1,1,4,5], ¬flatSixteen w := by decide +kernel
private theorem miss24 : ∀ w∈orders 7 [-6,-4,0,0,2,2,6], ¬flatSixteen w := by decide +kernel
private theorem miss25 : ∀ w∈orders 7 [-6,-3,-3,1,3,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss26 : ∀ w∈orders 7 [-6,-3,-3,2,2,3,5], ¬flatSixteen w := by decide +kernel
private theorem miss27 : ∀ w∈orders 7 [-6,-3,-2,1,1,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss28 : ∀ w∈orders 7 [-6,-3,-1,-1,2,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss29 : ∀ w∈orders 7 [-6,-3,-1,0,0,5,5], ¬flatSixteen w := by decide +kernel
private theorem miss30 : ∀ w∈orders 7 [-6,-3,0,0,1,1,7], ¬flatSixteen w := by decide +kernel
private theorem miss32 : ∀ w∈orders 7 [-6,-2,-2,-1,1,5,5], ¬flatSixteen w := by decide +kernel
private theorem miss33 : ∀ w∈orders 7 [-6,-2,-2,0,0,4,6], ¬flatSixteen w := by decide +kernel
private theorem miss34 : ∀ w∈orders 7 [-6,-2,-2,1,1,1,7], ¬flatSixteen w := by decide +kernel
private theorem miss35 : ∀ w∈orders 7 [-6,-2,-1,-1,1,2,7], ¬flatSixteen w := by decide +kernel
private theorem miss36 : ∀ w∈orders 7 [-5,-5,-2,1,3,4,4], ¬flatSixteen w := by decide +kernel
private theorem miss37 : ∀ w∈orders 7 [-5,-5,-2,2,2,3,5], ¬flatSixteen w := by decide +kernel
private theorem miss38 : ∀ w∈orders 7 [-5,-5,-1,0,2,4,5], ¬flatSixteen w := by decide +kernel
private theorem miss39 : ∀ w∈orders 7 [-5,-5,-1,1,2,2,6], ¬flatSixteen w := by decide +kernel
private theorem miss40 : ∀ w∈orders 7 [-5,-5,0,0,1,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss41 : ∀ w∈orders 7 [-5,-4,-3,1,2,4,5], ¬flatSixteen w := by decide +kernel
private theorem miss42 : ∀ w∈orders 7 [-5,-4,-2,-1,3,4,5], ¬flatSixteen w := by decide +kernel
private theorem miss43 : ∀ w∈orders 7 [-5,-4,-2,0,1,5,5], ¬flatSixteen w := by decide +kernel
private theorem miss44 : ∀ w∈orders 7 [-5,-4,-1,-1,1,4,6], ¬flatSixteen w := by decide +kernel
private theorem miss45 : ∀ w∈orders 7 [-5,-4,-1,0,1,2,7], ¬flatSixteen w := by decide +kernel
private theorem miss46 : ∀ w∈orders 7 [-5,-3,-3,0,1,4,6], ¬flatSixteen w := by decide +kernel
private theorem miss47 : ∀ w∈orders 7 [-5,-3,-2,-2,2,5,5], ¬flatSixteen w := by decide +kernel
private theorem miss48 : ∀ w∈orders 7 [-5,-3,-2,-2,3,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss49 : ∀ w∈orders 7 [-5,-3,-2,-1,2,2,7], ¬flatSixteen w := by decide +kernel
private theorem miss50 : ∀ w∈orders 7 [-5,-3,-2,0,0,3,7], ¬flatSixteen w := by decide +kernel
private theorem miss51 : ∀ w∈orders 7 [-5,-2,-2,-2,1,3,7], ¬flatSixteen w := by decide +kernel
private theorem miss52 : ∀ w∈orders 7 [-5,-2,-2,-1,-1,5,6], ¬flatSixteen w := by decide +kernel
private theorem miss53 : ∀ w∈orders 7 [-5,-2,-1,-1,0,1,8], ¬flatSixteen w := by decide +kernel
private theorem miss56 : ∀ w∈orders 7 [-4,-4,-3,-1,2,5,5], ¬flatSixteen w := by decide +kernel
private theorem miss57 : ∀ w∈orders 7 [-4,-4,-3,-1,3,3,6], ¬flatSixteen w := by decide +kernel
private theorem miss58 : ∀ w∈orders 7 [-4,-4,-3,1,1,2,7], ¬flatSixteen w := by decide +kernel
private theorem miss59 : ∀ w∈orders 7 [-4,-4,-2,-2,2,4,6], ¬flatSixteen w := by decide +kernel
private theorem miss60 : ∀ w∈orders 7 [-4,-4,-2,-1,1,3,7], ¬flatSixteen w := by decide +kernel
private theorem miss61 : ∀ w∈orders 7 [-4,-4,-1,-1,-1,5,6], ¬flatSixteen w := by decide +kernel
private theorem miss62 : ∀ w∈orders 7 [-4,-4,0,0,0,0,8], ¬flatSixteen w := by decide +kernel
private theorem miss63 : ∀ w∈orders 7 [-4,-3,-3,-1,0,5,6], ¬flatSixteen w := by decide +kernel
private theorem miss64 : ∀ w∈orders 7 [-4,-3,-2,-1,-1,4,7], ¬flatSixteen w := by decide +kernel
private theorem miss65 : ∀ w∈orders 7 [-4,-3,-2,-1,1,1,8], ¬flatSixteen w := by decide +kernel
private theorem miss66 : ∀ w∈orders 7 [-4,-3,-1,-1,-1,2,8], ¬flatSixteen w := by decide +kernel
private theorem miss67 : ∀ w∈orders 7 [-4,-2,-2,-2,0,2,8], ¬flatSixteen w := by decide +kernel
private theorem miss68 : ∀ w∈orders 7 [-3,-3,-3,-2,0,4,7], ¬flatSixteen w := by decide +kernel
private theorem miss69 : ∀ w∈orders 7 [-3,-3,-3,-1,0,2,8], ¬flatSixteen w := by decide +kernel

theorem seven_classified (x : ZMod 7 → ℤ) (sm : Contraction.mass x=0) (sq : Contraction.energy x=96)
    (h1 : corr x 1= -16) (h2 : corr x 2= -16) (h3 : corr x 3= -16) :
    ∃ L∈sevenPatterns, (seven x).Perm L := by
  obtain ⟨v,hv,perm,word⟩ := seven_spectrum x sm sq
  have flat := list_flat_sixteen x h1 h2 h3
  rw [cover] at hv
  simp only [candidates,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,by decide,perm⟩
  · exact False.elim (miss1 _ word flat)
  · exact False.elim (miss2 _ word flat)
  · exact False.elim (miss3 _ word flat)
  · exact False.elim (miss4 _ word flat)
  · exact False.elim (miss5 _ word flat)
  · exact False.elim (miss6 _ word flat)
  · exact False.elim (miss7 _ word flat)
  · exact False.elim (miss8 _ word flat)
  · exact False.elim (miss9 _ word flat)
  · exact False.elim (miss10 _ word flat)
  · exact False.elim (miss11 _ word flat)
  · exact False.elim (miss12 _ word flat)
  · exact False.elim (miss13 _ word flat)
  · exact False.elim (miss14 _ word flat)
  · exact False.elim (miss15 _ word flat)
  · exact False.elim (miss16 _ word flat)
  · exact False.elim (miss17 _ word flat)
  · exact False.elim (miss18 _ word flat)
  · exact False.elim (miss19 _ word flat)
  · exact False.elim (miss20 _ word flat)
  · exact False.elim (miss21 _ word flat)
  · exact False.elim (miss22 _ word flat)
  · exact False.elim (miss23 _ word flat)
  · exact False.elim (miss24 _ word flat)
  · exact False.elim (miss25 _ word flat)
  · exact False.elim (miss26 _ word flat)
  · exact False.elim (miss27 _ word flat)
  · exact False.elim (miss28 _ word flat)
  · exact False.elim (miss29 _ word flat)
  · exact False.elim (miss30 _ word flat)
  · exact ⟨_,by decide,perm⟩
  · exact False.elim (miss32 _ word flat)
  · exact False.elim (miss33 _ word flat)
  · exact False.elim (miss34 _ word flat)
  · exact False.elim (miss35 _ word flat)
  · exact False.elim (miss36 _ word flat)
  · exact False.elim (miss37 _ word flat)
  · exact False.elim (miss38 _ word flat)
  · exact False.elim (miss39 _ word flat)
  · exact False.elim (miss40 _ word flat)
  · exact False.elim (miss41 _ word flat)
  · exact False.elim (miss42 _ word flat)
  · exact False.elim (miss43 _ word flat)
  · exact False.elim (miss44 _ word flat)
  · exact False.elim (miss45 _ word flat)
  · exact False.elim (miss46 _ word flat)
  · exact False.elim (miss47 _ word flat)
  · exact False.elim (miss48 _ word flat)
  · exact False.elim (miss49 _ word flat)
  · exact False.elim (miss50 _ word flat)
  · exact False.elim (miss51 _ word flat)
  · exact False.elim (miss52 _ word flat)
  · exact False.elim (miss53 _ word flat)
  · exact ⟨_,by decide,perm⟩
  · exact ⟨_,by decide,perm⟩
  · exact False.elim (miss56 _ word flat)
  · exact False.elim (miss57 _ word flat)
  · exact False.elim (miss58 _ word flat)
  · exact False.elim (miss59 _ word flat)
  · exact False.elim (miss60 _ word flat)
  · exact False.elim (miss61 _ word flat)
  · exact False.elim (miss62 _ word flat)
  · exact False.elim (miss63 _ word flat)
  · exact False.elim (miss64 _ word flat)
  · exact False.elim (miss65 _ word flat)
  · exact False.elim (miss66 _ word flat)
  · exact False.elim (miss67 _ word flat)
  · exact False.elim (miss68 _ word flat)
  · exact False.elim (miss69 _ word flat)
  · exact ⟨_,by decide,perm⟩

#print axioms seven_classified

end Signed39.Profiles
