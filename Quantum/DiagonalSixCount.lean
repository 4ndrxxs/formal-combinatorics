module
public import Quantum.DiagonalSixPairs

/-! Cardinality of all cell projectors from the six possible sector bases. -/
@[expose] public section
noncomputable section
namespace DiagonalSix.Model
open Matrix Finset
open scoped BigOperators
variable (g : Model)

def rays (k : Tri) : Finset M := by
  classical
  exact (Finset.univ.filter (fun x : Idx × Idx => g.occurs k x.1 x.2)).image
    (fun x => g.p x.1 x.2)

def bases (k : Tri) : Finset (Finset M) := by
  classical exact (g.rays k).image (pair (g.X k))

def allRays : Finset M := by
  classical exact Finset.univ.image (fun x : Idx × Idx => g.p x.1 x.2)

theorem mem_rays (k : Tri) (q : M) :
    q∈g.rays k ↔ ∃ r c, g.occurs k r c ∧ g.p r c=q := by
  classical simp [rays]

theorem mem_bases (k : Tri) (T : Finset M) :
    T∈g.bases k ↔ ∃ r c, g.occurs k r c ∧ pair (g.X k) (g.p r c)=T := by
  classical
  simp only [bases,Finset.mem_image,g.mem_rays]
  constructor
  · rintro ⟨q,⟨r,c,h,rfl⟩,e⟩; exact ⟨r,c,h,e⟩
  · rintro ⟨r,c,h,e⟩; exact ⟨_,⟨r,c,h,rfl⟩,e⟩

theorem bases_bound (k : Tri) : (g.bases k).card≤2 := by
  classical
  by_contra! large
  obtain ⟨A,B,D,hA,hB,hD,ab,ad,bd⟩ := Finset.two_lt_card_iff.mp large
  let C : Finset M → Colors.Code := fun x => if x=A then 1 else if x=B then 2 else 3
  have nz (x) : C x≠0 := by dsimp [C]; split <;> first | decide | split <;> decide
  have hit {t} (ht : t∈g.bases k) : Colors.present (g.code k C) (C t) := by
    obtain ⟨r,c,ok,eq⟩ := (g.mem_bases k t).mp ht
    exact ⟨r,c,by simp [code,ok,eq]⟩
  apply Colors.at_most_two _ k (g.code_valid k C nz)
  · simpa [C] using hit hA
  · simpa [C,ab.symm] using hit hB
  · simpa [C,ad.symm,bd.symm] using hit hD

theorem cell_ne (r c : Idx) : g.p r c≠0 := by
  intro h
  have t := g.trace r c
  simp [h] at t

theorem exists_sector (r c : Idx) : ∃ k, g.occurs k r c := by
  by_contra! h
  have z (k) : g.p r c*g.X k=0 := (g.binary r c k).resolve_right (h k)
  have q := congrArg (g.p r c * ·) g.Xtotal
  simp only [Finset.mul_sum,z,Finset.sum_const_zero,mul_one] at q
  exact g.cell_ne r c q.symm

theorem sector_disjoint (i j : Tri) (h : i≠j) : Disjoint (g.rays i) (g.rays j) := by
  rw [Finset.disjoint_left]
  intro q a b
  obtain ⟨r,c,hi,eq⟩ := (g.mem_rays i q).mp a
  obtain ⟨r',c',hj,eq'⟩ := (g.mem_rays j q).mp b
  have hi' : q*g.X i=q := eq ▸ hi
  have hj' : q*g.X j=q := eq' ▸ hj
  have z : q=0 := by
    calc
      _ = q*g.X j := hj'.symm
      _ = (q*g.X i)*g.X j := by rw [hi']
      _ = 0 := by rw [mul_assoc,g.Xorth i j h,mul_zero]
  exact g.cell_ne r c (eq.trans z)

theorem complement_mem (k : Tri) (q : M) (hm : q∈g.rays k) : g.X k-q∈g.rays k := by
  obtain ⟨r,c,hc,eq⟩ := (g.mem_rays k q).mp hm
  obtain ⟨a,b,_,hs,h⟩ := g.slice (g.row r) (g.trace r) k (fun j => g.binary r j k)
  rcases (h c).mp hc with e | e
  · subst c
    apply (g.mem_rays k _).mpr
    refine ⟨r,b,(h b).mpr (Or.inr rfl),?_⟩
    rw [← eq,← hs]; abel
  · subst c
    apply (g.mem_rays k _).mpr
    refine ⟨r,a,(h a).mpr (Or.inl rfl),?_⟩
    rw [← eq,← hs]; abel

theorem complement_ne (k : Tri) (q : M) (hm : q∈g.rays k) : q≠g.X k-q := by
  obtain ⟨r,c,hc,rfl⟩ := (g.mem_rays k q).mp hm
  intro e
  have eq : g.X k=g.p r c+g.p r c := by linear_combination (norm := abel) -e
  unfold occurs at hc
  rw [eq,mul_add,g.idem] at hc
  apply g.cell_ne r c
  linear_combination (norm := abel) hc

theorem pair_of_member (H p q : M) (h : q∈pair H p) : pair H q=pair H p := by
  classical
  simp only [pair,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with e | e
  · rw [e]
  · rw [e]
    apply pair_same
    abel

theorem rays_card (k : Tri) : (g.rays k).card=2*(g.bases k).card := by
  classical
  have union : (g.bases k).biUnion id=g.rays k := by
    ext q
    simp only [Finset.mem_biUnion,id_eq]
    constructor
    · rintro ⟨s,hs,hq⟩
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
      rcases (show q=p ∨ q=g.X k-p by simpa [pair] using hq) with e | e
      · exact e ▸ hp
      · exact e ▸ g.complement_mem k p hp
    · intro h
      exact ⟨pair (g.X k) q,Finset.mem_image.mpr ⟨q,h,rfl⟩,by simp [pair]⟩
  have dis : (↑(g.bases k) : Set (Finset M)).PairwiseDisjoint id := by
    intro s hs t ht hst
    change Disjoint s t
    rw [Finset.disjoint_left]
    intro q qs qt
    obtain ⟨a,_,ea⟩ := Finset.mem_image.mp hs
    obtain ⟨b,_,eb⟩ := Finset.mem_image.mp ht
    subst s; subst t
    exact hst ((pair_of_member _ _ q qs).symm.trans (pair_of_member _ _ q qt))
  have two (s) (h : s∈g.bases k) : s.card=2 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    simp [pair,g.complement_ne k p hp]
  rw [← union,Finset.card_biUnion dis]
  change (∑ s ∈ g.bases k, s.card)=_
  rw [Finset.sum_congr rfl two]
  simp [mul_comm]

theorem count : g.allRays.card=6 ∨ g.allRays.card=8 ∨ g.allRays.card=10 ∨ g.allRays.card=12 := by
  classical
  have union : Finset.univ.biUnion g.rays=g.allRays := by
    ext q
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,allRays,Finset.mem_image,g.mem_rays]
    constructor
    · rintro ⟨k,r,c,_,eq⟩; exact ⟨(r,c),eq⟩
    · rintro ⟨⟨r,c⟩,eq⟩
      obtain ⟨k,h⟩ := g.exists_sector r c
      exact ⟨k,r,c,h,eq⟩
  have dis : (↑(Finset.univ : Finset Tri) : Set Tri).PairwiseDisjoint g.rays :=
    fun i _ j _ h => g.sector_disjoint i j h
  have pos (k) : 0<(g.bases k).card := by
    apply Finset.card_pos.mpr
    obtain ⟨a,_,_,_,h⟩ := g.slice (g.row (0,0)) (g.trace (0,0)) k (fun j => g.binary (0,0) j k)
    exact ⟨_,(g.mem_bases k _).mpr ⟨(0,0),a,(h a).mpr (Or.inl rfl),rfl⟩⟩
  have tot := Finset.card_biUnion dis
  rw [union,Fin.sum_univ_three,g.rays_card,g.rays_card,g.rays_card] at tot
  have p0:=pos 0
  have p1:=pos 1
  have p2:=pos 2
  have b0:=g.bases_bound 0
  have b1:=g.bases_bound 1
  have b2:=g.bases_bound 2
  omega

#print axioms count
end DiagonalSix.Model
