module

public import Quantum.SudokuCollections
public import Quantum.SmallEight
public import Quantum.SmallTen

/-! Two-square blocks supply the required small-dimensional ray unions. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku.SmallLayers
open QuantumCertificate Collections

private def restrict {n c : ℕ} (A : PartialArray (n+n) n c (evenMask n))
    (e : Fin n ↪ Fin (n+n)) (h : ∀ i j, evenMask n (e i,e j)=true) : Full n where
  entry p := A.entry (e p.1,e p.2)
  nz p := A.nz ⟨_,h p.val.1 p.val.2⟩
  unit p := A.unit ⟨_,h p.val.1 p.val.2⟩
  rows i j k _ _ ne := A.rows (e i) (e j) (e k) (h _ _) (h _ _) (e.injective.ne ne)
  cols i j k _ _ ne := A.cols (e i) (e j) (e k) (h _ _) (h _ _) (e.injective.ne ne)

theorem diagonal_split {n c : ℕ} (h : Nonempty (PartialArray (n+n) n c (evenMask n))) :
    ∃ a b : Full n, (a.rays ∪ b.rays).ncard=c := by
  obtain ⟨A⟩ := h
  let l := Fin.castAddEmb n (n:=n)
  let r := Fin.natAddEmb n (m:=n)
  have left (i j : Fin n) : evenMask n (l i,l j)=true := by simp [l,evenMask]
  have right (i j : Fin n) : evenMask n (r i,r j)=true := by simp [r,evenMask]
  let a := restrict A l left
  let b := restrict A r right
  have he : a.rays ∪ b.rays = A.rays := by
    ext q
    constructor
    · rintro (⟨⟨⟨i,j⟩,hij⟩,rfl⟩|⟨⟨⟨i,j⟩,hij⟩,rfl⟩)
      · exact ⟨⟨_,left i j⟩,rfl⟩
      · exact ⟨⟨_,right i j⟩,rfl⟩
    · rintro ⟨⟨⟨i,j⟩,hij⟩,rfl⟩
      by_cases hi : i.val<n
      · have hj : j.val<n := by simpa [evenMask,hi] using hij
        exact Or.inl ⟨⟨(⟨i.val,hi⟩,⟨j.val,hj⟩),rfl⟩,rfl⟩
      · have hj : ¬j.val<n := by simpa [evenMask,hi] using hij
        let x : Fin n := ⟨i.val-n,by have := i.isLt; omega⟩
        let y : Fin n := ⟨j.val-n,by have := j.isLt; omega⟩
        have hx : r x=i := by apply Fin.ext; change n+(i.val-n)=i.val; omega
        have hy : r y=j := by apply Fin.ext; change n+(j.val-n)=j.val; omega
        apply Or.inr
        refine ⟨⟨(x,y),rfl⟩,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨1,by simp [b,restrict,hx,hy]⟩
  exact ⟨a,b,he ▸ A.count⟩

theorem of_partial_pair {n c : ℕ} (h : Nonempty (PartialArray (n+n) n c (evenMask n))) :
    Attain n 2 c := by
  obtain ⟨a,b,hab⟩ := diagonal_split h
  exact of_two a b hab

private theorem bound (n : ℕ) (a : Full n) : a.rays.ncard≤n*n := by
  classical
  let f := fun p : Cell n => Projectivization.mk ℂ (a.entry p) (a.nz ⟨p,rfl⟩)
  have he : a.rays=Set.range f := by
    ext q
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.val,rfl⟩
    · rintro ⟨p,rfl⟩
      exact ⟨⟨p,rfl⟩,rfl⟩
  rw [he,← Set.image_univ]
  simpa [Cell,Nat.card_eq_fintype_card] using
    Set.ncard_image_le (f:=f) (s:=Set.univ) Set.finite_univ

theorem five_top : Attain 5 1 25 := by
  obtain ⟨a,b,hab⟩ := diagonal_split (n:=5) (c:=50) SmallEven.B10_50.block
  have ha := bound 5 a
  have hb := bound 5 b
  have hu := Set.ncard_union_le a.rays b.rays
  rw [hab] at hu
  have eq : a.rays.ncard=25 := by omega
  refine ⟨fun _ => a,?_⟩
  have hs : states (fun _ : Fin 1 => a)=a.rays := by
    ext z
    exact ⟨fun hz => (state_mem.mp hz).choose_spec,fun hz => state_mem.mpr ⟨0,hz⟩⟩
  rwa [hs]

private def seeds4 : List ℕ := [4,6,7,9,13,15,19,23,25,29,30,31,32]

private theorem seed4 {x : ℕ} (h : x∈seeds4) : Attain 4 2 x := by
  simp only [seeds4,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact of_partial_pair (n:=4) SmallEven.B8_4.block
  · exact of_partial_pair (n:=4) SmallEven.B8_6.block
  · exact of_partial_pair (n:=4) SmallEven.B8_7.block
  · exact of_partial_pair (n:=4) SmallEven.B8_9.block
  · exact of_partial_pair (n:=4) SmallEven.B8_13.block
  · exact of_partial_pair (n:=4) SmallEven.B8_15.block
  · exact of_partial_pair (n:=4) SmallEven.B8_19.block
  · exact of_partial_pair (n:=4) SmallEven.B8_23.block
  · exact of_partial_pair (n:=4) SmallEven.B8_25.block
  · exact of_partial_pair (n:=4) SmallEven.B8_29.block
  · exact of_partial_pair (n:=4) SmallEven.B8_30.block
  · exact of_partial_pair (n:=4) SmallEven.B8_31.block
  · exact of_partial_pair (n:=4) SmallEven.B8_32.block

private def seeds5 : List ℕ := [5,7,8,9,11,13,14,21,23,25,29,33,37,41,44,45,47,49,50]

private theorem seed5 {x : ℕ} (h : x∈seeds5) : Attain 5 2 x := by
  simp only [seeds5,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact of_partial_pair (n:=5) SmallEven.B10_5.block
  · exact of_partial_pair (n:=5) SmallEven.B10_7.block
  · exact of_partial_pair (n:=5) SmallEven.B10_8.block
  · exact of_partial_pair (n:=5) SmallEven.B10_9.block
  · exact of_partial_pair (n:=5) SmallEven.B10_11.block
  · exact of_partial_pair (n:=5) SmallEven.B10_13.block
  · exact of_partial_pair (n:=5) SmallEven.B10_14.block
  · exact of_partial_pair (n:=5) SmallEven.B10_21.block
  · exact of_partial_pair (n:=5) SmallEven.B10_23.block
  · exact of_partial_pair (n:=5) SmallEven.B10_25.block
  · exact of_partial_pair (n:=5) SmallEven.B10_29.block
  · exact of_partial_pair (n:=5) SmallEven.B10_33.block
  · exact of_partial_pair (n:=5) SmallEven.B10_37.block
  · exact of_partial_pair (n:=5) SmallEven.B10_41.block
  · exact of_partial_pair (n:=5) SmallEven.B10_44.block
  · exact of_partial_pair (n:=5) SmallEven.B10_45.block
  · exact of_partial_pair (n:=5) SmallEven.B10_47.block
  · exact of_partial_pair (n:=5) SmallEven.B10_49.block
  · exact of_partial_pair (n:=5) SmallEven.B10_50.block

private def sums (L : List ℕ) := L.flatMap (fun a => L.map (a+·))

private theorem pair {n z : ℕ} (hn : 2≤n) {L : List ℕ} (h : z∈sums L)
    (seed : ∀ {x}, x∈L → Attain n 2 x) : Attain n 4 z := by
  obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp h
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
  exact append hn (by decide : 0<2) (seed ha) (seed hb)

private theorem cover4 : ∀ c : Fin 65, 4≤c.val → c.val≠5 →
    c.val∈seeds4 ∨ c.val∈sums seeds4 := by decide +kernel

private theorem cover5 : ∀ c : Fin 126, 5≤c.val → c.val≠6 →
    c.val∈seeds5 ∨ c.val∈sums seeds5 ∨ c.val∈(sums seeds5).map (·+25) := by decide +kernel

theorem four (c : ℕ) (lo : 4≤c) (hi : c≤64) (hole : c≠5) : Attain 4 4 c := by
  rcases cover4 ⟨c,by omega⟩ lo hole with single|two
  · exact pad (by decide : 0<2) (by decide) (seed4 single)
  · exact pair (by decide) two seed4

theorem five (c : ℕ) (lo : 5≤c) (hi : c≤125) (hole : c≠6) : Attain 5 5 c := by
  rcases cover5 ⟨c,by omega⟩ lo hole with single|two|three
  · exact pad (by decide : 0<2) (by decide) (seed5 single)
  · exact pad (by decide : 0<4) (by decide) (pair (by decide) two seed5)
  · obtain ⟨a,ha,he⟩ := List.mem_map.mp three
    change a+25=c at he
    subst c
    exact append (by decide) (by decide : 0<1) (pair (by decide) ha seed5) five_top

#print axioms four
#print axioms five
end QuantumSudoku.SmallLayers
