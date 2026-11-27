module
public import Quantum.DiagonalSixTiles
public import Mathlib.Data.Fin.VecNotation

/-! A finite incidence lemma for one two-dimensional sector. Colors encode
arbitrary unordered orthogonal pairs in the sector. Zero indicates absence. -/
@[expose] public section
namespace DiagonalSix.Colors
open Finset
abbrev Code := BitVec 2

def line {α : Type} (f : α → Code) : Prop :=
  ∃ a b, a≠b ∧ f a=f b ∧ ∀ i, f i≠0 ↔ i=a ∨ i=b

def present (f : Idx → Idx → Code) (c : Code) : Prop := ∃ i j, f i j=c

def valid (f : Idx → Idx → Code) (k : Tri) : Prop :=
  (∀ r, line (f r)) ∧ (∀ c, line (fun r => f r c)) ∧
  line (fun r => f r r) ∧ line (fun r => f r (r.1,r.2.rev)) ∧
  (∀ i j : Tri, if label i j=k then (∀ a b : Bit, f (i,a) (j,b)=0)
    else line (fun ab : Pair => f (i,ab.1) (j,ab.2)))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def other (i j k : Tri) : Tri := label (label i k) j

def slot (k : Tri) (n : Fin 6) : Tri × Tri :=
  let p := (![ (0,1),(0,2),(2,2),(2,0),(1,0),(1,1) ] : Fin 6 → Tri × Tri) n
  (p.1+k,p.2+k)

theorem geom : ∀ k n, let p := slot k n
    label p.1 p.2≠k ∧
    (((slot k (n+1)=(p.1,other p.1 p.2 k)) ∧ (slot k (n-1)=(other p.2 p.1 k,p.2))) ∨
     ((slot k (n-1)=(p.1,other p.1 p.2 k)) ∧ (slot k (n+1)=(other p.2 p.1 k,p.2)))) := by
  decide +kernel

theorem exhaust : ∀ k i j, label i j≠k → ∃ n, slot k n=(i,j) := by decide +kernel

theorem opposite_diag : ∀ k n, n=2 ∨ n=5 → (slot k n).1=(slot k n).2 := by decide +kernel

theorem neighbor_allowed : ∀ k i j, label i j≠k →
    label i (other i j k)≠k ∧ label (other j i k) j≠k := by decide +kernel

def cyclic (z : Fin 6 → Code) (m : Code) : Prop :=
  (∀ n, z n=z (n+1) ∨ z n=z (n-1)) ∧
  (∀ n, n=2 ∨ n=5 → (z n=z (n+1) ∧ z n=z (n-1)) ∨ z n=m)

theorem cycle_check : ∀ a b c d e f m : Code,
    let z : Fin 6 → Code := ![a,b,c,d,e,f]
    cyclic z m → (∃ n, z n=1) → (∃ n, z n=2) → (∃ n, z n=3) → False := by
  unfold cyclic
  decide +kernel

theorem cycle_bound (z : Fin 6 → Code) (m : Code) (h : cyclic z m)
    (a : ∃ n, z n=1) (b : ∃ n, z n=2) (c : ∃ n, z n=3) : False := by
  have he : (![z 0,z 1,z 2,z 3,z 4,z 5] : Fin 6 → Code)=z := by
    funext n; fin_cases n <;> rfl
  have t := cycle_check (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) m
  dsimp only at t
  rw [he] at t
  exact t h a b c

def rowCover (a b : Pair) := ∀ t : Bit, t=a.1 ∨ t=b.1
def colCover (a b : Pair) := ∀ s : Bit, s=a.2 ∨ s=b.2

theorem shape : ∀ a b : Pair, a≠b → (rowCover a b ∨ colCover a b) ∧
    ((rowCover a b ∧ colCover a b) ∨ a.1=a.2 ∨ b.1=b.2) := by
  unfold rowCover colCover
  decide +kernel

theorem line_tag {α : Type} {f : α → Code} (h : line f) :
    ∃ z : Code, z≠0 ∧ (∀ i, f i≠0 → f i=z) ∧
      ∃ a b, a≠b ∧ f a=z ∧ f b=z := by
  obtain ⟨a,b,hab,he,hl⟩ := h
  refine ⟨f a,(hl a).mpr (Or.inl rfl),?_,a,b,hab,rfl,he.symm⟩
  intro i hi
  rcases (hl i).mp hi with h | h
  · rw [h]
  · rw [h,he]

def data (f : Idx → Idx → Code) (i j : Tri) (z : Code) : Prop :=
  z≠0 ∧ (∀ a : Pair, f (i,a.1) (j,a.2)≠0 → f (i,a.1) (j,a.2)=z) ∧
  ∃ a b : Pair, a≠b ∧ f (i,a.1) (j,a.2)=z ∧ f (i,b.1) (j,b.2)=z

/-- The six nonempty tiles of a sector form a cycle. Every tile shares its
color with a neighboring tile. Opposite diagonal tiles either share their
main-diagonal color or agree with both neighbors. -/
theorem at_most_two (f : Idx → Idx → Code) (k : Tri) (h : valid f k)
    (a1 : present f 1) (a2 : present f 2) (a3 : present f 3) : False := by
  classical
  rcases h with ⟨hr,hc,hm,_,ht⟩
  have get (i j : Tri) : ∃ z : Code, label i j≠k → data f i j z := by
    by_cases hn : label i j=k
    · exact ⟨0,fun hh => False.elim (hh hn)⟩
    · have t := ht i j
      rw [if_neg hn] at t
      obtain ⟨z,hz⟩ := line_tag t
      exact ⟨z,fun _ => hz⟩
  choose tag good using get
  obtain ⟨m,_,main,_⟩ := line_tag hm
  let z (n : Fin 6) := Function.uncurry tag (slot k n)
  have localFacts (i j : Tri) (hn : label i j≠k) :
      (tag i j=tag i (other i j k) ∨ tag i j=tag (other j i k) j) ∧
      (i=j → (tag i j=tag i (other i j k) ∧ tag i j=tag (other j i k) j) ∨ tag i j=m) := by
    obtain ⟨nz,_,a,b,hab,ha,hb⟩ := good i j hn
    obtain ⟨hrn,hcn⟩ := neighbor_allowed k i j hn
    have row (cov : rowCover a b) : tag i j=tag i (other i j k) := by
      obtain ⟨nt,_,u,_,_,hu,_⟩ := good i (other i j k) hrn
      obtain ⟨m1,_,line1,_⟩ := line_tag (hr (i,u.1))
      have ne := hu.symm ▸ nt
      have et := line1 _ ne
      rw [hu] at et
      rcases cov u.1 with h | h
      · rw [h] at line1
        exact (ha.symm.trans (line1 _ (ha.symm ▸ nz))).trans et.symm
      · rw [h] at line1
        exact (hb.symm.trans (line1 _ (hb.symm ▸ nz))).trans et.symm
    have col (cov : colCover a b) : tag i j=tag (other j i k) j := by
      obtain ⟨nt,_,u,_,_,hu,_⟩ := good (other j i k) j hcn
      obtain ⟨m1,_,line1,_⟩ := line_tag (hc (j,u.2))
      have ne := hu.symm ▸ nt
      have et := line1 _ ne
      rw [hu] at et
      rcases cov u.2 with h | h
      · rw [h] at line1
        exact (ha.symm.trans (line1 _ (ha.symm ▸ nz))).trans et.symm
      · rw [h] at line1
        exact (hb.symm.trans (line1 _ (hb.symm ▸ nz))).trans et.symm
    obtain ⟨hor,hdiag⟩ := shape a b hab
    refine ⟨hor.imp row col,?_⟩
    rintro rfl
    rcases hdiag with ⟨r,c⟩ | da | db
    · exact Or.inl ⟨row r,col c⟩
    · right; rw [da] at ha; exact ha.symm.trans (main _ (ha.symm ▸ nz))
    · right; rw [db] at hb; exact hb.symm.trans (main _ (hb.symm ▸ nz))
  have facts (n : Fin 6) :
      (z n=z (n+1) ∨ z n=z (n-1)) ∧
      (n=2 ∨ n=5 → (z n=z (n+1) ∧ z n=z (n-1)) ∨ z n=m) := by
    let p := slot k n
    obtain ⟨hn,neighbors⟩ := geom k n
    have hloc := localFacts p.1 p.2 hn
    rcases neighbors with ⟨hr,hc⟩ | ⟨hr,hc⟩
    · simp only [z,hr,hc,Function.uncurry_apply_pair]
      exact ⟨hloc.1,fun h => hloc.2 (opposite_diag k n h)⟩
    · simp only [z,hr,hc,Function.uncurry_apply_pair]
      exact ⟨hloc.1.symm,fun h => (hloc.2 (opposite_diag k n h)).imp And.symm id⟩
  have used (x : Code) (nx : x≠0) (w : present f x) : ∃ n, z n=x := by
    obtain ⟨⟨i,t⟩,⟨j,s⟩,eq⟩ := w
    have ncell : f (i,t) (j,s)≠0 := eq.symm ▸ nx
    have hn : label i j≠k := by
      intro bad
      have q := ht i j
      rw [if_pos bad] at q
      exact ncell (q t s)
    obtain ⟨n,hp⟩ := exhaust k i j hn
    exact ⟨n,by simpa only [z,hp,Function.uncurry_apply_pair] using
      ((good i j hn).2.1 (t,s) ncell).symm.trans eq⟩
  exact cycle_bound z m ⟨fun n => (facts n).1,fun n => (facts n).2⟩
    (used 1 (by decide) a1) (used 2 (by decide) a2) (used 3 (by decide) a3)

#print axioms at_most_two
end DiagonalSix.Colors
