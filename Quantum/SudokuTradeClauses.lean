module
public import Quantum.SudokuTradeColoring
public import Quantum.UniqueSudokuRup

/-! The clause language for the physical Sudoku instance. A clause may come
only from the four choices of a cell, one of the three actual Sudoku units,
a printed active clue, or the assumption that the zero sheet differs. -/
@[expose] public section
namespace SudokuTrade.SAT
variable [C : Config] [L : Laws]
open UniqueSudoku.Rup
include L

def var (x r : I) (i h : Color) : ℕ := ((x.val*C.side+r.val)*4+i.val)*4+h.val
def lit (x r : I) (i h : Color) : ℕ := 2*var x r i h

def atomTruth (g : Active) (v : ℕ) : Prop :=
  g (Fin.ofNat C.side (v/16/C.side)) (Fin.ofNat C.side (v/16)) (Fin.ofNat 4 (v/4))=Fin.ofNat 4 v

def truth (g : Active) (l : ℕ) : Prop := if l%2=0 then atomTruth g (l/2) else ¬atomTruth g (l/2)

theorem opposite (g : Active) (l : ℕ) : truth g l → ¬truth g (flip l) := by
  by_cases e : l%2=0
  · have ne : (l+1)%2≠0 := by omega
    have div : (l+1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,ne,div]
  · have yes : (l-1)%2=0 := by omega
    have div : (l-1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,yes,div]

theorem truth_flip (g : Active) (l : ℕ) : truth g (flip l) ↔ ¬truth g l := by
  by_cases e : l%2=0
  · have ne : (l+1)%2≠0 := by omega
    have div : (l+1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,ne,div]
  · have yes : (l-1)%2=0 := by omega
    have div : (l-1)/2=l/2 := by omega
    simp [truth,UniqueSudoku.Rup.flip,e,yes,div]

@[simp] theorem truth_lit (g : Active) (x r : I) (i h : Color) : truth g (lit x r i h) ↔ g x r i=h := by
  have even : (2*var x r i h)%2=0 := by omega
  have div : 2*var x r i h/2=var x r i h := by omega
  rw [truth,lit,if_pos even,div]
  unfold atomTruth
  have layers : var x r i h / 16 = r.val+C.side*x.val := by
    unfold var
    rw [mul_comm x.val,add_comm (C.side*x.val)]
    omega
  have x' : Fin.ofNat C.side (var x r i h/16/C.side)=x := by
    apply Fin.ext
    change _%C.side=x.val
    rw [layers,Nat.add_mul_div_left _ _ (NeZero.pos C.side),Nat.div_eq_of_lt r.isLt]
    simp [Nat.mod_eq_of_lt x.isLt]
  have r' : Fin.ofNat C.side (var x r i h/16)=r := by
    apply Fin.ext
    change _%C.side=r.val
    rw [layers]
    simp [Nat.mod_eq_of_lt r.isLt]
  have i' : Fin.ofNat 4 (var x r i h/4)=i := by apply Fin.ext; change _%4=i.val; unfold var; omega
  have h' : Fin.ofNat 4 (var x r i h)=h := by apply Fin.ext; change _%4=h.val; unfold var; omega
  rw [x',r',i',h']

def groupLit (d : ℕ) (x k : I) (h i : Color) : ℕ :=
  match d with
  | 0 => lit x k h i
  | 1 => lit x k i h
  | 2 => let r:=colRow (cap i) k
         lit (x+typ (cap i) r) r i h
  | _ => lit x (typRow (cap i) k) i h

private theorem perm_unique {f : Color→Color} (hf : Function.Injective f) (h : Color) :
    ∃! i,f i=h := by
  obtain ⟨j,eq⟩ := (Finite.injective_iff_surjective.mp hf) h
  exact ⟨j,eq,fun y yh => hf (yh.trans eq.symm)⟩

theorem one_in_group {g : Active} (good : Good g) (d : ℕ) (x k : I) (h : Color) :
    ∃! i,truth g (groupLit d x k h i) := by
  cases d with
  | zero => simp [groupLit]
  | succ d => cases d with
    | zero => simpa [groupLit] using perm_unique (good.row x k) h
    | succ d => cases d with
      | zero => simpa [groupLit,columnChoice] using perm_unique (good.col x k) h
      | succ d => simpa [groupLit,blockChoice] using perm_unique (good.block x k) h

def mask : List ℕ→ℕ
  | [] => 0
  | n::ns => bit n ||| mask ns

@[simp] theorem mask_mem (ns : List ℕ) (v : ℕ) : (mask ns).testBit v=true ↔ v∈ns := by
  induction ns with
  | nil => simp [mask]
  | cons a r ih =>
    simp only [mask,Nat.testBit_or,Bool.or_eq_true,bit_test,decide_eq_true_eq,ih,List.mem_cons]
    rw [eq_comm (a:=a) (b:=v)]

theorem holds_mask (g : Active) (ns : List ℕ) : Holds (truth g) (mask ns) ↔ ∃ v∈ns,truth g v := by
  simp [Holds]

def denyZero : List ℕ := (List.finRange C.side).flatMap fun r =>
  (List.finRange 4).map fun i => flip (lit 0 r i i)

def encode (d : ℕ) (x k : I) (h : Color) (a b : ℕ) : ℕ :=
  let G:=groupLit d x k h
  if d<4 then
    if a=4 then mask (List.ofFn G)
    else
      let i:=Fin.ofNat 4 a
      let j:=Fin.ofNat 4 b
      if i=j then mask [G i,flip (G i)] else mask [flip (G i),flip (G j)]
  else if d=4 then
    if ray k h=refRay h then bit (lit x k h h) else mask [G h,flip (G h)]
  else mask denyZero

theorem taut (g : Active) (v : ℕ) : Holds (truth g) (mask [v,flip v]) := by
  rw [holds_mask]
  by_cases h : truth g v
  · exact ⟨v,by simp,h⟩
  · exact ⟨flip v,by simp,(truth_flip _ _).mpr h⟩

theorem base_correct {g : Active} (good : Good g) (diff : ¬∀ r i,g 0 r i=i)
    (d : ℕ) (x k : I) (h : Color) (a b : ℕ) : Holds (truth g) (encode d x k h a b) := by
  dsimp only [encode]
  split
  · split
    · rw [holds_mask]
      obtain ⟨i,hi,_⟩:=one_in_group good d x k h
      exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩
    · split
      · exact taut _ _
      · rename_i ne
        rw [holds_mask]
        obtain ⟨j,hj,uniq⟩ := one_in_group good d x k h
        by_cases s : truth g (groupLit d x k h (Fin.ofNat 4 a))
        · have no : ¬truth g (groupLit d x k h (Fin.ofNat 4 b)) :=
            fun t => ne ((uniq _ s).trans (uniq _ t).symm)
          exact ⟨_,by simp,(truth_flip _ _).mpr no⟩
        · exact ⟨_,by simp,(truth_flip _ _).mpr s⟩
  · split
    · split
      · rename_i p
        exact ⟨_,by simp,(truth_lit _ _ _ _ _).mpr (good.pinned x k h p)⟩
      · exact taut _ _
    · push Not at diff
      obtain ⟨r,i,ne⟩:=diff
      rw [holds_mask]
      refine ⟨flip (lit 0 r i i),?_,(truth_flip _ _).mpr ?_⟩
      · exact List.mem_flatMap.mpr ⟨r,List.mem_finRange _,List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩⟩
      · simpa using ne

def tagMask (tag : ℕ) : ℕ :=
  encode (tag/100/C.side/C.side) (Fin.ofNat C.side (tag/100/C.side)) (Fin.ofNat C.side (tag/100))
    (Fin.ofNat 4 (tag/25)) (tag/5%5) (tag%5)

theorem tag_correct {g : Active} (good : Good g) (diff : ¬∀ r i,g 0 r i=i) (tag : ℕ) :
    Holds (truth g) (tagMask tag) := base_correct good diff _ _ _ _ _ _
end SudokuTrade.SAT
