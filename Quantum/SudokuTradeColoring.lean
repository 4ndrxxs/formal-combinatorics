module
public import Quantum.SudokuTradeAtlas

/-! Translating any ordinary completion into four active colors on the actual
sheets. Row, column, and block constraints retain all sheet offsets. -/
@[expose] public section
namespace SudokuTrade
variable [C : Config] [L : Laws]
open Laws
include L

abbrev Active := I→I→Color→Color

def columnChoice (g : Active) (z c : I) (i : Color) : Color :=
  let r:=colRow (cap i) c
  g (z+typ (cap i) r) r i

def blockChoice (g : Active) (x t : I) (i : Color) : Color :=
  g x (typRow (cap i) t) i

structure Good (g : Active) : Prop where
  row : ∀ x r,Function.Injective (g x r)
  col : ∀ z c,Function.Injective (columnChoice g z c)
  block : ∀ x t,Function.Injective (blockChoice g x t)
  pinned : ∀ x r i,ray r i=refRay i → g x r i=i

def shift (a : I) (g : Active) : Active := fun x r i => g (a+x) r i

theorem Good.shift {g : Active} (h : Good g) (a : I) : Good (SudokuTrade.shift a g) where
  row x r := h.row (a+x) r
  col z c := by
    intro i j eq
    apply h.col (a+z) c
    simpa only [columnChoice,SudokuTrade.shift,add_assoc] using eq
  block x t := h.block (a+x) t
  pinned x r i := h.pinned (a+x) r i

private theorem good_values {f : Pair→Pair→Pair} (h : ClassicalCompletes puzzle f)
    (x r : I) (i : Color) : ∃ j, f (activeCell x r i).1 (activeCell x r i).2=activeAxis j := by
  let p := (activeCell x r i).2
  change ∃ j, f (x,r) p=activeAxis j
  by_contra outside
  obtain ⟨q,bq⟩ := (baseline_ordinary.1 (x,r)).2 (f (x,r) p)
  have exterior : ¬∃ j,baseline (x,r) q=activeAxis j := by simpa [bq] using outside
  have same := h.2 _ _ _ (clue_exterior exterior)
  have pos : q=p := (h.1.1 (x,r)).1 (same.trans bq)
  apply outside
  exact ⟨i,bq.symm.trans (pos ▸ baseline_active x r i)⟩

private theorem colors_injective {S : Type*} (own ref : S→Pair) (h : Function.Injective own)
    (place : Color→S) (g : Color→Color) (a : ∀ i,own (place i)=activeAxis (g i))
    (b : ∀ i,ref (place i)=activeAxis i) : Function.Injective g := by
  intro i j eq
  have same := h ((a i).trans ((congrArg activeAxis eq).trans (a j).symm))
  apply axis_inj
  exact (b i).symm.trans ((congrArg ref same).trans (b j))

def columnRow (z c : I) (i : Color) : Pair :=
  let r:=colRow (cap i) c
  (z+typ (cap i) r,r)

theorem column_cell (z c : I) (i : Color) :
    activeCell (columnRow z c i).1 (columnRow z c i).2 i = (columnRow z c i,(-z,c)) := by
  simp [activeCell,columnRow]

def blockPosition (t : I) (i : Color) : Pair :=
  let r:=typRow (cap i) t
  (r,col (cap i) r)

theorem block_cell (x t : I) (i : Color) :
    activeCell x (blockPosition t i).1 i = ((x,(blockPosition t i).1),(t-x,(blockPosition t i).2)) := by
  simp [activeCell,blockPosition]

theorem active_of_completion {f : Pair→Pair→Pair} (h : ClassicalCompletes puzzle f) :
    ∃ g : Active, Good g ∧ ∀ x r i,f (activeCell x r i).1 (activeCell x r i).2=activeAxis (g x r i) := by
  choose g matched using good_values h
  refine ⟨g,⟨?_,?_,?_,?_⟩,matched⟩
  · intro x r
    exact colors_injective (f (x,r)) (baseline (x,r)) (h.1.1 _).1
      (fun i => (activeCell x r i).2) (g x r) (matched x r) (baseline_active x r)
  · intro z c
    apply colors_injective (fun p => f p (-z,c)) (fun p => baseline p (-z,c)) (h.1.2.1 _).1
      (columnRow z c) (columnChoice g z c)
    · intro i
      have v := matched (columnRow z c i).1 (columnRow z c i).2 i
      rwa [column_cell] at v
    · intro i
      have v := baseline_active (columnRow z c i).1 (columnRow z c i).2 i
      rwa [column_cell] at v
  · intro x t
    apply colors_injective (fun p : Pair => f (x,p.1) (t-x,p.2))
      (fun p : Pair => baseline (x,p.1) (t-x,p.2)) (h.1.2.2 x (t-x)).1
      (blockPosition t) (blockChoice g x t)
    · intro i
      have v := matched x (blockPosition t i).1 i
      rwa [block_cell] at v
    · intro i
      have v := baseline_active x (blockPosition t i).1 i
      rwa [block_cell] at v
  · intro x r i pin
    exact axis_inj ((matched x r i).symm.trans (h.2 _ _ _ (clue_active pin)))

theorem unique_of_forced (force : ∀ g : Active,Good g → ∀ r i,g 0 r i=i)
    {f : Pair→Pair→Pair} (h : ClassicalCompletes puzzle f) : f=baseline := by
  obtain ⟨g,proper,matched⟩:=active_of_completion h
  have eq (x r : I) (i : Color) : g x r i=i := by
    simpa [shift] using force _ (proper.shift x) r i
  funext r c
  by_cases inner : ∃ i,baseline r c=activeAxis i
  · obtain ⟨i,hi⟩:=inner
    have hm:=matched r.1 r.2 i
    rw [recover_cell r c i hi,eq] at hm
    exact hm.trans hi.symm
  · exact h.2 _ _ _ (clue_exterior inner)

end SudokuTrade
