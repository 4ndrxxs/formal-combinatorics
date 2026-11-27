module
public import Quantum.SudokuTradeData
public import Quantum.FractionalBlockPlacements

/-! Row, column and block permutations of the explicit classical completion. -/
@[expose] public section
namespace SudokuTrade
variable [C : Config] [L : Laws]
open Laws
include L
open FractionalLayouts QuantumSudoku

def slice {α : Type*} (T : I → I → I → α) (d : Direction) (k : I) (p : Pair) : α :=
  match d with
  | .row => T k p.1 p.2
  | .column => T p.1 k p.2
  | .block => T p.1 p.2 k

def word (r c t : I) : Pair := (symb r c,t-typ (symb r c) r)

def pos (d : Direction) (k : I) (w : Pair) : Pair :=
  match d with
  | .row => (col w.1 k,typ w.1 k+w.2)
  | .column =>
    let r:=colRow w.1 k
    (r,typ w.1 r+w.2)
  | .block =>
    let r:=typRow w.1 (k-w.2)
    (r,col w.1 r)

@[simp] theorem word_pos (d : Direction) (k : I) (w : Pair) : slice word d k (pos d k w)=w := by
  rcases w with ⟨a,b⟩
  cases d with
  | row => simp [slice,word,pos]
  | column =>
    have h : symb (colRow a k) k=a := by simpa using symb_col a (colRow a k)
    simp [slice,word,pos,h]
  | block => simp [slice,word,pos]

@[simp] theorem pos_word (d : Direction) (k : I) (p : Pair) : pos d k (slice word d k p)=p := by
  rcases p with ⟨a,b⟩
  cases d with
  | row => simp [slice,word,pos]
  | column =>
    have h : colRow (symb a k) k=a := by simpa using inv_col (symb a k) a
    simp [slice,word,pos,h]
  | block => simp [slice,word,pos]

def arranged (d : Direction) (k : I) : Pair ≃ Pair :=
  ⟨pos d k,slice word d k,word_pos d k,pos_word d k⟩

def baseline (r c : Pair) : Pair := word r.2 c.2 (r.1+c.1)

def Ordinary (f : Pair → Pair → Pair) : Prop :=
  (∀ r,Function.Bijective (f r)) ∧
  (∀ c,Function.Bijective (fun r => f r c)) ∧
  ∀ x y,Function.Bijective (fun p : Pair => f (x,p.1) (y,p.2))

def rowEquiv (x : I) : Pair ≃ Pair where
  toFun p := (p.2,x+p.1)
  invFun p := (p.2-x,p.1)
  left_inv p := by rcases p with ⟨a,b⟩; simp
  right_inv p := by rcases p with ⟨a,b⟩; simp

def colEquiv (y : I) : Pair ≃ Pair where
  toFun p := (p.2,p.1+y)
  invFun p := (p.2-y,p.1)
  left_inv p := by rcases p with ⟨a,b⟩; simp
  right_inv p := by rcases p with ⟨a,b⟩; simp

theorem baseline_ordinary : Ordinary baseline := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨x,r⟩
    exact ((rowEquiv x).trans (arranged .row r).symm).bijective
  · rintro ⟨y,c⟩
    exact ((colEquiv y).trans (arranged .column c).symm).bijective
  · intro x y
    exact (arranged .block (x+y)).symm.bijective

def activeCell (x r : I) (i : Color) : Pair × Pair :=
  ((x,r),(typ (cap i) r-x,col (cap i) r))

@[simp] theorem baseline_active (x r : I) (i : Color) :
    baseline (activeCell x r i).1 (activeCell x r i).2=activeAxis i := by
  simp [baseline,activeCell,word,activeAxis]

/-- A given physical position with an active planted symbol is the indicated active cell. -/
theorem recover_cell (r c : Pair) (i : Color) (hw : baseline r c=activeAxis i) :
    activeCell r.1 r.2 i=(r,c) := by
  rcases r with ⟨x,r⟩
  rcases c with ⟨y,c⟩
  have h : symb r c=cap i := congrArg Prod.fst hw
  have d : (x+y)-typ (symb r c) r=0 := congrArg Prod.snd hw
  have qt : x+y=typ (cap i) r := by simpa [h,sub_eq_zero] using d
  have qc : col (cap i) r=c := by rw [←h,col_symb]
  simp [activeCell,qc,←qt]

/-- Every exterior value is printed. Within the four active coordinates exactly
the cells already equal to their planted reference ray are printed. -/
def puzzle (r c : Pair) : Option Pair :=
  let w:=baseline r c
  if h : w.1.val<4 then
    if w.2=0 ∧ ray r.2 ⟨w.1.val,h⟩≠refRay ⟨w.1.val,h⟩ then none else some w
  else some w

def ClassicalCompletes (p : Pair → Pair → Option Pair) (f : Pair → Pair → Pair) : Prop :=
  Ordinary f ∧ ∀ r c k, p r c=some k → f r c=k

theorem baseline_completes : ClassicalCompletes puzzle baseline := by
  refine ⟨baseline_ordinary,?_⟩
  intro r c k h
  dsimp only [puzzle] at h
  split at h
  · split at h
    · contradiction
    · exact Option.some.inj h
  · exact Option.some.inj h

theorem clue_exterior {r c : Pair} (h : ¬∃ i, baseline r c=activeAxis i) :
    puzzle r c=some (baseline r c) := by
  dsimp only [puzzle]
  split
  · rename_i small
    split
    · rename_i hw
      exfalso
      apply h
      refine ⟨⟨_,small⟩,Prod.ext ?_ hw.1⟩
      exact Fin.ext rfl
    · rfl
  · rfl

theorem clue_active {x r : I} {i : Color} (eq : ray r i = refRay i) :
    puzzle (activeCell x r i).1 (activeCell x r i).2=some (activeAxis i) := by
  simp only [puzzle,baseline_active]
  simp [activeAxis,cap,activeCell,eq,i.isLt]

end SudokuTrade
