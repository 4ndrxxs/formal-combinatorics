module
public import Quantum.FractionalCyclicLift
public import Quantum.Exact
public import Quantum.FractionalBlockPlacements

/-! Data for a four-color change in a cyclic Sudoku. A configuration consists of
finite permutations and integer coordinates for a four-dimensional ray chart. -/
@[expose] public section
namespace SudokuTrade
open QuantumCertificate FractionalLayouts

abbrev Color := Fin 4

class Config where
  side : ℕ
  four : 4 ≤ side
  col : Fin side → Fin side → Fin side
  colRow : Fin side → Fin side → Fin side
  typ : Fin side → Fin side → Fin side
  typRow : Fin side → Fin side → Fin side
  symb : Fin side → Fin side → Fin side
  ray : Fin side → Color → Fin 24
  refRay : Color → Fin 24
  num : Fin 24 → Color → IQ

variable [C : Config]

abbrev I := Fin C.side
abbrev Pair := I × I

instance side_ne : NeZero C.side := ⟨by have := C.four; omega⟩

abbrev col := C.col
abbrev colRow := C.colRow
abbrev typ := C.typ
abbrev typRow := C.typRow
abbrev symb := C.symb
abbrev ray := C.ray
abbrev refRay := C.refRay
abbrev num := C.num

def cap (i : Color) : I := ⟨i.val,by have := C.four; omega⟩
def activeAxis (i : Color) : Pair := (cap i,0)

theorem cap_inj : Function.Injective cap := fun _ _ eq => Fin.ext (congrArg (fun a : I => a.val) eq)
theorem axis_inj : Function.Injective activeAxis := fun _ _ eq => cap_inj (congrArg Prod.fst eq)

def sourceRow (d : Direction) (k : I) (i : Color) : I :=
  match d with
  | .row => k
  | .column => colRow (cap i) k
  | .block => typRow (cap i) k

class Laws : Prop where
  symb_col : ∀ h r, symb r (col h r)=h
  col_symb : ∀ h r, col (symb r h) r=h
  col_inv : ∀ h r, col h (colRow h r)=r
  inv_col : ∀ h r, colRow h (col h r)=r
  typ_inv : ∀ h r, typ h (typRow h r)=r
  inv_typ : ∀ h r, typRow h (typ h r)=r
  ref_num : ∀ i j, num (refRay i) j = (if j=i then (4,0) else (0,0))
  tested_frames : ∀ d k i j,
    gram 1 (num (ray (sourceRow d k i) i)) (num (ray (sourceRow d k j) j)) =
    if i=j then (16,0) else (0,0)

attribute [simp] Laws.symb_col Laws.col_symb Laws.col_inv Laws.inv_col Laws.typ_inv Laws.inv_typ

end SudokuTrade
