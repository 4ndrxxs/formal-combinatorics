module
public import Quantum.FractionalPartialBasis

/-! An odd sum of Sudoku constraints over F₂ rules out every ordinary
completion of a partial grid when every unprinted cell cancels. -/
@[expose] public section
noncomputable section
namespace PartialSudoku
open QuantumSudoku FractionalLayouts Finset
open scoped BigOperators

variable {n m : ℕ} [NeZero n] (L : Layout n m)
abbrev R := ZMod 2

def bit (f : Sites n→Sites n→Sites n) (r c : Sites n) : R :=
  if f r c=L.symbol (.inl 0) then 1 else 0
def mass (f : Sites n→Sites n→Sites n) (r c t : Fin n) : R :=
  ∑ x : Fin n,bit L f (x,r) (t-x,c)

theorem one {f : Sites n→Sites n→Sites n} (hf : ClassicalCompletes L.puzzle f)
    (d : Direction) (k : Sites n) :
    (∑ j : Sites n,bit L f (arrange d (k,j)).1 (arrange d (k,j)).2)=1 := by
  let e := Equiv.ofBijective (fun j : Sites n => f (arrange d (k,j)).1 (arrange d (k,j)).2) (hf.1 d k)
  simpa [e,bit] using e.sum_comp (fun a : Sites n => if a=L.symbol (.inl 0) then (1:R) else 0)

def view (x : Fin n) : Sites n ≃ Sites n where
  toFun p := (p.2-x,p.1)
  invFun p := (p.2,p.1+x)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp
def mirror (t : Fin n) : Fin n ≃ Fin n where
  toFun x := t-x
  invFun y := t-y
  left_inv := fun x => sub_sub_cancel t x
  right_inv := fun x => sub_sub_cancel t x

theorem mass_col (f : Sites n→Sites n→Sites n) (r c t : Fin n) :
    mass L f r c t=∑ y : Fin n, bit L f (t-y,r) (y,c) := by
  have h := (mirror t).sum_comp (fun x : Fin n => bit L f (x,r) (t-x,c))
  simpa [mirror,mass,sub_sub_cancel] using h.symm

theorem fibre_sum {f : Sites n→Sites n→Sites n} (hf : ClassicalCompletes L.puzzle f)
    (d : Direction) (k : Fin n) : (∑ p : Sites n,slice (mass L f) d k p)=(n:R) := by
  cases d with
  | row =>
    simp only [slice,mass]
    rw [sum_comm]
    have localSum (x : Fin n) : (∑ p : Sites n,bit L f (x,k) (p.2-x,p.1))=1 :=
      ((view x).sum_comp (fun j => bit L f (x,k) j)).trans (one L hf .row (x,k))
    simp [localSum]
  | column =>
    simp only [slice,mass_col]
    rw [sum_comm]
    have localSum (y : Fin n) : (∑ p : Sites n,bit L f (p.2-y,p.1) (y,k))=1 :=
      ((view y).sum_comp (fun j => bit L f j (y,k))).trans (one L hf .column (y,k))
    simp [localSum]
  | block =>
    simp only [slice,mass]
    rw [sum_comm]
    have localSum (x : Fin n) : (∑ p : Sites n,bit L f (x,p.1) (k-x,p.2))=1 :=
      one L hf .block (x,k-x)
    simp [localSum]

theorem outside_zero {f : Sites n→Sites n→Sites n} (hf : ClassicalCompletes L.puzzle f)
    {r c t : Fin n} {u : Fin m} (h : L.label r c t=.inr u) : mass L f r c t=0 := by
  apply sum_eq_zero
  intro x _
  have eq : x+(t-x)=t := by simpa [add_comm] using sub_add_cancel t x
  have clue : L.puzzle (x,r) (t-x,c)=some (L.symbol (.inr u)) := by simp [Layout.puzzle,Layout.given,eq,h]
  simp [bit,hf.2 _ _ _ clue]

structure Cut (L : Layout n m) where
  row : Fin n→R
  col : Fin n→R
  block : Fin n→R
  on_active : ∀ r c t, match L.label r c t with
    | .inl _ => row r+col c+block t=0 | .inr _ => True
  odd : ((∑ r,row r)+(∑ c,col c)+(∑ t,block t))*(n:R)≠0

theorem Cut.impossible (C : Cut L) : ¬ ∃ f,ClassicalCompletes L.puzzle f := by
  rintro ⟨f,hf⟩
  let M := mass L f
  have zeros (r c t : Fin n) : (C.row r+C.col c+C.block t)*M r c t=0 := by
    cases h : L.label r c t with
    | inl i =>
      have hh := C.on_active r c t
      rw [h] at hh
      rw [show C.row r+C.col c+C.block t=0 from hh,zero_mul]
    | inr u => rw [show M r c t=0 from outside_zero L hf h,mul_zero]
  have colSwap : (∑ r,∑ c,∑ t,C.col c*M r c t)=(∑ c,∑ r,∑ t,C.col c*M r c t) := sum_comm
  have blockSwap : (∑ r,∑ c,∑ t,C.block t*M r c t)=(∑ t,∑ r,∑ c,C.block t*M r c t) := by
    calc
      _=(∑ r,∑ t,∑ c,C.block t*M r c t) := by apply sum_congr rfl; intro r _; exact sum_comm
      _=_ := sum_comm
  have total (d : Direction) (k : Fin n) : (∑ p : Sites n,slice M d k p)=(n:R) := fibre_sum L hf d k
  have rr (r : Fin n) : (∑ c,∑ t,M r c t)=(n:R) := by simpa [slice,Fintype.sum_prod_type] using total .row r
  have cc (c : Fin n) : (∑ r,∑ t,M r c t)=(n:R) := by simpa [slice,Fintype.sum_prod_type] using total .column c
  have bb (t : Fin n) : (∑ r,∑ c,M r c t)=(n:R) := by simpa [slice,Fintype.sum_prod_type] using total .block t
  have z : (∑ r,∑ c,∑ t,(C.row r+C.col c+C.block t)*M r c t)=0 := by simp [zeros]
  simp only [add_mul,Finset.sum_add_distrib] at z
  rw [colSwap,blockSwap] at z
  simp only [←Finset.mul_sum,rr,cc,bb,←Finset.sum_mul,←add_mul] at z
  exact C.odd z

theorem cut_counterexample (C : Cut L) :
    ∃ (p : Sites n→Sites n→Option (Sites n)) (v : Grid (Fin n)),
      QuantumCompletes p v ∧ ¬ ∃ f,ClassicalCompletes p f :=
  ⟨L.puzzle,L.board,L.quantum,C.impossible L⟩

#print axioms cut_counterexample
end PartialSudoku
