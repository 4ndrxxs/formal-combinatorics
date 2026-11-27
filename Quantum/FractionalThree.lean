module
public import Quantum.FractionalLayouts

/-! The size-three witness is a single rectangle trade in a cyclic Sudoku.
Every one of its 27 lines has the prescribed nine probability rows. -/
@[expose] public section
noncomputable section
namespace FractionalThree
open Function Equiv QuantumSudoku FractionalPolygons.Sudoku FractionalLayouts

abbrev J := Index (Fin 3)
def number : J≃Fin 9 := finProdFinEquiv

def label (x : Site (Fin 3)) : Fin 9 :=
  ![![2,0,0,3,4,5,6,7,8],![3,4,5,6,7,8,0,2,0],![6,7,8,0,2,0,3,4,5],
    ![0,2,3,4,5,6,7,8,0],![4,5,6,7,8,0,2,0,3],![7,8,0,2,0,3,4,5,6],
    ![0,3,4,5,6,7,8,0,2],![5,6,7,8,0,2,0,3,4],![8,0,2,0,3,4,5,6,7]]
    (number x.1) (number x.2)

def repair (d : Direction) (k i : J) : Fin 9 :=
  if label (arrange d (k,i))=0 ∧ ∃ j : Fin 9, j<number i ∧ label (arrange d (k,number.symm j))=0
  then 1 else label (arrange d (k,i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem repair_injective : ∀ d k, Injective (repair d k) := by
  intro d; cases d <;> decide +kernel

def repaired (d : Direction) (k : J) : J≃Fin 9 := Equiv.ofBijective _
  ((Fintype.bijective_iff_injective_and_card _).mpr ⟨repair_injective d k,by decide +kernel⟩)

def loop7 (k : ℕ) : Site (Fin 3) :=
  let q : Fin 9 × Fin 9 :=
    ![(5,4),(5,2),(0,2),(0,1),(8,1),(8,3),(7,4),(5,4)] ⟨k%8,Nat.mod_lt _ (by decide)⟩
  (number.symm q.1,number.symm q.2)

theorem loop7_edges : ∀ k : Fin 7, Adjacent (loop7 k) (loop7 (k.val+1)) := by
  unfold Adjacent; decide +kernel
theorem loop7_flags : ∀ k : Fin 8, label (loop7 k)=0 := by decide +kernel

def witness (B : FractionalDenseBasis.Basis J) : Marked (Fin 3) := by
  apply Classical.choice
  let incl : Fin 4 ↪ Fin 9 := Fin.castLEEmb (by omega)
  obtain ⟨ρ,hρ⟩ := align (incl.trans number.symm.toEmbedding) B.special
  let e := number.symm.trans ρ
  have e0 : e 0=B.special 0 := hρ 0
  have e1 : e 1=B.special 1 := hρ 1
  refine ⟨{
    B := B
    p := fun x => dist B (e (label x))
    lines := ?_
    length := 7
    odd := by decide
    short := by decide
    walk := loop7
    closes := rfl
    edges := fun k hk => loop7_edges ⟨k,hk⟩
    flags := ?_ }⟩
  · intro d k
    refine ⟨(repaired d k).trans e,fun i => ?_⟩
    change dist B (e (label (arrange d (k,i))))=dist B (e (repair d k i))
    unfold repair
    split
    · rename_i h
      rw [h.1,e0,e1]
      exact funext B.sameA
    · rfl
  · intro k hk
    rw [loop7_flags ⟨k,by omega⟩,e0]

#print axioms witness
end FractionalThree
