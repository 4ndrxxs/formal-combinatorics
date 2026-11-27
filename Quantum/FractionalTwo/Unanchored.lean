module
public import Quantum.FractionalTwo.Complete

/-! The Sudoku symmetry group is transitive on cell-symbol triples. An
arbitrary fractional board therefore reduces to the normalized case. -/
@[expose] public section
noncomputable section
namespace FractionalTwo
open Function Finset FractionalBinary
open scoped BigOperators

def xor4 (a b : Fin 4) := Fin.ofNat 4 (a.val ^^^ b.val)
theorem xor4_involutive : ∀ a b : Fin 4,xor4 a (xor4 a b)=b := by decide +kernel
def xorEquiv (a : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := xor4 a
  invFun := xor4 a
  left_inv := xor4_involutive a
  right_inv := xor4_involutive a

@[simp] theorem loc_atom : ∀ s d,loc (atom s d)=s := by decide +kernel
@[simp] theorem digit_atom : ∀ s d,digit (atom s d)=d := by decide +kernel
@[simp] theorem atom_roundtrip : ∀ a,atom (loc a) (digit a)=a := by decide +kernel

def moveSite (a : A) (s : S) : S := (xor4 (loc a).1 s.1,xor4 (loc a).2 s.2)
def move (a b : A) : A := atom (moveSite a (loc b)) (xor4 (digit a) (digit b))
theorem move_zero : ∀ a,move a 0=a := by decide +kernel
theorem move_involutive : ∀ a b,move a (move a b)=b := by decide +kernel

def moveLine (a : A) (l : Fin 12) : Fin 12 := Fin.ofNat 12 (
  if l.val<4 then (xor4 (loc a).1 (Fin.ofNat 4 l.val)).val else
  if l.val<8 then 4+(xor4 (loc a).2 (Fin.ofNat 4 l.val)).val else
  8+((l.val%4) ^^^ (2*((loc a).1.val/2)+(loc a).2.val/2)))

def lineMovePosition (a : A) (l : Fin 12) : Fin 4 :=
  if l.val<4 then (loc a).2 else if l.val<8 then (loc a).1 else
    Fin.ofNat 4 (2*((loc a).1.val%2)+(loc a).2.val%2)

theorem move_line : ∀ a l i,
    moveSite a (line l i)=line (moveLine a l) (xor4 (lineMovePosition a l) i) := by decide +kernel

theorem move_total {t : A→ℝ} (ht : Fractional t) (a : A) : Fractional (fun b => t (move a b)) := by
  refine ⟨fun b => ht.nonneg _,fun u => ?_⟩
  by_cases hu : u.val<16
  · let s : S := (Fin.ofNat 4 (u.val/4),Fin.ofNat 4 u.val)
    let u' : Fin 64 := Fin.ofNat 64 (4*(moveSite a s).1.val+(moveSite a s).2.val)
    have inside : ∀ (s : S) (d : Fin 4),house (Fin.ofNat 64 (4*s.1.val+s.2.val)) d=atom s d := by decide +kernel
    have he (i : Fin 4) : move a (house u i)=house u' (xorEquiv (digit a) i) := by
      rw [show house u i=atom s i by simp [house,s,hu],inside]
      simp [move,xorEquiv]
    simp_rw [he]
    exact (Equiv.sum_comp (xorEquiv (digit a)) (fun i => t (house u' i))).trans (ht.total _)
  · let l := Fin.ofNat 12 ((u.val-16)/4)
    let d := Fin.ofNat 4 u.val
    let l' := moveLine a l
    let d' := xor4 (digit a) d
    let u' := Fin.ofNat 64 (16+4*l'.val+d'.val)
    have outside : ∀ (l : Fin 12) (d i : Fin 4),house (Fin.ofNat 64 (16+4*l.val+d.val)) i=atom (line l i) d := by decide +kernel
    have he (i : Fin 4) : move a (house u i)=house u' (xorEquiv (lineMovePosition a l) i) := by
      rw [show house u i=atom (line l i) d by simp [house,l,d,hu],outside]
      simp [move,move_line,xorEquiv,l',d']
    simp_rw [he]
    exact (Equiv.sum_comp (xorEquiv (lineMovePosition a l)) (fun i => t (house u' i))).trans (ht.total _)

def Proper (f : S→Fin 4) : Prop := ∀ l,Injective (fun i => f (line l i))
def moveSolution (a : A) (f : S→Fin 4) (s : S) : Fin 4 := xor4 (digit a) (f (moveSite a s))

theorem proper_move {f : S→Fin 4} (hf : Proper f) (a : A) : Proper (moveSolution a f) := by
  intro l i j h
  change xorEquiv (digit a) _=xorEquiv (digit a) _ at h
  have hh := (xorEquiv (digit a)).injective h
  change f (moveSite a (line l i))=f (moveSite a (line l j)) at hh
  rw [move_line,move_line] at hh
  exact (xorEquiv _).injective (hf _ hh)

/-- The nonnegative unit-sum relaxation detects impossible ordinary 4-by-4 puzzles. -/
theorem integral_extension (t : A→ℝ) (ht : Fractional t) : ∃ f : S→Fin 4,Proper f ∧ Agrees t f := by
  by_cases unit : ∃ a,t a=1
  · obtain ⟨a,ha⟩ := unit
    obtain ⟨j,hj⟩ := anchored_extension _ (move_total ht a) (by simpa [move_zero] using ha)
    refine ⟨moveSolution a (candidate j),proper_move (fun l i s => candidate_injective j l i s) a,?_⟩
    intro b hb
    have he := hj (move a b) (by simpa [move_involutive] using hb)
    simpa [moveSolution,move,xor4_involutive] using congrArg (xor4 (digit a)) he
  · exact ⟨candidate 0,fun l i j => candidate_injective 0 l i j,fun a h => (unit ⟨a,h⟩).elim⟩

#print axioms integral_extension
end FractionalTwo
