import Quantum.Hadamard.Basic

/-! A sign matrix with constant row sum one and one prescribed value for its
off-diagonal Gram entries extends a normalized modular Hadamard matrix. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m : ℕ} {I : Type*} [Fintype I]

structure Rows (m : ℕ) (I : Type*) [Fintype I] (c : ZMod m) where
  entry : RowMatrix m I
  sign : ∀ i j, Sign (entry i j)
  row : ∀ i, ∑ j, entry i j=1
  off : ∀ i k, i≠k → ∑ j, entry i j*entry k j=c

structure Extender (m : ℕ) (I : Type*) [Fintype I] (r : ZMod m)
    extends Rows m I (1-r) where
  dim : (Fintype.card I : ZMod m)=1
  pos : 0<Fintype.card I

variable {r : ZMod m}

private theorem extend_core {n : ℕ} (D : Extender m I r) (h : AtOrder m (n+1))
    (res : ((n+1 : ℕ) : ZMod m)=r) : AtOrder m (n+Fintype.card I) := by
  classical
  obtain ⟨A,g⟩:=h
  let C := normalize A (0 : Fin (n+1))
  have cgood : Good C := g.normalize 0
  have first (j : Fin (n+1)) : C 0 j=1 := (normalized_first g 0 j).1
  have col (i : Fin (n+1)) : C i 0=1 := (normalized_first g 0 i).2
  have row (i : Fin n) : ∑ j : Fin n, C i.succ j.succ= -1 := by
    have hh := cgood.ortho i.succ 0 i.succ_ne_zero
    rw [Fin.sum_univ_succ] at hh
    simp only [first,col,mul_one] at hh
    linear_combination hh
  have off (i k : Fin n) (ne : i≠k) : ∑ j : Fin n, C i.succ j.succ*C k.succ j.succ= -1 := by
    have hh:=cgood.ortho i.succ k.succ (fun eq => ne ((Fin.succ_injective n) eq))
    rw [Fin.sum_univ_succ,col,col,one_mul] at hh
    linear_combination hh
  let K : RowMatrix m (Fin n⊕I)
    | .inl i,.inl j => C i.succ j.succ
    | .inr i,.inr j => D.entry i j
    | _,_ => 1
  have good : Good K := by
    constructor
    · intro i j
      rcases i with i|i <;> rcases j with j|j
      · exact cgood.sign _ _
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact D.sign _ _
    · intro i k ne
      rw [Fintype.sum_sum_type]
      rcases i with i|i <;> rcases k with k|k
      · have nd : i≠k := fun eq => ne (congrArg Sum.inl eq)
        simpa [K,off i k nd,D.dim]
      · simp [K,row,D.row]
      · simp [K,row,D.row]
      · have nd : i≠k := fun eq => ne (congrArg Sum.inr eq)
        simp [K,D.off i k nd]
        push_cast at res
        linear_combination res
  exact of_card good (by simp)

theorem Extender.grow {n : ℕ} (D : Extender m I r) (hn : 0<n) (h : AtOrder m n)
    (res : (n:ZMod m)=r) : AtOrder m (n+(Fintype.card I-1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  convert extend_core D h res using 1
  have := D.pos
  omega

theorem Extender.iterate {n : ℕ} (D : Extender m I r) (hn : 0<n) (h : AtOrder m n)
    (res : (n:ZMod m)=r) (t : ℕ) : AtOrder m (n+t*(Fintype.card I-1)) := by
  have step : ((Fintype.card I-1 : ℕ) : ZMod m)=0 := by
    rw [Nat.cast_sub (by have := D.pos; omega),Nat.cast_one,D.dim,sub_self]
  induction t with
  | zero => simpa using h
  | succ t ih =>
    have hh := D.grow (by omega : 0<n+t*(Fintype.card I-1)) ih (by push_cast; rw [step,res];ring)
    simpa [Nat.succ_mul,Nat.add_assoc] using hh

/-- A circulant certificate can check each nonzero shift against the first row. -/
def cyclic {v : ℕ} [NeZero v] (f : ZMod v → ZMod m) (sg : ∀ x,Sign (f x))
    (one : ∑ x, f x=1) (corr : ∀ d : ZMod v, d≠0 → ∑ x,f x*f (x+d)=1-r)
    (dim : (v:ZMod m)=1) : Extender m (ZMod v) r where
  entry i j := f (j-i)
  sign _ _ := sg _
  row i := ((Equiv.subRight i).sum_comp f).trans one
  off i k ne := by
    have hh := (Equiv.subRight i).sum_comp (fun x => f x*f (x+(i-k)))
    have shift (x : ZMod v) : x-i+(i-k)=x-k := by abel
    change (∑ x, f (x-i)*f (x-i+(i-k))) = _ at hh
    simpa only [shift] using hh.trans (corr (i-k) (sub_ne_zero.mpr ne))
  dim := by simpa using dim
  pos := Fintype.card_pos

#print axioms Extender.grow
end HadamardMod
