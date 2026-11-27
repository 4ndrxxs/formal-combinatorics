import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NormNum

/-! Extremal five-by-five supports. Cyclic shifts of a permutation partition
the board. Comparing two permutations which switch two rows gives the
rectangle identity in the equality case. -/

namespace PermanentSupports
open Finset
abbrev I := Fin 5
abbrev Grid := I → I → Fin 2

def hits (G : Grid) (p : Equiv.Perm I) : ℕ := ∑ i, (G i (p i) : ℕ)
def size (G : Grid) : ℕ := ∑ i, ∑ j, (G i j : ℕ)

private def shift (p : Equiv.Perm I) (t : I) : Equiv.Perm I := (Equiv.addRight t).trans p

private theorem shifts (G : Grid) (p : Equiv.Perm I) : ∑ t, hits G (shift p t) = size G := by
  unfold hits size
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact ((Equiv.addLeft i).trans p).sum_comp (fun j ↦ (G i j : ℕ))

private theorem shift_zero (p : Equiv.Perm I) : shift p 0 = p := by ext i; simp [shift]

theorem size_le (G : Grid) (d : ℕ) (bound : ∀ p, hits G p ≤ d) : size G ≤ 5*d := by
  rw [← shifts G (Equiv.refl I)]
  calc
    _ ≤ ∑ _ : I, d := Finset.sum_le_sum fun i _ ↦ bound _
    _ = _ := by simp

theorem exists_three (G : Grid) (big : 10 < size G) (bound : ∀ p, hits G p ≤ 3) :
    ∃ p, hits G p = 3 := by
  by_contra! smaller
  have h := size_le G 2 (fun p ↦ by have := bound p; have := smaller p; omega)
  omega

private theorem uniform (G : Grid) (maximal : size G = 15) (bound : ∀ p, hits G p ≤ 3)
    (p : Equiv.Perm I) : hits G p = 3 := by
  by_contra neq
  have lt : hits G p < 3 := lt_of_le_of_ne (bound p) neq
  have h : ∑ t : I, hits G (shift p t) < ∑ _ : I, (3 : ℕ) :=
    Finset.sum_lt_sum (fun t _ ↦ bound _) ⟨0,mem_univ _,by simpa [shift_zero] using lt⟩
  simp [shifts,maximal] at h

private theorem prescribe {i k j l : I} (ik : i ≠ k) (jl : j ≠ l) :
    ∃ p : Equiv.Perm I, p i = j ∧ p k = l := by
  let q := Equiv.swap i j
  have qi : q i = j := Equiv.swap_apply_left i j
  have distinct : j ≠ q k := by rw [← qi]; exact fun eq ↦ ik (q.injective eq)
  refine ⟨q.trans (Equiv.swap (q k) l),?_,?_⟩
  · simp [qi,Equiv.swap_apply_of_ne_of_ne distinct jl]
  · simp

private theorem split_sum (f : I → ℕ) {i k : I} (ik : i ≠ k) :
    f i + f k + ∑ a ∈ ((univ.erase i).erase k), f a = ∑ a, f a := by
  rw [Nat.add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨ik.symm,mem_univ _⟩),
    Finset.add_sum_erase _ _ (mem_univ i)]

private theorem rectangle (G : Grid) (all : ∀ p, hits G p = 3) (i k j l : I) :
    (G i j : ℕ) + G k l = G i l + (G k j : ℕ) := by
  by_cases ik : i = k
  · subst k; omega
  by_cases jl : j = l
  · subst l; rfl
  obtain ⟨p,pi,pk⟩ := prescribe ik jl
  let q := (Equiv.swap i k).trans p
  have qi : q i = l := by simp [q,pk]
  have qk : q k = j := by simp [q,pi]
  have same : ∑ a ∈ ((univ.erase i).erase k), (G a (p a) : ℕ) =
      ∑ a ∈ ((univ.erase i).erase k), (G a (q a) : ℕ) := by
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨ak,hi⟩ := mem_erase.mp ha
    have ai := (mem_erase.mp hi).1
    simp [q,Equiv.swap_apply_of_ne_of_ne ai ak]
  have h := (all p).trans (all q).symm
  unfold hits at h
  rw [← split_sum (fun a ↦ (G a (p a) : ℕ)) ik,
    ← split_sum (fun a ↦ (G a (q a) : ℕ)) ik, pi, pk, qi, qk, same] at h
  exact Nat.add_right_cancel h

/-- With at most three supported entries on every permutation and fifteen
occupied cells, the board consists of three full rows or three full columns. -/
theorem extremal (G : Grid) (maximal : size G = 15) (bound : ∀ p, hits G p ≤ 3) :
    ((∀ i j, G i j = G i 0) ∧ ∑ i, (G i 0 : ℕ) = 3) ∨
      ((∀ i j, G i j = G 0 j) ∧ ∑ j, (G 0 j : ℕ) = 3) := by
  have all := uniform G maximal bound
  have diag := all (Equiv.refl I)
  by_cases rows : ∀ i j, G i j = G i 0
  · left
    exact ⟨rows,by simpa only [hits,rows] using diag⟩
  push Not at rows
  obtain ⟨r,j,diff⟩ := rows
  obtain ⟨f,t,hf,ht⟩ : ∃ f t : I, (G r f : ℕ) = 0 ∧ (G r t : ℕ) = 1 := by
    by_cases lt : (G r 0 : ℕ) < G r j
    · exact ⟨0,j,by omega,by omega⟩
    · exact ⟨j,0,by omega,by omega⟩
  have van (i : I) : (G i f : ℕ) = 0 := by have h := rectangle G all r i f t; omega
  have cols (i j : I) : G i j = G 0 j := by
    apply Fin.ext
    have a := rectangle G all r i f j
    have b := rectangle G all r 0 f j
    have := van i
    have := van 0
    omega
  right
  exact ⟨cols,by simpa only [hits,Equiv.refl_apply,cols] using diag⟩

#print axioms size_le
#print axioms exists_three
#print axioms extremal
end PermanentSupports
