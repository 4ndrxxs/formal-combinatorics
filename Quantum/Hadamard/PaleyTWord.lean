import Quantum.Hadamard.PaleyT271

/-! A packed word of signed coordinate vectors constructs four disjoint circulants.
Only its integer dot sums need to be supplied to this certificate. -/
namespace Hadamard.PeriodicT
open Finset
namespace Word

def symbol (w i : ℕ) : Fin 8 :=
  ⟨(w >>> (3*i))%8,Nat.mod_lt _ (by decide)⟩

def dot (w p u : ℕ) : ℕ → ℤ
  | 0 => 0
  | j+1 => dot w p u j + letterDot (symbol w j) (symbol w ((j+u)%p))

def verify (w p a : ℕ) : ℕ → Bool
  | 0 => true
  | i+1 => verify w p a i && (dot w p (a+i) p == if a+i=0 then (p:ℤ) else 0)

theorem verified {w p a n t : ℕ} (h : verify w p a n=true) (lo : a≤t) (hi : t<a+n) :
    dot w p t p = if t=0 then (p:ℤ) else 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [verify,Bool.and_eq_true,beq_iff_eq] at h
    by_cases e : t=a+n
    · simpa [e] using h.2
    · exact ih h.1 (by omega)

private theorem dot_sum (w p t n : ℕ) : dot w p t n =
    ∑ j ∈ range n, letterDot (symbol w j) (symbol w ((j+t)%p)) := by
  induction n with
  | zero => simp [dot]
  | succ n ih => simp [dot,sum_range_succ,ih]

private theorem agree : ∀ a b : Fin 8, letterDot a b = ∑ c, component c a * component c b := by decide +kernel
private theorem ternary : ∀ a : Fin 8, ∀ c : Fin 4,
    component c a = 0 ∨ component c a = 1 ∨ component c a = -1 := by decide +kernel
private theorem partition : ∀ a : Fin 8, ∃! c : Fin 4, component c a ≠ 0 := by unfold ExistsUnique; decide +kernel

def system {p : ℕ} [NeZero p] (w:ℕ)
    (checked : ∀ s : Fin p, dot w p s.val p=if s.val=0 then (p:ℤ) else 0) : System p where
  entry c j := component c (symbol w j.val)
  ternary c j := ternary _ _
  partition j := partition _
  correlation t := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j:Fin p, letterDot (symbol w j.val) (symbol w ((j.val+t.val)%p)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (agree _ _).symm
      _ = dot w p t.val p := by
        rw [dot_sum]
        exact Fin.sum_univ_eq_sum_range (fun j => letterDot (symbol w j) (symbol w ((j+t.val)%p))) p
      _ = _ := checked t

end Word
end Hadamard.PeriodicT

