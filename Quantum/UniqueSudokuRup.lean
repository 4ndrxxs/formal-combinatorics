module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic

/-! A proof-producing check of reverse unit propagation with explicit pivots.
Clauses are bit sets of signed literals. A hint gives an earlier clause and the
only literal in it allowed to be true. A final hint has code zero. -/
@[expose] public section
namespace UniqueSudoku.Rup

def bit (i : ℕ) := 1 <<< i
def flip (i : ℕ) := if i%2=0 then i+1 else i-1
def inside (a b : ℕ) : Bool := a &&& b == a

def Holds (truth : ℕ → Prop) (c : ℕ) : Prop := ∃ i,c.testBit i=true ∧ truth i
def FalseOn (truth : ℕ → Prop) (a : ℕ) : Prop := ∀ i,a.testBit i=true → ¬truth i

@[simp] theorem bit_test (a i : ℕ) : (bit a).testBit i = decide (a=i) := by
  simp [bit,Nat.one_shiftLeft,Nat.testBit_two_pow]

private theorem inside_mem {a b : ℕ} (h : inside a b=true) {i : ℕ} (hi : a.testBit i=true) :
    b.testBit i=true := by
  have eq : a &&& b=a := beq_iff_eq.mp h
  have v := congrArg (fun z : ℕ => z.testBit i) eq
  simpa [Nat.testBit_and,hi] using v

theorem not_holds_iff (truth : ℕ→Prop) (m : ℕ) : ¬Holds truth m ↔ FalseOn truth m := by
  simp [Holds,FalseOn]

private theorem forced {truth : ℕ→Prop} {a c v : ℕ}
    (h : Holds truth c) (f : FalseOn truth a) (sub : inside c (a ||| bit v)=true) : truth v := by
  obtain ⟨i,mem,t⟩:=h
  have m:=inside_mem sub mem
  simp only [Nat.testBit_or,bit_test,Bool.or_eq_true,decide_eq_true_eq] at m
  rcases m with k|eq
  · exact (f i k t).elim
  · exact eq ▸ t

private theorem insert_false {truth : ℕ→Prop} {a v : ℕ} (f : FalseOn truth a) (nv : ¬truth v) :
    FalseOn truth (a ||| bit v) := by
  intro i h
  simp only [Nat.testBit_or,bit_test,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with k|eq
  · exact f i k
  · exact eq ▸ nv

def run (db : ℕ→ℕ) (bound : ℕ) (avoid : ℕ) : List (ℕ×ℕ) → Bool
  | [] => false
  | (j,0)::_ => decide (j<bound) && inside (db j) avoid
  | (j,v+1)::rest =>
    decide (j<bound) && inside (db j) (avoid ||| bit v) &&
      run db bound (avoid ||| bit (flip v)) rest

theorem run_contradiction (truth : ℕ→Prop) (opposite : ∀ l,truth l → ¬truth (flip l))
    (db : ℕ→ℕ) (bound : ℕ) (valid : ∀ j<bound,Holds truth (db j)) (steps : List (ℕ×ℕ)) (avoid : ℕ)
    (f : FalseOn truth avoid) (h : run db bound avoid steps=true) : False := by
  induction steps generalizing avoid with
  | nil => simp [run] at h
  | cons head rest ih =>
    obtain ⟨j,c⟩:=head
    cases c with
    | zero =>
      simp only [run,Bool.and_eq_true,decide_eq_true_eq] at h
      obtain ⟨i,hi,t⟩:=valid j h.1
      exact f i (inside_mem h.2 hi) t
    | succ v =>
      simp only [run,Bool.and_eq_true,decide_eq_true_eq] at h
      have t:=forced (valid j h.1.1) f h.1.2
      exact ih _ (insert_false f (opposite v t)) h.2

theorem derive (truth : ℕ→Prop) (opposite : ∀ l,truth l → ¬truth (flip l))
    (db : ℕ→ℕ) (bound : ℕ) (valid : ∀ j<bound,Holds truth (db j)) (steps : List (ℕ×ℕ))
    (h : run db bound (db bound) steps=true) : Holds truth (db bound) := by
  by_contra no
  exact run_contradiction truth opposite db bound valid steps _ ((not_holds_iff _ _).mp no) h

theorem empty_false (truth : ℕ→Prop) : ¬Holds truth 0 := by simp [Holds]

end UniqueSudoku.Rup
