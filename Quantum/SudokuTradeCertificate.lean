module
public import Quantum.SudokuTradeClauses

/-! A finite proof of uniqueness from the certified physical constraint language.
Each referenced learned clause must precede its use. -/
@[expose] public section
namespace SudokuTrade.Certificate
open UniqueSudoku.Rup SudokuTrade.SAT
variable [C : Config] [L : Laws]
include L

def db (count : ℕ) (tag learned : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j<count then tagMask (tag j) else learned (j-count)

def check (count : ℕ) (tag learned : ℕ → ℕ) (steps : ℕ → List (ℕ × ℕ)) (i : ℕ) : Bool :=
  let D := db count tag learned
  run D (count+i) (D (count+i)) (steps i)

theorem force (c n : ℕ) (tag learned : ℕ → ℕ) (steps : ℕ → List (ℕ × ℕ))
    (hn : 0<n) (checks : ∀ i, i<n → check c tag learned steps i=true)
    (empty : db c tag learned (c+n-1)=0) (g : Active) (good : Good g) : ∀ r i,g 0 r i=i := by
  by_contra diff
  let D := db c tag learned
  have valid (j : ℕ) (hj : j<c+n) : Holds (truth g) (D j) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      by_cases first : j<c
      · simpa [D,db,first] using tag_correct good diff (tag j)
      · let i:=j-c
        have small : i<n := by dsimp [i]; omega
        have eq : c+i=j := by dsimp [i]; omega
        apply derive _ (opposite g) D j (fun k hk => ih k hk (by omega)) (steps i)
        simpa only [check,eq,D] using checks i small
  have bad := valid (c+n-1) (by omega)
  change Holds (truth g) (db c tag learned (c+n-1)) at bad
  rw [empty] at bad
  exact empty_false _ bad

omit L

def Interval (f : ℕ → Bool) (a b : ℕ) : Prop := ∀ (i : ℕ), (a ≤ i) → (i < b) → f i = true

theorem interval_fin (f : ℕ → Bool) (a b : ℕ)
    (h : ∀ j : Fin (b-a), f (a+j.val)=true) : Interval f a b := by
  intro i ha hb
  have hh := h ⟨i-a,by omega⟩
  change f (a+(i-a))=true at hh
  rwa [show a+(i-a)=i by omega] at hh

theorem interval_join {f : ℕ → Bool} {a m b : ℕ} (l : Interval f a m) (r : Interval f m b) :
    Interval f a b := by
  intro i ha hb
  by_cases h : i<m
  · exact l i ha h
  · exact r i (by omega) hb

end SudokuTrade.Certificate
