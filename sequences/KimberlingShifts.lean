import KimberlingBlocks

namespace KimberlingMoses

/-- Positions of the selected A entry in consecutive blocks of seven, for the
four offsets appearing in the three conjectures in section 4. -/
def shiftPos (c n : ℕ) : ℕ :=
  if c = 0 then (if n%3=0 then 2 else 3) else
  if c = 2 then 4 else if c = 3 then 5 else if n%3=0 then 7 else 6

abbrev shiftA (c : ℕ) := blockA 6 (shiftPos c)
abbrev shiftB (c : ℕ) := blockB 6 (shiftPos c)

private theorem pos_add_three (c n : ℕ) : shiftPos c (n+3) = shiftPos c n := by simp [shiftPos]

private theorem shiftA_add (c n : ℕ) : shiftA c (n+9) = shiftA c n + 63 := by
  unfold shiftA blockA; have hp : shiftPos c (n+9) = shiftPos c n := by simp [shiftPos,Nat.add_mod]
  rw [hp]; omega

private theorem shiftB_add (c n : ℕ) : shiftB c (n+18) = shiftB c n + 21 := by
  unfold shiftB blockB
  rw [show (n+18)/6=n/6+3 by omega, show (n+18)%6=n%6 by omega, pos_add_three]; omega

theorem shift_solution (c : ℕ) (hc : c=0 ∨ c=2 ∨ c=3 ∨ c=5) :
    OffsetSolution 2 4 c (shiftA c) (shiftB c) where
  toComplementary := block_complementary 6 (by decide) _ (fun q => by unfold shiftPos; split_ifs <;> omega)
  initial := by rcases hc with rfl|rfl|rfl|rfl <;> decide
  equation n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases small : n < 9
      · interval_cases n <;> rcases hc with rfl|rfl|rfl|rfl <;> decide
      · let t := n-9
        have ht : n = t+9 := by dsimp [t]; omega
        have he := ih t (by dsimp [t]; omega)
        rw [ht, shiftA_add, show 2*(t+9)=2*t+18 by omega, show 4*(t+9)=4*t+18+18 by omega,
          shiftB_add, shiftB_add c (4*t+18), shiftB_add c (4*t)]; omega

/-- Conjecture 14 in Kimberling and Moses (2021), comparing offsets zero and two. -/
theorem conjecture14 {a b a' b' : ℕ → ℕ} (base : OffsetSolution 2 4 0 a b)
    (shifted : OffsetSolution 2 4 2 a' b') (n : ℕ) :
    a' n - a n = if n%3=0 then 2 else 1 := by
  rw [(offset_unique base (shift_solution 0 (by decide))).1,
      (offset_unique shifted (shift_solution 2 (by decide))).1]
  by_cases hn : n%3=0 <;> simp [shiftA, blockA, shiftPos, hn]

/-- Conjecture 15 in Kimberling and Moses (2021), comparing offsets zero and three. -/
theorem conjecture15 {a b a' b' : ℕ → ℕ} (base : OffsetSolution 2 4 0 a b)
    (shifted : OffsetSolution 2 4 3 a' b') (n : ℕ) :
    a' n - a n = if n%3=0 then 3 else 2 := by
  rw [(offset_unique base (shift_solution 0 (by decide))).1,
      (offset_unique shifted (shift_solution 3 (by decide))).1]
  by_cases hn : n%3=0 <;> simp [shiftA, blockA, shiftPos, hn]

/-- Conjecture 16 in Kimberling and Moses (2021), comparing offsets zero and five. -/
theorem conjecture16 {a b a' b' : ℕ → ℕ} (base : OffsetSolution 2 4 0 a b)
    (shifted : OffsetSolution 2 4 5 a' b') (n : ℕ) :
    a' n - a n = if n%3=0 then 5 else 3 := by
  rw [(offset_unique base (shift_solution 0 (by decide))).1,
      (offset_unique shifted (shift_solution 5 (by decide))).1]
  by_cases hn : n%3=0 <;> simp [shiftA, blockA, shiftPos, hn]

#print axioms conjecture14
#print axioms conjecture15
#print axioms conjecture16

end KimberlingMoses
