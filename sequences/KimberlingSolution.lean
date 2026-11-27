import KimberlingGeneral
import KimberlingIrregular
import KimberlingShifts
import KimberlingDensity
import KimberlingThreshold

open Filter Topology

namespace KimberlingMoses

/-- Formal conclusions for the eight conjectures in Kimberling and Moses, JIS 24
(2021), 21.3.3. The two incorrect clauses of Conjecture 6, the subscript issue
in Conjecture 8, and the false equivalence of Conjecture 20 are explicit. -/
structure PaperResults : Prop where
  generalExists : ∀ (h k : ℕ), 2≤h → 2≤k → ∃ a b, OffsetSolution h (k*h) 0 a b
  shiftedExists : ∀ (c : ℕ), c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=5 → ∃ a b, OffsetSolution 2 4 c a b
  basicExists : ∃ a b, Solution a b
  generalA : ∀ {h k : ℕ}, 2≤h → 2≤k → ∀ {a b : ℕ → ℕ}, OffsetSolution h (k*h) 0 a b →
    ∀ n, a n = (h*(k+1)+1)*n + if n%(k+1)=0 then 2 else 3
  modulusFails : ∀ {a b : ℕ → ℕ}, OffsetSolution 3 6 0 a b →
    a 3=32 ∧ ∀ i≤2, a 3%24 ≠ a i%24
  bRecurrenceFails : ∀ {a b : ℕ → ℕ}, OffsetSolution 2 4 0 a b → b 19 ≠ b 18+b 6-b 5
  bIntegerCounterexample : ∃ a b, OffsetSolution 2 4 0 a b ∧
    b 19=24 ∧ b 18=22 ∧ b 6=8 ∧ b 5=7 ∧ (b 19:ℤ) ≠ (b 18:ℤ)+b 6-b 5
  nonRecurrence : ∀ {a b : ℕ → ℕ}, OffsetSolution 2 4 1 a b →
    ¬∃ (N : ℕ) (E : LinearRecurrence ℂ), E.IsSolution (fun n => (upperIndices a (N+n):ℂ))
  indexGaps : ∀ {a b : ℕ → ℕ}, OffsetSolution 2 4 1 a b → ∀ g,
    (∃ j, upperIndices a (j+1)-upperIndices a j=g) ↔ 1≤g ∧ g≤5
  printedGaps : ∀ {a b : ℕ → ℕ}, OffsetSolution 2 4 1 a b → ∀ g,
    (∃ j, a (j+1)-a j=g) ↔ g=6 ∨ g=7 ∨ g=8
  offsetTwo : ∀ {a b a' b' : ℕ → ℕ}, OffsetSolution 2 4 0 a b → OffsetSolution 2 4 2 a' b' →
    ∀ n, a' n-a n = if n%3=0 then 2 else 1
  offsetThree : ∀ {a b a' b' : ℕ → ℕ}, OffsetSolution 2 4 0 a b → OffsetSolution 2 4 3 a' b' →
    ∀ n, a' n-a n = if n%3=0 then 3 else 2
  offsetFive : ∀ {a b a' b' : ℕ → ℕ}, OffsetSolution 2 4 0 a b → OffsetSolution 2 4 5 a' b' →
    ∀ n, a' n-a n = if n%3=0 then 5 else 3
  fiveGaps : ∀ {a b : ℕ → ℕ}, Solution a b → ∀ g, OccursGap b g ↔ 1≤g ∧ g≤5
  density : ∀ {a b : ℕ → ℕ}, Solution a b → Tendsto (proportion b) atTop (𝓝 (2/5:ℝ))
  uniqueBelowThreshold : ∃! ab : (ℕ → ℕ) × (ℕ → ℕ), AdvancedSolution 1 1 1 (-2) ab.1 ab.2
  thresholdFails : ¬∀ (u v k : ℕ) (c : ℤ), 1≤k → 1≤u → u≤v →
    ((∃! ab : (ℕ → ℕ) × (ℕ → ℕ), AdvancedSolution u v k c ab.1 ab.2) ↔ 2-(u:ℤ)-v+k-(v:ℤ)*k≤c)

theorem all_eight : PaperResults where
  generalExists h k hh hk := ⟨generalA h k,generalB h k,general_solution h k hh hk⟩
  shiftedExists c hc := by
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,_,shift_solution 0 (by decide)⟩
    · exact ⟨_,_,irregular_solution⟩
    · exact ⟨_,_,shift_solution 2 (by decide)⟩
    · exact ⟨_,_,shift_solution 3 (by decide)⟩
    · exact ⟨_,_,shift_solution 5 (by decide)⟩
  basicExists := ⟨seqA,seqB,explicit_solution⟩
  generalA := general_formula
  modulusFails := conjecture6_modulus_counterexample
  bRecurrenceFails := conjecture6_B_counterexample
  bIntegerCounterexample := ⟨generalA 2 2, generalB 2 2, general_solution 2 2 (by decide) (by decide), by decide⟩
  nonRecurrence := conjecture8_nonrecurrence
  indexGaps := conjecture8_index_gaps
  printedGaps := conjecture8_printed_gaps
  offsetTwo := conjecture14
  offsetThree := conjecture15
  offsetFive := conjecture16
  fiveGaps := conjecture18
  density := conjecture19
  uniqueBelowThreshold := conjecture20_unique_below_threshold
  thresholdFails := conjecture20_false

#print axioms all_eight

end KimberlingMoses
