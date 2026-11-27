import PaleyAllOrders

/-! Independent statement using literal matrix entries, a binary quadratic
form, and opposite Boolean signs at distinct roots. -/

noncomputable section
open Matrix

namespace PaleyQuadraticStatement
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def value (a b c : F) : Option F → F
  | none => a
  | some t => a*t^2+b*t+c

def completed (s : Option F→Bool) : Matrix (Option F) (Option F) ℝ := fun i j ↦
  if i=j then (if s i then 1 else -1) else
    match i,j with
    | some u,some v => (quadraticChar F (v-u) : ℤ)
    | _,_ => 1

theorem verified (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (a b c : F) (nonsingular : b^2-4*a*c≠0) (s : Option F→Bool) (orientation : Bool)
    (away : ∀ i, value a b c i≠0 →
      (if s i then (1:ℤ) else -1)=(if orientation then (1:ℤ) else -1)*quadraticChar F (value a b c i))
    (opposite : ∀ i j, i≠j → value a b c i=0 → value a b c j=0 → s i≠s j) :
    let q := Fintype.card F
    (4/5:ℝ)*(2*(q:ℝ))*((q:ℝ)-1)^(q/2) ≤ |(completed s).det| := by
  have odd : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  have v (i : Option F) : value a b c i=Hadamard.ProjectiveSigning.quadraticValue a b c i := by cases i <;> rfl
  have agree : ∀ i, Hadamard.ProjectiveSigning.quadraticValue a b c i≠0 →
      (if s i then (1:ℤ) else -1)=(if orientation then (1:ℤ) else -1)*
      quadraticChar F (Hadamard.ProjectiveSigning.quadraticValue a b c i) := by
    simpa only [v] using away
  have roots := Hadamard.ProjectiveSigning.sum_at_opposite_roots odd a b c nonsingular s (by
    simpa only [v] using opposite)
  have unit : (if orientation then (1:ℤ) else -1)^2=1 := by cases orientation <;> decide
  have result := Hadamard.ProjectiveSigning.quadratic_paley_four_fifths_all q4 lo
    a b c nonsingular s _ unit agree roots
  have mat : completed s = Hadamard.ProjectiveSigning.realPaley+
      diagonal (fun i ↦ if s i then (1:ℝ) else -1) := by
    ext i j
    by_cases h : i=j
    · subst j
      cases i <;> simp [completed,Hadamard.ProjectiveSigning.realPaley,HadamardMod.TorusFrobenius.entry]
    · cases i <;> cases j <;> simp_all [completed,Hadamard.ProjectiveSigning.realPaley,HadamardMod.TorusFrobenius.entry]
  rw [mat]; exact result

#print axioms verified

end PaleyQuadraticStatement
