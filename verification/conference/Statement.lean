import Mathlib

/-! Statement of the two finite estimates, independently of the research modules. -/

namespace ConferenceAudit

def signedDiagonal {I J : Type*} : I ⊕ J → ℝ
  | .inl _ => 1
  | .inr _ => -1

def Estimates : Prop := ∀ (k : ℕ) (C : Matrix (Fin (k+1) ⊕ Fin (k+1))
    (Fin (k+1) ⊕ Fin (k+1)) ℝ),
  0 < k → C.transpose = C → C*C = (2*(k:ℝ)+1) • 1 → (∀ i, C i i = 0) →
  (∀ i j, i≠j → C i j=1 ∨ C i j= -1) →
  let n := 2*((k:ℝ)+1)
  let W := (2*n-2)*(n-2)^k
  let d := |(C+Matrix.diagonal signedDiagonal).det|
  (674 ≤ n-1 → (4/5:ℝ)*W ≤ d) ∧
    (16 ≤ n → |Real.log (d/W) - (1/2-Real.log 2)| ≤ 4*(Real.sqrt (n-1)+1)/n)

def ProportionEstimate : Prop := ∀ (k a b : ℕ) (C : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ),
  a+b=2*(k+1) → C.transpose=C → C*C=(2*(k:ℝ)+1) • 1 → (∀ i, C i i=0) →
  (∀ i j, i≠j → C i j=1 ∨ C i j= -1) →
  let n := 2*((k:ℝ)+1)
  let W := (2*n-2)*(n-2)^k
  let z := (a:ℝ)/n
  let d := |(C+Matrix.diagonal signedDiagonal).det|
  16≤n → |Real.log (d/W)-(2*z*(1-z)-Real.log 2)| ≤ (8*Real.sqrt (n-1)+4)/n

end ConferenceAudit
