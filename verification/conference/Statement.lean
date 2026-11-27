import Mathlib

/-! Finite estimates and filter limits stated independently of the research modules. -/

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
  (169 ≤ n-1 → (4/5:ℝ)*W ≤ d) ∧
    (16 ≤ n → |Real.log (d/W) - (1/2-Real.log 2)| ≤ 4*(Real.sqrt (n-1)+1)/n)

def ProportionEstimate : Prop := ∀ (k a b : ℕ) (C : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ),
  a+b=2*(k+1) → C.transpose=C → C*C=(2*(k:ℝ)+1) • 1 → (∀ i, C i i=0) →
  (∀ i j, i≠j → C i j=1 ∨ C i j= -1) →
  let n := 2*((k:ℝ)+1)
  let W := (2*n-2)*(n-2)^k
  let z := (a:ℝ)/n
  let d := |(C+Matrix.diagonal signedDiagonal).det|
  16≤n → |Real.log (d/W)-(2*z*(1-z)-Real.log 2)| ≤ (8*Real.sqrt (n-1)+4)/n

open Filter Topology

noncomputable def completedRatio {a b : ℕ} (k : ℕ)
    (C : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ) : ℝ :=
  let n := 2*((k:ℝ)+1)
  |(C+Matrix.diagonal signedDiagonal).det| / ((2*n-2)*(n-2)^k)

def BalancedLimit.{u} : Prop := ∀ (ι : Type u) (l : Filter ι) (k : ι → ℕ),
  Tendsto k l atTop →
  ∀ C : (j : ι) → Matrix (Fin (k j+1) ⊕ Fin (k j+1)) (Fin (k j+1) ⊕ Fin (k j+1)) ℝ,
  (∀ j, (C j).transpose = C j) → (∀ j, C j*C j=(2*(k j:ℝ)+1) • 1) →
  (∀ j i, C j i i=0) → (∀ j i s, i≠s → C j i s=1 ∨ C j i s= -1) →
  Tendsto (fun j ↦ completedRatio (k j) (C j)) l (𝓝 (Real.exp (1/2)/2))

def ProportionLimit.{u} : Prop := ∀ (ι : Type u) (l : Filter ι) (k a b : ι → ℕ) (z : ℝ),
  Tendsto k l atTop → (∀ j, a j+b j=2*(k j+1)) →
  Tendsto (fun j ↦ (a j:ℝ)/(2*((k j:ℝ)+1))) l (𝓝 z) →
  ∀ C : (j : ι) → Matrix (Fin (a j) ⊕ Fin (b j)) (Fin (a j) ⊕ Fin (b j)) ℝ,
  (∀ j, (C j).transpose = C j) → (∀ j, C j*C j=(2*(k j:ℝ)+1) • 1) →
  (∀ j i, C j i i=0) → (∀ j i s, i≠s → C j i s=1 ∨ C j i s= -1) →
  Tendsto (fun j ↦ completedRatio (k j) (C j)) l (𝓝 (Real.exp (2*z*(1-z))/2))

/-- Exact totals at every number of positive signs, encoded in one variable. -/
def DiagonalGenerating : Prop := ∀ (v : ℕ) (q z : ℝ)
    (C : Matrix (Fin (2*v)) (Fin (2*v)) ℝ), 1<q → C.transpose=C →
    C*C=q • 1 → C.trace=0 →
    (∑ f : Fin (2*v) → Bool, z^(Finset.univ.filter (fun i ↦ f i = true)).card *
      |(C+Matrix.diagonal (fun i ↦ if f i then (1:ℝ) else -1)).det|) =
      ((q-1)*(1+z)^2+4*z)^v

/-- The average is divided by the actual number of balanced sign assignments. -/
def BalancedMean : Prop := ∀ (k : ℕ) (C : Matrix (Fin (2*(k+1))) (Fin (2*(k+1))) ℝ),
    0<k → C.transpose=C → C*C=(2*(k:ℝ)+1) • 1 → (∀ i, C i i=0) →
    let q := 2*(k:ℝ)+1
    (q+1/q)^(k+1) ≤
      (∑ f : Fin (2*(k+1)) → Bool, if (Finset.univ.filter (fun i ↦ f i=true)).card=k+1
        then |(C+Matrix.diagonal (fun i ↦ if f i then (1:ℝ) else -1)).det| else 0) /
          ((2*(k+1)).choose (k+1) : ℝ)

/-- A literal sign vector on the given indices attains the strict finite bound. -/
def AboveLimitAtEveryOrder : Prop := ∀ (k : ℕ) (C : Matrix (Fin (2*(k+1))) (Fin (2*(k+1))) ℝ),
    0<k → C.transpose=C → C*C=(2*(k:ℝ)+1) • 1 → (∀ i, C i i=0) →
    (∀ i j, i≠j → C i j=1 ∨ C i j= -1) →
    ∃ d : Fin (2*(k+1)) → ℝ, (∀ i, d i=1 ∨ d i= -1) ∧
      (Finset.univ.filter (fun i ↦ d i=1)).card=k+1 ∧
      let n := 2*((k:ℝ)+1)
      Real.exp (1/2)/2 * ((2*n-2)*(n-2)^k) < |(C+Matrix.diagonal d).det|

/-- Every balanced sign vector on the original n coordinates from order 110. -/
def AllBalanced110 : Prop := ∀ (k : ℕ) (C : Matrix (Fin (2*(k+1))) (Fin (2*(k+1))) ℝ)
    (s : Fin (2*(k+1)) → Bool), 110≤2*(k+1) →
    C.transpose=C → C*C=(2*(k:ℝ)+1) • 1 → (∀ i, C i i=0) →
    (∀ i j, i≠j → C i j=1 ∨ C i j= -1) →
    (Finset.univ.filter (fun i ↦ s i=true)).card=k+1 →
    let n := 2*((k:ℝ)+1)
    (4/5:ℝ)*((2*n-2)*(n-2)^k) ≤ |(C+Matrix.diagonal (fun i ↦ if s i then (1:ℝ) else -1)).det|

end ConferenceAudit
