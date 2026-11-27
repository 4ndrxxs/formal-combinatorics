import Quantum.Hadamard.GoethalsBits

/-! Exact cubic trace of a symmetric sign block with zero diagonal, computed
from row words by Hamming distance. Bit 1 denotes a negative entry. -/

open Finset Matrix
open scoped BigOperators

namespace Hadamard.BitTrace

def sign (w j : ℕ) : ℤ := if w.testBit j then -1 else 1

def wordMatrix {v : ℕ} (w : Fin v → ℕ) : Matrix (Fin v) (Fin v) ℤ :=
  fun i j ↦ sign (w i) j.val

def correlation (v a b : ℕ) : ℤ :=
  (v:ℤ)-2*(HadamardMod.lowOnes v (a ^^^ b):ℤ)

theorem row_dot (v a b : ℕ) :
    (∑ j : Fin v, sign a j.val * sign b j.val) = correlation v a b := by
  have term (j : Fin v) : sign a j.val * sign b j.val =
      1-2*((if (a ^^^ b).testBit j.val then 1 else 0 : ℕ):ℤ) := by
    simp only [sign,Nat.testBit_xor]
    cases a.testBit j.val <;> cases b.testBit j.val <;> norm_num
  simp only [term,sum_sub_distrib,←mul_sum,←Nat.cast_sum,
    ←HadamardMod.lowOnes_sum,correlation]
  simp

theorem correlation_self (v a : ℕ) : correlation v a a=v := by
  rw [←row_dot]
  have term (j : Fin v) : sign a j.val * sign a j.val=1 := by
    simp only [sign]
    cases a.testBit j.val <;> norm_num
  simp [term]

/-- Entries of the square of the sign matrix are Hamming correlations. -/
theorem square_entry {v : ℕ} (w : Fin v→ℕ) (sym : (wordMatrix w).IsSymm)
    (i j : Fin v) : ((wordMatrix w)^2) i j=correlation v (w i) (w j) := by
  rw [pow_two, Matrix.mul_apply, ←row_dot]
  apply sum_congr rfl
  intro k _
  change wordMatrix w i k * wordMatrix w k j = wordMatrix w i k * wordMatrix w j k
  rw [sym.apply j k]

/-- A computable double sum. Removing the positive diagonal changes the trace
by -3 v²+2v. -/
def cubicInteger {v : ℕ} (w : Fin v → ℕ) : ℤ :=
  (∑ i : Fin v, ∑ j : Fin v, correlation v (w i) (w j) * sign (w j) i.val)
    -3*(v:ℤ)^2+2*(v:ℤ)

theorem cubicInteger_eq_trace {v : ℕ} (w : Fin v→ℕ) (sym : (wordMatrix w).IsSymm)
    (diag : ∀ i : Fin v, sign (w i) i.val=1) :
    cubicInteger w = ((wordMatrix w-1)^3).trace := by
  let M := wordMatrix w
  have t3 : (M^3).trace =
      ∑ i : Fin v, ∑ j : Fin v, correlation v (w i) (w j) * sign (w j) i.val := by
    rw [pow_succ,Matrix.trace]
    apply sum_congr rfl
    intro i _
    change ∑ j, (M^2) i j * M j i = _
    simp only [M,square_entry w sym]
    rfl
  have t2 : (M^2).trace=(v:ℤ)^2 := by
    change (∑ i, ((wordMatrix w)^2) i i)=_
    simp [square_entry w sym, correlation_self,pow_two]
  have t1 : M.trace=(v:ℤ) := by
    change (∑ i, sign (w i) i.val)=_
    simp [diag]
  have expand : (M-1)^3=M^3-(3:ℤ) • (M^2)+(3:ℤ) • M-1 := by
    rw [show (3:ℤ) • (M^2)=M^2+M^2+M^2 by abel,
      show (3:ℤ) • M=M+M+M by abel]
    noncomm_ring
  change cubicInteger w = ((M-1)^3).trace
  rw [expand, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul,Matrix.trace_smul,t3,t2,t1,Matrix.trace_one]
  simp [cubicInteger]
  ring

/-- The nibble at position i lists the number of one-bits in byte i.
Each of the 256 table entries is certified against the bit definition. -/
private def byteCounts : ℕ := 0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

private def byteCount (w : ℕ) : ℕ := (byteCounts >>> (4*(w%256)))%16

private theorem byteCount_eq (w : ℕ) : byteCount w=HadamardMod.lowOnes 8 w := by
  have small : ∀ i : Fin 256, byteCount i.val=HadamardMod.lowOnes 8 i.val := by decide +kernel
  let j : Fin 256 := ⟨w%256, Nat.mod_lt _ (by decide)⟩
  have hj : byteCount w=byteCount j.val := by
    dsimp only [byteCount,j]
    rw [Nat.mod_mod]
  rw [hj,small j,HadamardMod.lowOnes_sum,HadamardMod.lowOnes_sum]
  apply Finset.sum_congr rfl
  intro i _
  have bit : j.val.testBit i.val=w.testBit i.val := by
    change (w%2^8).testBit i.val=w.testBit i.val
    rw [Nat.testBit_mod_two_pow]
    simp [i.isLt]
  rw [bit]

private theorem lowOnes_add (r k w : ℕ) : HadamardMod.lowOnes (r+k) w =
    HadamardMod.lowOnes r w+HadamardMod.lowOnes k (w/2^r) := by
  induction r generalizing w with
  | zero => simp [HadamardMod.lowOnes]
  | succ r ih =>
    rw [Nat.succ_add,HadamardMod.lowOnes,HadamardMod.lowOnes,ih]
    rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm 2]
    omega

/-- Read eight bits per step, then the remaining low-order bits in the last byte. -/
def packedOnes : ℕ → ℕ → ℕ → ℕ
  | 0, r, w => HadamardMod.lowOnes r w
  | c+1, r, w => byteCount w+packedOnes c r (w/256)

private theorem packedOnes_eq (c r w : ℕ) :
    packedOnes c r w=HadamardMod.lowOnes (8*c+r) w := by
  induction c generalizing w with
  | zero => simp [packedOnes]
  | succ c ih =>
    rw [show 8*(c+1)+r=8+(8*c+r) by omega,lowOnes_add,packedOnes,ih,byteCount_eq]
    rfl

def packedCorrelation (v a b : ℕ) : ℤ :=
  (v:ℤ)-2*(packedOnes (v/8) (v%8) (a ^^^ b):ℤ)

theorem packedCorrelation_eq (v a b : ℕ) : packedCorrelation v a b=correlation v a b := by
  rw [packedCorrelation,packedOnes_eq,show 8*(v/8)+v%8=v by omega]
  rfl

def packedCubic {v : ℕ} (w : Fin v → ℕ) : ℤ :=
  (∑ i : Fin v, ∑ j : Fin v, packedCorrelation v (w i) (w j) * sign (w j) i.val)
    -3*(v:ℤ)^2+2*(v:ℤ)

theorem packedCubic_eq {v : ℕ} (w : Fin v → ℕ) : packedCubic w=cubicInteger w := by
  simp only [packedCubic,cubicInteger,packedCorrelation_eq]

/-- Check a Boolean predicate at each nonnegative index below n. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, f => f n && allBelow n f

theorem allBelow_step {n : ℕ} {f : ℕ → Bool} (previous : allBelow n f=true)
    (last : f n=true) : allBelow (n+1) f=true := by
  simp [allBelow,previous,last]

private theorem below_true {n : ℕ} {f : ℕ → Bool} (check : allBelow n f=true)
    (i : ℕ) (lt : i<n) : f i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h : f n=true ∧ allBelow n f=true := by simpa [allBelow] using check
    by_cases e : i=n
    · simpa [e] using h.1
    · exact ih h.2 (by omega)

/-- A row in the lower triangle of the full conference correlation test. -/
def lowerRow (n : ℕ) (raw : ℕ → ℕ) (i : ℕ) : Bool :=
  allBelow i (fun j ↦ decide (packedCorrelation n (raw i) (raw j)=2*sign (raw i) j))

theorem correlations_of_lower {n : ℕ} (raw : ℕ → ℕ)
    (sym : (wordMatrix (fun i : Fin n ↦ raw i.val)).IsSymm)
    (checked : allBelow n (lowerRow n raw)=true) (i j : Fin n) (ne : i≠j) :
    correlation n (raw i.val) (raw j.val)=2*sign (raw i.val) j.val := by
  have lower (a b : Fin n) (h : b.val < a.val) :
      correlation n (raw a.val) (raw b.val)=2*sign (raw a.val) b.val := by
    have row := below_true checked a.val a.isLt
    have entry := below_true (f:=fun j ↦ decide
      (packedCorrelation n (raw a.val) (raw j)=2*sign (raw a.val) j)) row b.val h
    rw [←packedCorrelation_eq]
    exact of_decide_eq_true entry
  by_cases h : j.val < i.val
  · exact lower i j h
  · have flip : i.val < j.val := by
      have unequal : i.val≠j.val := fun eq ↦ ne (Fin.ext eq)
      omega
    have c : correlation n (raw i.val) (raw j.val)=correlation n (raw j.val) (raw i.val) := by
      simp only [correlation,Nat.xor_comm (raw i.val) (raw j.val)]
    rw [c,lower j i flip]
    exact congrArg (fun z : ℤ ↦ 2*z) (sym.apply i j)

/-- A computable integer sum in the order of the natural indices. -/
def sumBelow : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n+1, f => sumBelow n f+f n

private theorem sumBelow_fin (n : ℕ) (f : ℕ → ℤ) :
    sumBelow n f=∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Fin.sum_univ_castSucc,ih]; rfl

def packedRowTotal (n : ℕ) (raw : ℕ → ℕ) (i : ℕ) : ℤ :=
  sumBelow n (fun j ↦ packedCorrelation n (raw i) (raw j)*sign (raw j) i)

theorem cube_of_totals {n : ℕ} (raw : ℕ → ℕ) (totals : ℕ → ℤ)
    (checked : allBelow n (fun i ↦ decide (packedRowTotal n raw i=totals i))=true) :
    cubicInteger (fun i : Fin n ↦ raw i.val)=sumBelow n totals-3*(n:ℤ)^2+2*(n:ℤ) := by
  rw [←packedCubic_eq,packedCubic,sumBelow_fin]
  have row (i : Fin n) :
      (∑ j : Fin n, packedCorrelation n (raw i.val) (raw j.val)*sign (raw j.val) i.val)=totals i.val := by
    have h : packedRowTotal n raw i.val=totals i.val := of_decide_eq_true (below_true checked i.val i.isLt)
    rwa [packedRowTotal,sumBelow_fin] at h
  simp only [row]

#print axioms cube_of_totals
#print axioms correlations_of_lower
#print axioms cubicInteger_eq_trace
#print axioms packedCubic_eq

end Hadamard.BitTrace
