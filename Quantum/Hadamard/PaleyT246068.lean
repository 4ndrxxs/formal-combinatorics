import Quantum.Hadamard.PaleyTProduct
import Quantum.Hadamard.PaleyT227Data

/-! A concrete real Hadamard matrix of order 246068. It combines the
order-271 periodic T-system with Paley's matrix at q=907 in sixteen
circulant blocks of size 227. The sixteen first rows are checked here
directly. A set bit denotes a minus sign. -/
namespace Hadamard.PeriodicT
open Finset HadamardMod Block227
set_option maxHeartbeats 150000
set_option maxRecDepth 100000

private theorem rotation {k w : ℕ} [NeZero k] (bound : w<2^k) (s i : Fin k) :
    (cycleWord k w s.val).testBit i.val = w.testBit (i+s).val := by
  simp only [cycleWord,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_shiftLeft,Fin.val_add]
  by_cases h : s.val+i.val<k
  · rw [Nat.mod_eq_of_lt (show i.val+s.val<k by omega)]
    simp [Nat.not_le_of_lt h,add_comm]
  · have ge : k ≤ s.val+i.val := by omega
    have zero : w.testBit (s.val+i.val)=false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide : 0<2) ge))
    have md : (i.val+s.val)%k=s.val+i.val-k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ i.val+s.val)]
      rw [Nat.mod_eq_of_lt (by have := i.isLt; have := s.isLt; omega)]
      omega
    simp [zero,ge,md]

private def letter (a : ℕ) (y : Fin 227) : ℤ := if a.testBit y.val then -1 else 1

private theorem dot_cross (a b : ℕ) (hb : b < 2^227) (v : Fin 227) :
    (∑ y : Fin 227, letter a y * letter b (y+v)) =
      (227:ℤ)-2*(ham a b v.val : ℤ) := by
  let z := a ^^^ cycleWord 227 b v.val
  have term (y:Fin 227) : letter a y * letter b (y+v) =
      1-2*((if z.testBit y.val then 1 else 0:ℕ):ℤ) := by
    simp only [z,Nat.testBit_xor,rotation hb,letter]
    cases a.testBit y.val <;> cases b.testBit (y+v).val <;> norm_num
  simp only [term,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [←Nat.cast_sum]
  rw [← lowOnes_sum 227 z]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rfl

private def paley227 : BlockSystem 227 where
  row i j y := letter (words i j) y
  signs i j y := by unfold letter; split <;> simp [HadamardMod.Sign]
  gram i k v := by
    change (∑ j:Fin 4, ∑ y:Fin 227, letter (words i j) y * letter (words k j) (y+v))=_
    rw [Fin.sum_univ_four]
    rw [dot_cross _ _ (words_bound k 0),dot_cross _ _ (words_bound k 1),
        dot_cross _ _ (words_bound k 2),dot_cross _ _ (words_bound k 3)]
    have h := congrArg (fun z : ℕ => (z:ℤ)) (totals i k v)
    simp only [amount,Nat.cast_add] at h
    split_ifs at h ⊢ with eq <;> push_cast at h ⊢ <;> linarith

/-- An ordinary integral sign Hadamard matrix of order 246068. -/
theorem real246068 : HadamardMod.AtOrder 0 246068 :=
  real_of_blocks system271 paley227

theorem real246068_gram : HadamardMod.IntegralSolution 0 246068 :=
  HadamardMod.integer_gram real246068

#print axioms real246068
#print axioms real246068_gram
end Hadamard.PeriodicT

