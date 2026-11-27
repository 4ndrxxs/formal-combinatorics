import Quantum.Hadamard.Goethals

/-! Kernel-reducible Hamming weights for binary circulant autocorrelations.
Each sum of modular inner products reduces to elementary natural arithmetic. -/
namespace HadamardMod
open Finset

def lowOnes : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,w => (if w.testBit 0 then 1 else 0) + lowOnes n (w/2)

theorem lowOnes_sum (k w : ℕ) :
    lowOnes k w = ∑ i:Fin k, if w.testBit i.val then 1 else 0 := by
  induction k generalizing w with
  | zero => simp [lowOnes]
  | succ k ih =>
    rw [Fin.sum_univ_succ,lowOnes,ih]
    simp only [Fin.val_zero,Fin.val_succ,Nat.testBit_succ] <;> rfl

def cycleWord (k w s : ℕ) := (w ||| (w <<< k)) >>> s

private theorem cycleWord_bit {k w : ℕ} [NeZero k] (bound : w<2^k) (s i : Fin k) :
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

def cyclicChanges (k w s : ℕ) := lowOnes k (w ^^^ cycleWord k w s)

theorem cyclicCorr_bits {k m w : ℕ} [NeZero k] (hw : w<2^k) (s : Fin k) :
    cyclicCorr (bitSeq m k w) (bitSeq m k w) s =
      (k:ZMod m)-2*(cyclicChanges k w s.val:ℕ) := by
  let v := w ^^^ cycleWord k w s.val
  have term (i:Fin k) : bitSeq m k w i*bitSeq m k w (i+s) =
      1-2*((if v.testBit i.val then 1 else 0:ℕ):ZMod m) := by
    simp only [v,Nat.testBit_xor,cycleWord_bit hw,bitSeq]
    cases w.testBit i.val <;> cases w.testBit (i+s).val <;> norm_num
  simp only [cyclicCorr,term,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [←Nat.cast_sum]
  simp [cyclicChanges,lowOnes_sum,v]

theorem of_hamming_four {k m a b c d : ℕ} [NeZero k]
    (bounds : a<2^k ∧ b<2^k ∧ c<2^k ∧ d<2^k)
    (ok : ∀ s:Fin k, s≠0 →
      (2*(cyclicChanges k a s.val+cyclicChanges k b s.val+
        cyclicChanges k c s.val+cyclicChanges k d s.val))%m=(4*k)%m) : AtOrder m (4*k) := by
  obtain ⟨ha,hb,hc,hd⟩ := bounds
  apply of_bit_sequences ![a,b,c,d]
  intro s hs
  rw [Fin.sum_univ_four]
  change cyclicCorr (bitSeq m k a) (bitSeq m k a) s+
    cyclicCorr (bitSeq m k b) (bitSeq m k b) s+
    cyclicCorr (bitSeq m k c) (bitSeq m k c) s+
    cyclicCorr (bitSeq m k d) (bitSeq m k d) s=0
  rw [cyclicCorr_bits ha,cyclicCorr_bits hb,cyclicCorr_bits hc,cyclicCorr_bits hd]
  have h := (ZMod.natCast_eq_natCast_iff _ _ m).mpr (ok s hs)
  push_cast at h
  linear_combination -h

#print axioms of_hamming_four
end HadamardMod
