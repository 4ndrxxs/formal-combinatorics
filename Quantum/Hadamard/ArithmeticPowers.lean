import Quantum.Hadamard.Basic
import Quantum.Hadamard.ArithmeticSeed

/-! Explicit starting matrices in every parity class above powers of four
and in every even parity class above twice powers of four. -/

namespace HadamardMod

open Hadamard.Arithmetic

theorem four_seed {m : ℕ} (hm : m.Prime) (hm2 : 2 < m) (c : ℕ) :
    ∃ k > 0, AtOrder m k ∧ k ≡ c [MOD 4] ∧ k ≡ 4 [MOD m] := by
  obtain ⟨z,z4,zm⟩ := Nat.chineseRemainder (four_coprime_prime hm hm2) c 4
  let k := z+4*m
  have k4 : k ≡ c [MOD 4] := by
    apply Nat.ModEq.trans (b:=z) _ z4
    simp [k,Nat.ModEq]
  have km : k ≡ 4 [MOD m] := by
    apply Nat.ModEq.trans (b:=z) _ zm
    simp [k,Nat.ModEq]
  refine ⟨k, ?_, offdiag_four (by simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr km), k4, km⟩
  dsimp [k]; omega

theorem power_four_seed {m : ℕ} (hm : m.Prime) (hm2 : 2 < m) (e c : ℕ) :
    ∃ k > 0, AtOrder m k ∧ k ≡ c [MOD 4] ∧ k ≡ 4^e [MOD m] := by
  obtain ⟨a,apos,A,a4,am⟩ := four_seed hm hm2 c
  obtain ⟨b,bpos,B,b4,bm⟩ := four_seed hm hm2 1
  have powers (j : ℕ) : AtOrder m (a*b^j) := by
    induction j with
    | zero => simpa using A
    | succ j ih => simpa [pow_succ, Nat.mul_assoc] using at_mul ih B
  let j := e+(m-2)
  have jp : j+1 = e+(m-1) := by dsimp [j]; omega
  have fermat : 4^(m-1) ≡ 1 [MOD m] :=
    Nat.ModEq.pow_card_sub_one_eq_one hm (four_coprime_prime hm hm2)
  have exponent : 4^(j+1) ≡ 4^e [MOD m] := by
    rw [jp, pow_add]
    simpa using fermat.mul_left (4^e)
  refine ⟨a*b^j, Nat.mul_pos apos (pow_pos bpos _), powers j, ?_, ?_⟩
  · simpa using a4.mul (b4.pow j)
  · exact (am.mul (bm.pow j)).trans (by simpa only [pow_succ', Nat.mul_comm] using exponent)

theorem twice_power_four_seed {m : ℕ} (hm : m.Prime) (hm2 : 2 < m) (e c : ℕ)
    (hc : c%2=0) : ∃ k > 0, AtOrder m k ∧ k ≡ c [MOD 4] ∧ k ≡ 2*4^e [MOD m] := by
  obtain ⟨a,apos,A,a4,am⟩ := power_four_seed hm hm2 e (c/2)
  refine ⟨2*a, by omega, at_mul (order_two m) A, ?_, am.mul_left 2⟩
  simpa [show 2*(c/2)=c by omega] using a4.mul_left 2

theorem zero_residue_seed {m n : ℕ} (hm : m.Prime) (hm2 : 2 < m) (hn : n ≡ 0 [MOD m]) :
    ∃ k > 0, AtOrder m k ∧ k ≡ n [MOD 4] ∧ k ≡ n [MOD m] := by
  let k := n+4*m
  have k4 : k ≡ n [MOD 4] := by simp [k,Nat.ModEq]
  have km : k ≡ n [MOD m] := by simp [k,Nat.ModEq]
  have hz : (k : ZMod m)=0 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ m).mpr (km.trans hn)
  exact ⟨k, by dsimp [k]; omega, ones hz, k4, km⟩

end HadamardMod
