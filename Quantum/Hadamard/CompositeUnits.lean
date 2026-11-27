import Quantum.Hadamard.ArithmeticOneStep
import Quantum.Hadamard.ArithmeticPeriods

/-! Projective extenders for the unit residue classes at modulus 4b. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG

private theorem large_unit_four_from_period {b w : ℕ} (bp : 0<b) (odd : (2:ℕ).Coprime b)
    (cw : w.Coprime b)
    (period : ∀ q : ℕ, q.Coprime (4*b) → ∃ d : ℕ,
      (geom q (d+2):ZMod (4*b))=0 ∧ (q:ZMod (4*b))^(d+2)=1) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ 4*w [MOD 4*b] → AtOrder (4*b) n := by
  by_cases one : b=1
  · subst b
    simp only [Nat.mul_one]
    refine ⟨0,fun n _ hn _ => ones ?_⟩
    exact (ZMod.natCast_eq_zero_iff _ 4).mpr hn
  obtain ⟨u,_,hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime cw (by omega : 1<b)
  have inv : w*u ≡ 1 [MOD b] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt (by omega : 1<b)] using hu
  have cu : u.Coprime b := Nat.coprime_of_mul_modEq_one w (by simpa [mul_comm] using inv)
  obtain ⟨q,_,qp,q4,qb⟩ := prime_crt (m:=4) (n:=b) (a:=1) (b:=u)
    (by decide) bp.ne' (odd.pow_left 2) (by decide) cu 2
  letI : Fact q.Prime := ⟨qp⟩
  have cop4 : q.Coprime 4 := coprime_of_modEq q4 (by decide)
  have copb : q.Coprime b := coprime_of_modEq qb cu
  obtain ⟨d,zero,power⟩ := period q (cop4.mul_right copb)
  have qpower : q^(d+2) ≡ 1 [MOD 4*b] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using power
  have invq : q*w ≡ 1 [MOD b] := (qb.mul_right w).trans (by simpa [mul_comm] using inv)
  have e : q^(d+1) ≡ w [MOD b] := calc
    q^(d+1) ≡ q^(d+1)*(q*w) [MOD b] := by simpa using invq.symm.mul_left (q^(d+1))
    _ = q^(d+2)*w := by ring
    _ ≡ w [MOD b] := by simpa using (qpower.of_dvd (dvd_mul_left b 4)).mul_right w
  have er : 4*(q:ZMod (4*b))^(d+1) = (4*w:ℕ) := by
    have z := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (e.mul_left' 4)
    simpa using z
  obtain ⟨D⟩ := projective_extender_at (d:=d+1) zero
  rw [er] at D
  apply large_of_one_extender bp odd D
  simp only [Fintype.card_fin]
  have kpos : 0 < geom q ((d+1)+1) := by rw [geom_succ]; omega
  change 1 < geom q (((d+1)+1)+1)
  rw [geom_succ q ((d+1)+1)]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos kpos qp.pos)

theorem unit_four_large {b w : ℕ} (bp : 0<b) (odd : (2:ℕ).Coprime b)
    (cw : w.Coprime b) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ 4*w [MOD 4*b] → AtOrder (4*b) n :=
  large_unit_four_from_period bp odd cw (fun _ cop => geom_period (by omega) cop)

#print axioms unit_four_large
end HadamardMod
