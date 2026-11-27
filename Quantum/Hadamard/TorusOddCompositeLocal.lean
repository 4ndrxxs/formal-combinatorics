import Quantum.Hadamard.PowerResidues
import Mathlib.Data.Nat.Factorization.Basic

/-! A nonzero square class modulo an odd prime power remains a square at every
higher power for any fixed integer representative. -/
noncomputable section
namespace HadamardMod.TorusOddComposite
open Hadamard.Arithmetic Hadamard.Arithmetic.PowerResidues

theorem lift_nonzero_square {p e f n:ℕ} (pp:p.Prime) (po:2<p)
    (nonzero:¬p^e∣n) (square:IsSquare (n:ZMod (p^e))) : IsSquare (n:ZMod (p^f)) := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : NeZero (p^e) := ⟨pow_ne_zero _ pp.ne_zero⟩
  obtain ⟨root,rr⟩ := square
  let x := root.val
  have con : x^2 ≡ n [MOD p^e] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp [x,pow_two,rr])
  have xpos : x≠0 := by
    intro h
    apply nonzero
    exact Nat.modEq_zero_iff_dvd.mp (by simpa [h] using con.symm)
  let d:=x.factorization p
  let b:=x/(p^d)
  have split : x=p^d*b := (Nat.ordProj_mul_ordCompl_eq_self x p).symm
  have xs : x^2=p^(2*d)*b^2 := by
    calc
      _ = (p^d*b)^2 := congrArg (·^2) split
      _ = _ := by rw [mul_pow,←pow_mul, Nat.mul_comm d 2]
  have le : 2*d<e := by
    by_contra! ge
    apply nonzero
    exact (con.dvd_iff (dvd_refl _)).mp ((pow_dvd_pow p ge).trans ⟨b^2,xs⟩)
  have dv : p^(2*d)∣n := (con.dvd_iff (pow_dvd_pow p le.le)).mp ⟨b^2,xs⟩
  obtain ⟨u,nu⟩ := dv
  have small := con.of_dvd (pow_dvd_pow p (show 2*d+1≤e by omega))
  rw [xs,nu,pow_succ] at small
  have cu : b^2 ≡ u [MOD p] := Nat.ModEq.mul_left_cancel' (pow_ne_zero _ pp.ne_zero) small
  have bc : b.Coprime p := (Nat.coprime_ordCompl pp xpos).symm
  have uc : u.Coprime p := cu.gcd_eq.symm.trans (bc.pow_left 2)
  cases f with
  | zero =>
    rw [pow_zero]
    exact ⟨0,Subsingleton.elim _ _⟩
  | succ f =>
    have unit : IsUnit (u:ZMod (p^(f+1))) := (ZMod.isUnit_iff_coprime _ _).mpr (uc.pow_right _)
    have low : IsSquare (red p f (u:ZMod (p^(f+1)))) := by
      rw [map_natCast]
      refine ⟨(b:ZMod p),?_⟩
      simpa only [Nat.cast_pow,pow_two,Nat.cast_mul] using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr cu).symm
    have lift := square_of_red po unit low
    rw [nu,Nat.cast_mul,Nat.cast_pow,show 2*d=d*2 by omega,pow_mul]
    exact (Even.isSquare_pow (by decide : Even 2) _).mul lift

#print axioms lift_nonzero_square
end HadamardMod.TorusOddComposite


