import Quantum.Hadamard.ComplementarySinger
import Quantum.Hadamard.ArithmeticBase

/-! Projective binary complementary pairs with independently prescribed length residues on
two coprime factors. The compatibility condition holds at a cut between ordered odd primes. -/
noncomputable section
namespace HadamardMod.Periodic
open Hadamard.PG Hadamard.Arithmetic

theorem switched_length {A B : ℕ} (ap : 0<A) (bp : 0<B) (ab : A.Coprime B)
    (oa : (2:ℕ).Coprime A) (ob : (2:ℕ).Coprime B) (phi : A.totient.Coprime B) :
    ∃ v:ℕ, Odd v ∧ HasLength (A*B) v ∧ v ≡ 1 [MOD A] ∧ v ≡ 2 [MOD B] := by
  obtain ⟨q,large,qp,qa,qb⟩ := prime_crt ap.ne' bp.ne' ab oa (Nat.coprime_one_left B) 2
  letI : Fact q.Prime := ⟨qp⟩
  let L := 2*A.totient
  have lp : 0<L := Nat.mul_pos (by decide) (Nat.totient_pos.mpr ap)
  obtain ⟨z,za,zb⟩ := Nat.chineseRemainder (ob.mul_left phi : L.Coprime B) 0 1
  let d := z+2*(L*B)
  have addzero (k:ℕ) (kl:k∣L*B) : d ≡ z [MOD k] := by
    have H : 2*(L*B) ≡ 0 [MOD k] := Nat.modEq_zero_iff_dvd.mpr (kl.trans (dvd_mul_left _ _))
    simpa [d] using Nat.ModEq.add_left z H
  have dl := (addzero L (dvd_mul_right L B)).trans za
  have db := (addzero B (dvd_mul_left B L)).trans zb
  have largeD : 2 ≤ d := by dsimp [d]; have := Nat.mul_pos lp bp; omega
  let n := d-1
  have en : n+1=d := by dsimp [n]; omega
  have en' : n+2=d+1 := by omega
  let v := geom q (n+2)
  have qae : (q:ZMod A)=2 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr qa
  have qbe : (q:ZMod B)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr qb
  have dp : A.totient∣d := (dvd_mul_left A.totient 2).trans (Nat.modEq_zero_iff_dvd.mp dl)
  obtain ⟨e,de⟩ := dp
  have period : (q:ZMod A)^d=1 := by
    have H := Nat.ModEq.pow_totient (coprime_of_modEq qa oa)
    have t : (q:ZMod A)^A.totient=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr H
    rw [de,pow_mul,t,one_pow]
  have va : (v:ZMod A)=1 := by
    have h := congrArg (fun t:ℤ => (t:ZMod A)) (geom_int q (n+2))
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_sub,Int.cast_one,Int.cast_pow] at h
    rw [en',pow_succ,period,qae] at h
    dsimp [v]
    rw [en']
    linear_combination h
  have vb : (v:ZMod B)=2 := by
    have h : (d:ZMod B)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr db
    dsimp [v]
    rw [en',geom_at_one _ _ _ qbe]
    push_cast
    rw [h]
    ring
  have ma : v ≡ 2*q^n [MOD A] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    rw [va,←qae,mul_comm,← pow_succ,en,period]
  have mb : v ≡ 2*q^n [MOD B] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    rw [vb,qbe,one_pow,mul_one]
  have full := (Nat.modEq_and_modEq_iff_modEq_mul ab).mp ⟨ma,mb⟩
  have mass : (v:ZMod (A*B))=2*(q:ZMod (A*B))^n := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr full
  have q2 : (q:ZMod 2)=1 := (ZMod.natCast_eq_natCast_iff q 1 2).mpr
    (Nat.odd_iff.mp (qp.odd_of_ne_two (by omega)))
  have d2 : d ≡ 0 [MOD 2] := dl.of_dvd (dvd_mul_right 2 A.totient)
  have vn : v ≡ n+2 [MOD 2] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (geom_at_one _ _ _ q2)
  have vo : Odd v := by rw [Nat.odd_iff]; change v%2=(n+2)%2 at vn; change d%2=0 at d2; omega
  exact ⟨v,vo,singer mass,(ZMod.natCast_eq_natCast_iff v 1 A).mp (by simpa using va),
    (ZMod.natCast_eq_natCast_iff v 2 B).mp (by simpa using vb)⟩

#print axioms switched_length
end HadamardMod.Periodic
