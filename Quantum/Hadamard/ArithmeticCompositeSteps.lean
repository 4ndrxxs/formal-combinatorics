import Quantum.Hadamard.ArithmeticBrouwer
import Quantum.Hadamard.ArithmeticPeriods

/-! Choose the Paley-product and Brouwer extenders by CRT and Dirichlet.
Each extender fills its class using the dense seed theorem. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.PG

theorem lex_unit_class {b w : ℕ} (bp : 0 < b) (odd : (2:ℕ).Coprime b)
    (wp : 0 < w) (unit : (4*w-1).Coprime b) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ 4*w [MOD 4*b] → AtOrder (4*b) n := by
  have mpos : 1 < 4*b := by omega
  have x4 : 4*w-1 ≡ 3 [MOD 4] := by change (4*w-1)%4=3%4; omega
  have c4 := coprime_of_modEq x4 (by decide : (3:ℕ).Coprime 4)
  obtain ⟨q,hq,pq,res⟩ := Nat.forall_exists_prime_gt_and_modEq 2 (by omega) (c4.mul_right unit)
  have cq := coprime_of_modEq res (c4.mul_right unit)
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime cq mpos
  have inv : q*i ≡ 1 [MOD 4*b] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt mpos] using hi
  have ci : i.Coprime (4*b) := Nat.coprime_of_mul_modEq_one q (by rw [mul_comm i q]; exact inv)
  obtain ⟨p,hp,pp,pi⟩ := Nat.forall_exists_prime_gt_and_modEq 2 (by omega) ci
  have pq1 : p*q ≡ 1 [MOD 4*b] := (pi.mul_right q).trans (by simpa [mul_comm] using inv)
  have q4 := (res.of_dvd (dvd_mul_right 4 b)).trans x4
  have p4 : p%4=3 := by
    have eq := (q4.mul_left p).symm.trans (pq1.of_dvd (dvd_mul_right 4 b))
    change (p*3)%4=1%4 at eq
    omega
  have : Fact q.Prime := ⟨pq⟩
  have : Fact p.Prime := ⟨pp⟩
  have cast : (((p*q:ℕ):ZMod (4*b)))=1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr pq1
  let D := lexExtension (paleySkew (4*b) p p4) (paleySkew (4*b) q q4).inner
    (by simpa only [ZMod.card] using cast)
  have size : 1 < Fintype.card (ZMod p × ZMod q) := by
    simp only [Fintype.card_prod,ZMod.card]; nlinarith
  have cr : 1+(Fintype.card (ZMod q):ZMod (4*b))=((4*w:ℕ):ZMod (4*b)) := by
    have rr := res.add_right 1
    rw [show 4*w-1+1=4*w by omega] at rr
    simpa [add_comm] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr rr
  exact large_of_one_extender bp odd (cr ▸ D) size

theorem brouwer_unit_class {b w : ℕ} (bp : 1 < b) (odd : (2:ℕ).Coprime b)
    (wp : 0 < w) (unit : (2*w-1).Coprime b) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ 4*w [MOD 4*b] → AtOrder (4*b) n := by
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime unit bp
  have inv : (2*w-1)*i ≡ 1 [MOD b] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt bp] using hi
  have ci := Nat.coprime_of_mul_modEq_one (2*w-1) (by simpa [mul_comm] using inv)
  obtain ⟨q,hq,pq,q4,qi⟩ := prime_crt (by decide) (by omega : b≠0) (odd.pow_left 2 : (4:ℕ).Coprime b)
    (by decide : (3:ℕ).Coprime 4) ci 2
  have : Fact q.Prime := ⟨pq⟩
  have cb := coprime_of_modEq qi ci
  have cq := (coprime_of_modEq q4 (by decide : (3:ℕ).Coprime 4)).mul_right cb
  have k2 : 2*w-1 ≡ 1 [MOD 2] := by change (2*w-1)%2=1%2; omega
  have q2 : q ≡ 1 [MOD 2] := (q4.of_dvd (by decide : 2∣4)).trans (by decide)
  have both : (2*w-1)*q ≡ 1 [MOD 2*b] := (Nat.modEq_and_modEq_iff_modEq_mul odd).mp
    ⟨by simpa using k2.mul q2,(qi.mul_left (2*w-1)).trans inv⟩
  have twice := both.mul_left' 2
  rw [show 2*(2*b)=4*b by ring] at twice
  have rel : (2:ZMod (4*b))*(2*(w:ZMod (4*b))-1)*q=2 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr twice
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_mul] at h
    push_cast at h
    linear_combination h
  obtain ⟨d,zero,power⟩ := geom_period (by omega : 0 < 4*b) cq
  obtain ⟨D⟩ := Hadamard.Brouwer.extender (n := d) (m := 4*b) q4
    (by rw [zero,mul_zero])
  have eq : 2*((q:ZMod (4*b))+1)*q^(d+1)=((4*w:ℕ):ZMod (4*b)) := by
    push_cast
    rw [show d+2=d+1+1 by omega,pow_succ] at power
    linear_combination 4*(w:ZMod (4*b))*power-(q:ZMod (4*b))^(d+1)*rel
  have big : 1 < Fintype.card (Fin (1+2*q*geom q (d+2))) := by
    rw [Fintype.card_fin,show d+2=d+1+1 by omega,geom_succ]
    have pos : 0 < 2*q*(1+geom q (d+1)*q) := by positivity
    omega
  exact large_of_one_extender (by omega) odd (eq ▸ D) big

#print axioms lex_unit_class
#print axioms brouwer_unit_class
end HadamardMod
