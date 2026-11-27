import Quantum.Hadamard.ComplementaryCut

/-! Independent one-or-two length residues at the full primary factors of every odd modulus. -/
namespace HadamardMod.Periodic
open Finset

theorem length_one (m : ℕ) : HasLength m 1 := by
  let z : Pair m (ZMod 1) := {
    a := fun _ => 1
    b := fun _ => 1
    pos := fun _ => Or.inl rfl
    neg := fun _ => Or.inl rfl
    off := fun s ne => False.elim (ne (Subsingleton.elim s 0)) }
  exact ⟨ZMod 1,inferInstance,inferInstance,by simp,⟨z⟩⟩

theorem power_length {m v : ℕ} (odd : (2:ℕ).Coprime m)
    (h : HasLength m v) (e : ℕ) : HasLength m (v^e) := by
  induction e with
  | zero => simpa using length_one m
  | succ e ih => simpa [pow_succ] using mul_length odd ih h

private theorem primary_dvd {M p : ℕ} (pos : 0<M) (mem : p∈M.primeFactors) :
    p ^ M.factorization p ∣ M := by
  have d := Finset.dvd_prod_of_mem (fun s => s ^ M.factorization s) mem
  rwa [←Nat.prod_primeFactors_pow_factorization pos.ne'] at d

theorem singleton_switch {M : ℕ} (pos : 0<M) (odd : (2:ℕ).Coprime M) (q : ℕ)
    (qp : q.Prime) :
    ∃ v : ℕ, Odd v ∧ v.Coprime M ∧ HasLength M v ∧
      ∀ p ∈ M.primeFactors, v ≡ (if p=q then 2 else 1) [MOD p ^ M.factorization p] := by
  obtain ⟨a,ao,ac,ah,av⟩ := threshold_switch pos odd (q-1)
  obtain ⟨b,bo,bc,bh,bv⟩ := threshold_switch pos odd q
  let e := M.totient-1
  have ee : e+1=M.totient := by dsimp [e]; have := Nat.totient_pos.mpr pos; omega
  have inv : b*b^e ≡ 1 [MOD M] := by
    rw [Nat.mul_comm b,←pow_succ,ee]
    exact Nat.ModEq.pow_totient bc
  refine ⟨a*b^e,ao.mul (show Odd (b^e) from bo.pow),ac.mul_left (bc.pow_left _),
    mul_length odd ah (power_length odd bh e),?_⟩
  intro p hp
  have ha := av p hp
  have hb := bv p hp
  rcases lt_trichotomy p q with lt|eq|gt
  · have l : p≤q-1 := by omega
    simp only [if_pos l] at ha
    simp only [if_pos lt.le] at hb
    simpa [ne_of_lt lt] using ha.mul (hb.pow e)
  · subst p
    have l : ¬q≤q-1 := by have := qp.pos; omega
    simp only [if_neg l] at ha
    simp only [le_refl,if_true] at hb
    simpa using ha.mul (hb.pow e)
  · have l : ¬p≤q-1 := by omega
    simp only [if_neg l] at ha
    simp only [if_neg (not_le_of_gt gt)] at hb
    simp only [if_neg (ne_of_gt gt)]
    exact ((ha.trans hb.symm).mul_right (b^e)).trans (inv.of_dvd (primary_dvd pos hp))

theorem prescribed_switches {M : ℕ} (pos : 0 < M) (odd : (2:ℕ).Coprime M) (twos : Finset ℕ) :
    ∃ v : ℕ, Odd v ∧ v.Coprime M ∧ HasLength M v ∧
      ∀ p ∈ M.primeFactors, v ≡ (if p ∈ twos then 2 else 1) [MOD p ^ M.factorization p] := by
  classical
  induction twos using Finset.induction_on with
  | empty =>
    exact ⟨1,by decide,Nat.coprime_one_left M,length_one M,by intro p hp; rfl⟩
  | @insert q S hq ih =>
    obtain ⟨a,ao,ac,ah,av⟩ := ih
    by_cases mem : q ∈ M.primeFactors
    · obtain ⟨b,bo,bc,bh,bv⟩ := singleton_switch pos odd q (Nat.prime_of_mem_primeFactors mem)
      refine ⟨a*b,ao.mul bo,ac.mul_left bc,mul_length odd ah bh,?_⟩
      intro p hp
      have h := (av p hp).mul (bv p hp)
      by_cases pq : p=q
      · subst p; simpa [hq] using h
      · simpa [pq] using h
    · refine ⟨a,ao,ac,ah,?_⟩
      intro p hp
      have pq : p≠q := fun eq => mem (eq ▸ hp)
      simpa [pq] using av p hp

#print axioms prescribed_switches
end HadamardMod.Periodic


