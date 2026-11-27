import Quantum.Hadamard.ComplementarySwitch

/-! Projective complementary pairs at a cut in the ordered prime powers of an odd modulus. -/
namespace HadamardMod.Periodic
open Finset Hadamard.Arithmetic

private theorem prime_coprime_lt {x y : ℕ} (xpos : 0 < x) (xy : x < y) (p : y.Prime) :
    x.Coprime y :=
  (p.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt xpos xy)).symm

private theorem phi_cut {M q : ℕ} (qp : q.Prime) (S : Finset ℕ)
    (before : ∀ p ∈ S, p.Prime ∧ p < q) :
    (∏ p ∈ S, p ^ M.factorization p).totient.Coprime q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S xs ih =>
    obtain ⟨xp,xq⟩ := before x (mem_insert_self x S)
    have rem (p : ℕ) (hp : p ∈ S) := before p (mem_insert_of_mem hp)
    have disjoint : (x ^ M.factorization x).Coprime (∏ p ∈ S, p ^ M.factorization p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      have xe : x ≠ p := fun e => xs (e ▸ hp)
      exact ((Nat.coprime_primes xp (rem p hp).1).mpr xe).pow_left _ |>.pow_right _
    rw [prod_insert xs,Nat.totient_mul disjoint]
    apply Nat.Coprime.mul_left _ (ih rem)
    cases e : M.factorization x with
    | zero => simp
    | succ a =>
      rw [Nat.totient_prime_pow_succ xp]
      exact ((prime_coprime_lt xp.pos xq qp).pow_left _).mul_left
        (prime_coprime_lt (by have := xp.two_le; omega) (by omega) qp)

theorem threshold_switch {M : ℕ} (pos : 0 < M) (odd : (2:ℕ).Coprime M) (c : ℕ) :
    ∃ v : ℕ, Odd v ∧ v.Coprime M ∧ HasLength M v ∧
      ∀ p ∈ M.primeFactors, v ≡ (if p ≤ c then 1 else 2) [MOD p ^ M.factorization p] := by
  classical
  let L := M.primeFactors.filter (· ≤ c)
  let R := M.primeFactors.filter (fun p => ¬p ≤ c)
  let w (p:ℕ) := p ^ M.factorization p
  let A := ∏ p ∈ L, w p
  let B := ∏ p ∈ R, w p
  have eq : A*B=M := (Finset.prod_filter_mul_prod_filter_not M.primeFactors (·≤c) w).trans
    (Nat.prod_primeFactors_pow_factorization pos.ne').symm
  have ap : 0<A := by have h : 0<A*B := eq ▸ pos; exact Nat.pos_of_mul_pos_right h
  have bp : 0<B := by have h : 0<A*B := eq ▸ pos; exact Nat.pos_of_mul_pos_left h
  have oa : (2:ℕ).Coprime A := odd.of_dvd_right (eq ▸ dvd_mul_right A B)
  have ob : (2:ℕ).Coprime B := odd.of_dvd_right (eq ▸ dvd_mul_left B A)
  have ab : A.Coprime B := by
    apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.prod_left
    intro p hp
    obtain ⟨pq,pc⟩ := Finset.mem_filter.mp hp
    obtain ⟨qq,qc⟩ := Finset.mem_filter.mp hq
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors pq)
      (Nat.prime_of_mem_primeFactors qq)).mpr (by omega)).pow_left _ |>.pow_right _
  have cp : A.totient.Coprime B := by
    apply Nat.Coprime.prod_right
    intro q hq
    obtain ⟨qq,qc⟩ := Finset.mem_filter.mp hq
    apply Nat.Coprime.pow_right
    apply phi_cut (M:=M) (Nat.prime_of_mem_primeFactors qq)
    intro p hp
    obtain ⟨pq,pc⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors pq,by omega⟩
  obtain ⟨v,vo,vh,va,vb⟩ := switched_length ap bp ab oa ob cp
  have vcp : v.Coprime (A*B) := (coprime_of_modEq va (Nat.coprime_one_left A)).mul_right
    (coprime_of_modEq vb ob)
  refine ⟨v,vo,eq ▸ vcp,eq ▸ vh,?_⟩
  intro p hp
  by_cases pc : p ≤ c
  · rw [if_pos pc]
    exact va.of_dvd (Finset.dvd_prod_of_mem w (Finset.mem_filter.mpr ⟨hp,pc⟩ : p∈L))
  · rw [if_neg pc]
    exact vb.of_dvd (Finset.dvd_prod_of_mem w (Finset.mem_filter.mpr ⟨hp,pc⟩ : p∈R))

#print axioms threshold_switch
end HadamardMod.Periodic


