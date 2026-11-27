import Quantum.Hadamard.ArithmeticGaussLift
import Quantum.Hadamard.ArithmeticPrimeGauss

/-! A local obstruction at singular orders congruent to two modulo four.
It holds for every odd p-adic valuation strictly below that of the
modulus when p is an odd prime congruent to three modulo four. -/
noncomputable section
namespace HadamardMod
open Hadamard.Gauss

theorem odd_power_gauss_negative {p v:ℕ} (pp:p.Prime) (p4:p%4=3) (vo:Odd v) :
    (sumSquares (p^v))^2=-((p^v:ℕ):ℂ) := by
  let : Fact p.Prime := ⟨pp⟩
  obtain ⟨t,rfl⟩ := vo
  induction t with
  | zero =>
    simp only [Nat.mul_zero,zero_add,pow_one]
    rw [sumSquares_eq]
    exact prime_phase_negative p4 ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
  | succ t IH =>
    have eq : p^(2*(t+1)+1)=p*(p^(2*t+1)*p) := by
      rw [show 2*(t+1)+1=(2*t+1)+2 by omega,pow_add,pow_two]; ring
    rw [eq,digit_reduction pp (by omega) (pow_pos pp.pos _),mul_pow,IH]
    push_cast
    ring

theorem no_singular_twice_mod_four {p v n u:ℕ} (pp:p.Prime) (p4:p%4=3)
    (vo:Odd v) (n4:n%4=2) (hn:n=p^v*u) (cu:u.Coprime p) : ¬IntegralSolution (p^(v+1)) n := by
  intro H
  have vpos : 0 < v := by obtain ⟨k,hk⟩ := vo; omega
  let : NeZero (p^v) := ⟨(pow_pos pp.pos _).ne'⟩
  obtain ⟨D,dg,ker⟩ := singular_self_dual pp vpos hn cu H
  have unit : IsUnit (2:ZMod (p^v)) := by
    simpa using (ZMod.isUnit_iff_coprime 2 (p^v)).mpr
      ((Hadamard.Arithmetic.two_coprime_prime pp (by omega)).pow_right v)
  obtain ⟨k,kp,gs⟩ := code_gauss unit D dg ker ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (p^v))
  have neg := odd_power_gauss_negative pp p4 vo
  rw [sumSquares_eq] at neg
  exact positive_gauss_contradiction (pow_pos pp.pos _) kp n4 neg gs

theorem no_even_singular_valuation {p e n:ℕ} (pp:p.Prime) (p4:p%4=3)
    (n4:n%4=2) (ve:n.factorization p < e) (vo:Odd (n.factorization p)) :
    ¬IntegralSolution (p^e) n := by
  intro H
  have nz:n≠0 := by omega
  let v:=n.factorization p
  let u:=n/(p^v)
  have hn:n=p^v*u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have dv : p^(v+1)∣p^e := pow_dvd_pow _ ve
  obtain ⟨A,sg,gram⟩ := H
  apply no_singular_twice_mod_four pp p4 vo n4 hn (Nat.coprime_ordCompl pp nz).symm
  exact ⟨A,sg,fun i k => (show ((p^(v+1):ℕ):ℤ)∣((p^e:ℕ):ℤ) by exact_mod_cast dv).trans (gram i k)⟩

#print axioms no_singular_twice_mod_four
#print axioms no_even_singular_valuation
end HadamardMod
