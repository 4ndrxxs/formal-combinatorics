import Quantum.Hadamard.ArithmeticSelfDualGauss

/-! The elementary one-dimensional square sum is the ordinary
quadratic-character Gauss sum; its square is negative at p=3 mod 4. -/
noncomputable section
namespace HadamardMod
open Finset MulChar

theorem prime_phase_negative {p:ℕ} [Fact p.Prime] (p4:p%4=3)
    (ψ:AddChar (ZMod p) ℂ) (prim:ψ.IsPrimitive) :
    (∑ x:ZMod p,ψ (x*x))^2=-(p:ℂ) := by
  classical
  let F := ZMod p
  have hc : ringChar F≠2 := by change ringChar (ZMod p) ≠ 2; rw [ZMod.ringChar_zmod_n]; omega
  let χ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have neq : χ≠1 := (ringHomComp_ne_one_iff (by exact_mod_cast (Int.cast_injective (α:=ℂ)))).mpr
    (quadraticChar_ne_one hc)
  have hq : χ.IsQuadratic := (quadraticChar_isQuadratic F).comp _
  have val (a:F) : χ a=(quadraticChar F a:ℂ) := rfl
  have ct (a:F) : (∑ x:F,if x^2=a then (1:ℂ) else 0)=χ a+1 := by
    rw [Finset.sum_boole,val]
    have card := quadraticChar_card_sqrts hc a
    have eq : (univ.filter fun x:F => x^2=a)={x:F | x^2=a}.toFinset := by ext; simp
    rw [eq]; exact_mod_cast card
  have z : (∑ a:F,ψ a)=0 := by simpa using AddChar.sum_mulShift (1:F) prim
  have repr : (∑ x:F,ψ (x*x))=gaussSum χ ψ := by
    calc
      _ = ∑ x:F,∑ a:F,if x^2=a then ψ a else 0 := by simp [pow_two]
      _ = ∑ a:F,(∑ x:F,if x^2=a then (1:ℂ) else 0)*ψ a := by
        rw [sum_comm]
        apply sum_congr rfl; intro a _
        rw [sum_mul]
        apply sum_congr rfl; intro x _
        by_cases h:x^2=a <;> simp [h]
      _ = _ := by simp [ct,add_mul,sum_add_distrib,z,gaussSum]
  have neg : χ (-1) = -1 := by
    rw [val,quadraticChar_neg_one hc,show Fintype.card F=p from ZMod.card p,
      ZMod.χ₄_nat_three_mod_four p4]; simp
  rw [repr,gaussSum_sq neq hq prim,neg,show Fintype.card F=p from ZMod.card p]
  ring

theorem positive_gauss_contradiction {P n k:ℕ} {G:ℂ} (pp:0 < P) (kp:0 < k)
    (n4:n%4=2) (neg:G^2=-(P:ℂ)) (pos:G^n=k) : False := by
  let t:=n/4
  have nt : n=2*(2*t+1) := by dsimp [t]; omega
  have eq : (-(P:ℂ))^(2*t+1)=(k:ℂ) := by rw [←neg,←pow_mul,←nt]; exact pos
  have odd : Odd (2*t+1) := ⟨t,rfl⟩
  rw [odd.neg_pow] at eq
  have real : -(P:ℝ)^(2*t+1)=(k:ℝ) := by exact_mod_cast eq
  have hp : (0:ℝ)<P := by exact_mod_cast pp
  have hk : (0:ℝ)<k := by exact_mod_cast kp
  have h := pow_pos hp (2*t+1)
  linarith

theorem no_singular_once_twice {p n u:ℕ} (pp:p.Prime) (p4:p%4=3)
    (n4:n%4=2) (hn:n=p*u) (cu:u.Coprime p) : ¬IntegralSolution (p^2) n := by
  intro H
  let : Fact p.Prime := ⟨pp⟩
  have code := singular_self_dual (v:=1) pp (by decide)
    (by simpa only [pow_one] using hn) cu H
  obtain ⟨D,dg,ker⟩ := code
  let q:=p^1
  have qp:q.Prime := by simpa [q] using pp
  let : Fact q.Prime := ⟨qp⟩
  have q4:q%4=3 := by simpa [q] using p4
  have unit : IsUnit (2:ZMod q) := by
    exact (ZMod.isUnit_iff_coprime 2 q).mpr (Hadamard.Arithmetic.two_coprime_prime qp (by omega))
  obtain ⟨k,kp,gs⟩ := code_gauss unit D dg ker ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
  have neg := prime_phase_negative q4 ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
  exact positive_gauss_contradiction qp.pos kp n4 neg gs

#print axioms prime_phase_negative
#print axioms no_singular_once_twice
end HadamardMod
