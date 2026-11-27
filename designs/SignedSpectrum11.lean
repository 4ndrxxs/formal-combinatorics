import SignedTemplateMatch
import SignedModularSupport

namespace Signed39.Template

open Finset Contraction

abbrev P := ZMod 11
abbrev K := ZMod 23

local instance : Fact (Nat.Prime 11):=⟨by decide⟩
local instance : Fact (Nat.Prime 23):=⟨by decide⟩

def chi (r i:P) : K := (2:K)^(r*i).val
def spectrum (u:P→ℤ) (r:P) : K := ∑i,chi r i*(u i:K)
def freq (j:Fin 5) : P := (j.val+1:ℕ)
def root (b:Fin 5→Bool) (j:Fin 5) : P := if b j then -(freq j) else freq j

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem chi_add : ∀r i j:P,chi r (i+j)=chi r i*chi r j := by decide +kernel
theorem chi_neg (r i:P) : chi (-r) i=chi r (-i) := by simp [chi]

theorem choose_roots (u:P→ℤ) (flat:∀t,corr u t=(if t=0 then 253 else 0)-23) :
    ∃b:Fin 5→Bool,∀j,spectrum u (root b j)=0 := by
  let U:=fun i=>(u i:K)
  have corrZero (t:P) : (∑i,U i*U (i+t))=0 := by
    have eq:=congrArg (fun x:ℤ=>(x:K)) (flat t)
    change (↑(∑i,u i*u (i+t)):K)=_ at eq
    rw [Int.cast_sum] at eq
    simpa only [U,Int.cast_mul,Int.cast_sub,Int.cast_ite,Int.cast_ofNat,Int.cast_zero,
      show (253:K)=0 by decide,show (23:K)=0 by decide,ite_self,sub_zero] using eq
  have prod (r:P) : spectrum u r*spectrum u (-r)=0 := by
    have inner (x:P) : (∑t,chi r t*U (x+t))=chi (-r) x*spectrum u r := by
      rw [spectrum,mul_sum]
      apply Fintype.sum_equiv (Equiv.addLeft x)
      intro t
      have e : chi r t=chi (-r) x*chi r (x+t) := by rw [chi_neg,←chi_add]; simp
      change chi r t*U (x+t)=chi (-r) x*(chi r (x+t)*U (x+t))
      rw [e]; ring
    calc
      _=∑x,U x*(chi (-r) x*spectrum u r) := by
        conv_lhs => rw [show spectrum u (-r)=∑x,chi (-r) x*U x from rfl,mul_sum]
        apply sum_congr rfl; intros; ring
      _=∑x,∑t,chi r t*(U x*U (x+t)) := by
        apply sum_congr rfl; intro x _
        rw [←inner,mul_sum]
        apply sum_congr rfl; intros; ring
      _=0 := by rw [sum_comm]; simp only [←mul_sum,corrZero,mul_zero,sum_const_zero]
  let b:=fun j:Fin 5=>decide (spectrum u (freq j)≠0)
  refine ⟨b,fun j=>?_⟩
  by_cases z:spectrum u (freq j)=0
  · simp [root,b,z]
  · have h:=(mul_eq_zero.mp (prod (freq j))).resolve_left z
    simpa [root,b,z] using h

structure Word where
  values : List ℤ
  coef : List ℕ
  deriving Repr,DecidableEq

def word (W:Word) (i:P) : ℤ := W.values.getD i.val 0
def rootCoef (W:Word) (j:Fin 5) : K := (W.coef.getD j.val 0:ℕ)

def valid (W:Word) (b:Fin 5→Bool) : Prop :=
  energy (word W)=230 ∧ (∀t,corr (word W) t=(if t=0 then 253 else 0)-23) ∧
  ∀i:P,(word W i:K)=∑j:Fin 5,rootCoef W j*chi (root b j) i

instance (W:Word) (b:Fin 5→Bool) : Decidable (valid W b) := by unfold valid; infer_instance

theorem template_modulus (u:P→ℤ) (flat:∀t,corr u t=(if t=0 then 253 else 0)-23)
    (b:Fin 5→Bool) (roots:∀j,spectrum u (root b j)=0) (W:Word) (cert:valid W b) :
    ∀t,(253:ℤ)∣matched u (word W) t-matched u (word W) 0 := by
  obtain ⟨_,fw,rr⟩:=cert
  have cp (v:P→ℤ) (f:∀t,corr v t=(if t=0 then 253 else 0)-23) (t:P) :
      ModularSupport.rcorr (fun i=>(v i:P)) t= -23 := by
    have h:=congrArg (fun x:ℤ=>(x:P)) (f t)
    change (↑(∑i,v i*v (i+t)):P)=_ at h
    simpa only [ModularSupport.rcorr,Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_ite,Int.cast_zero,
      Int.cast_ofNat,show (253:P)=0 by decide,ite_self,zero_sub] using h
  have m11 (t:P) : (11:ℤ)∣matched u (word W) t-matched u (word W) 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).mp
    rw [Int.cast_sub,sub_eq_zero]
    simp only [matched,Int.cast_sum,Int.cast_mul,sub_zero]
    simp only [sub_eq_add_neg]
    exact ModularSupport.cross_constant _ _ _ _ (cp u flat) (cp (word W) fw) (-t)
  have m23 (t:P) : (23:ℤ)∣matched u (word W) t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 23).mp
    simp only [matched,Int.cast_sum,Int.cast_mul,rr,mul_sum]
    rw [sum_comm]
    apply sum_eq_zero; intro j _
    calc
      _=rootCoef W j*chi (root b j) (-t)*spectrum u (root b j) := by
        rw [spectrum,mul_sum]
        apply sum_congr rfl; intro i _
        rw [sub_eq_add_neg,chi_add]; ring
      _=0 := by rw [roots,mul_zero]
  intro t
  exact (by decide : IsCoprime (11:ℤ) 23).mul_dvd (m11 t) (dvd_sub (m23 t) (m23 0))

#print axioms template_modulus

end Signed39.Template
