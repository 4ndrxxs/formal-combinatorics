import SignedFibreMultiplier
import SignedPrimePowerMultiplier

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

private theorem forward_const_mul (u:H→ZMod p) (c:ZMod p) :
    forward u*forward (fun _:H=>c)=forward (fun _:H=>(∑x,u x)*c) := by
  have same : forward (fun _:H=>c)=backward (fun _:H=>c) := by
    unfold forward backward
    exact Fintype.sum_equiv (Equiv.neg H) _ _ (fun x=>by simp)
  apply AddMonoidAlgebra.ext; ext t
  rw [same,cross_coeff,forward_coeff,←sum_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun x=>rfl)

theorem frobenius_constant_match (u v:H→ℤ) (B:H≃+H) (r:ℕ) (act:∀x:H,p^r • x=B x)
    (init:∀t,(p:ℤ)∣matched u v t-matched u v 0) (t w:H) :
    (p:ℤ)∣matched (fun x=>u (B.symm x)) v t-matched (fun x=>u (B.symm x)) v w := by
  let U:=fun x=>(u x:ZMod p)
  let V:=fun x=>(v x:ZMod p)
  let n:=p^r
  have positive : 0<n := pow_pos (Fact.out : p.Prime).pos _
  have coeff (g h:H→ℤ) (x:H) : (forward (fun i=>(g i:ZMod p))*backward (fun i=>(h i:ZMod p))).coeff x=(matched g h x:ZMod p) := by
    rw [cross_coeff,matched_shift,Int.cast_sum]; simp only [Int.cast_mul]
  have basic : ∃c:ZMod p,forward U*backward V=forward (fun _:H=>c) := by
    refine ⟨(matched u v 0:ZMod p),?_⟩
    apply AddMonoidAlgebra.ext; ext t
    rw [forward_coeff,show (forward U*backward V).coeff t=(matched u v t:ZMod p) from coeff u v t]
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (init t))
  have higher (j:ℕ) : ∃c:ZMod p,(forward U)^(j+1)*backward V=forward (fun _:H=>c) := by
    induction j with
    | zero=>simpa using basic
    | succ j ih=>
      obtain ⟨c,h⟩:=ih
      exact ⟨_,by rw [pow_succ' _ (j+1),mul_assoc,h,forward_const_mul]⟩
  have power : (forward U)^n=forward (fun x=>U (B.symm x)) := by
    rw [frobenius_forward]
    simp only [act,forward]
    exact Fintype.sum_equiv B.toEquiv _ _ (fun x=>by simp)
  obtain ⟨c,hc⟩:=higher (n-1)
  rw [Nat.sub_add_cancel positive,power] at hc
  have value (x:H) : (matched (fun i=>u (B.symm i)) v x:ZMod p)=c := by
    rw [←coeff,hc,forward_coeff]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sub,value,value,sub_self]

theorem horizontal_frobenius {k l s : ℤ} {f:ZMod p×H→ℤ} (hf:IsSDS k l f)
    (hn:k-l=(p:ℤ)*s) (hs:¬(p:ℤ)∣s) (cop:p.Coprime (Fintype.card H))
    (A:ZMod p≃+ZMod p) (B:H≃+H) (r:ℕ) (act:∀x:H,p^r • x=B x) (i:ZMod p) (t u:H) :
    let E:=A.prodCongr B
    (p:ℤ)∣matched (fun x=>f (E.symm x)) f (i,t)-matched (fun x=>f (E.symm x)) f (i,u) := by
  let E:=A.prodCongr B
  have expand (t:H) : matched (fun x=>f (E.symm x)) f (i,t)=
      ∑j:ZMod p,matched (fun x=>row f (A.symm (i+j)) (B.symm x)) (row f j) t := by
    rw [matched_shift,Fintype.sum_prod_type]
    apply sum_congr rfl; intro j _
    rw [matched_shift]; rfl
  change (p:ℤ)∣matched (fun x=>f (E.symm x)) f (i,t)-matched (fun x=>f (E.symm x)) f (i,u)
  rw [expand,expand,←sum_sub_distrib]
  apply dvd_sum; intro j _
  let i':=A.symm (i+j)
  apply frobenius_constant_match (row f i') (row f j) B r act _ t u
  intro z
  have h:=dvd_sub (row_cross_dvd hf hn cop j i' z) (row_cross_dvd hf hn cop j i' 0)
  have eq (t:H) : cross (row f j) (row f i') t=matched (row f i') (row f j) t := by
    rw [matched_shift,cross]; simp only [mul_comm,add_comm]
  simp only [eq] at h
  have ds : (p:ℤ)∣s*(matched (row f i') (row f j) z-matched (row f i') (row f j) 0) := by convert h using 1; ring
  exact ((Nat.prime_iff_prime_int.mp (Fact.out:p.Prime)).dvd_or_dvd ds).resolve_left hs

theorem long_frobenius_multiplier {k l s : ℤ} {f:ZMod p×H→ℤ} (hf:IsSDS k l f)
    (hn:k-l=(p:ℤ)*s) (hs:¬(p:ℤ)∣s) (pos:0<s) (cop:p.Coprime (Fintype.card H)) (long:p^2<Fintype.card H)
    (A:ZMod p≃+ZMod p) (B:H≃+H) (r:ℕ) (act:∀x:H,p^r • x=B x)
    (aux:∀t,s∣matched (fun x=>f ((A.prodCongr B).symm x)) f t-l) :
    ∃t:ZMod p×H,∀x,f ((A.prodCongr B).symm x)=f (x-t) := by
  let E:=A.prodCongr B
  let T:=fun t=>matched (fun x=>f (E.symm x)) f t-l
  have flat (x:ZMod p×H) : corr f x=(if x=0 then k-l else 0)+l := by rw [hf.flat]; split <;> omega
  have en : energy T=((p:ℤ)*s)^2 := hn ▸ match_excess_energy f _ _ E flat
  have same (i:ZMod p) (t u:H) : (p:ℤ)∣T (i,t)-T (i,u) := by
    simpa [T,sub_sub_sub_cancel_right,E] using horizontal_frobenius hf hn hs cop A B r act i t u
  have div (x:ZMod p×H) : k-l∣T x := hn ▸ long_fibre_divisibility T aux en pos.ne' hs long same x
  have pn : (0:ℤ)<p := by exact_mod_cast (Fact.out:p.Prime).pos
  exact integral_match_translation f _ _ (hn ▸ mul_pos pn pos) flat E div

#print axioms long_frobenius_multiplier

end Signed39.Contraction

