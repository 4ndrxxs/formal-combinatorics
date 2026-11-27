import SignedReducedPrimeCases

namespace Signed39.Contraction

open Finset

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

private theorem forbidden_triple (a b c:ℤ) (ms:a+b+c= -47) (en:a^2+b^2+c^2=881) :
    a= -24 ∨ a= -22 ∨ b= -24 ∨ b= -22 ∨ c= -24 ∨ c= -22 := by
  have bounds (x y z:ℤ) (h:x^2+y^2+z^2=881) : -29≤x ∧ x≤29 := by
    constructor <;> nlinarith [sq_nonneg y,sq_nonneg z,sq_nonneg (x-30),sq_nonneg (x+30)]
  obtain ⟨al,ar⟩:=bounds a b c en
  obtain ⟨bl,br⟩:=bounds b a c (by linarith)
  let i:Fin 59:=⟨(a+29).toNat,by omega⟩
  let j:Fin 59:=⟨(b+29).toNat,by omega⟩
  have av:(i.val:ℤ)-29=a:=by dsimp [i]; omega
  have bv:(j.val:ℤ)-29=b:=by dsimp [j]; omega
  have rule : ∀u v:Fin 59, let x:ℤ:=u.val-29; let y:ℤ:=v.val-29; let z:ℤ:= -47-x-y
    x^2+y^2+z^2=881 → x= -24 ∨ x= -22 ∨ y= -24 ∨ y= -22 ∨ z= -24 ∨ z= -22 := by decide +kernel
  have h:=rule i j
  dsimp only at h
  rw [av,bv,show -47-a-b=c by omega] at h
  exact h en

private theorem no_fixed_249 (w:ZMod 249→ℤ) (mw:mass w= -47) (fix:∀x,w (4*x)=w x)
    (fw:∀t,corr w t=(if t=0 then 217 else 0)+8) : False := by
  let e:ZMod 83×ZMod 3≃+ZMod 249:=(ZMod.chineseRemainder (by decide : Nat.Coprime 83 3)).toAddEquiv.symm
  let F:=fun x=>w (e x)
  have flat (z:ZMod 83×ZMod 3) : corr F z=(if z=0 then 217 else 0)+8 := by
    rw [integral_pullback_corr w e,fw]; simp
  have mf:mass F= -47 := (Fintype.sum_equiv e.toEquiv _ _ (fun _=>rfl)).trans mw
  have scale (h:ZMod 83) (i:ZMod 3) : e (4*h,i)=4*e (h,i) := by
    have id:4 • (h,i)=(4*h,i) := by
      apply Prod.ext
      · exact nsmul_eq_mul _ _
      · change 4 • i=i
        rw [nsmul_eq_mul,show ((4:ℕ):ZMod 3)=1 by decide,one_mul]
    rw [←id,map_nsmul,nsmul_eq_mul]; rfl
  let A:=fiber F
  have ma:mass A= -47 := by
    change (∑i:ZMod 3,∑h:ZMod 83,F (h,i))= -47
    rw [sum_comm,←Fintype.sum_prod_type]; exact mf
  have ea:corr A 0=881 := by
    change corr (fiber F) 0=881; rw [fiber_corr]
    have each (h:ZMod 83) : corr F (h,0)=(if h=0 then 217 else 0)+8 := by rw [flat]; simp
    simp [each,sum_add_distrib,ZMod.card]
  have avoid (i:ZMod 3) : A i≠ -24 ∧ A i≠ -22 := by
    let row:=fun h=>F (h,i)
    have fr (h:ZMod 83) : row (4*h)=row h := by change w (e (4*h,i))=w (e (h,i)); rw [scale,fix]
    have div:=fixed_mass_83 row fr
    change (41:ℤ)∣A i-F (0,i) at div
    have bd:=coeff_square_le F (0,i); rw [flat] at bd; norm_num at bd
    have small:-15≤F (0,i) ∧ F (0,i)≤15:=by
      constructor <;> nlinarith [sq_nonneg (F (0,i)-16),sq_nonneg (F (0,i)+16)]
    omega
  unfold mass at ma
  unfold corr at ea; simp only [add_zero,←sq] at ea
  rw [Analytic.sum_three] at ma ea
  have bad:=forbidden_triple (A 0) (A 1) (A 2) ma ea
  have h0:=avoid 0; have h1:=avoid 1; have h2:=avoid 2
  tauto

theorem reduced_249_contradiction (u:ZMod 249→ℤ) (mu:mass u=155)
    (fu:∀t,corr u t=(if t=0 then 868 else 0)+93) : False := by
  let : Fact (Nat.Prime 2):=⟨by decide⟩
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=2) u 249 868 93 1 (-47) 217 8 (by rw [ZMod.card]; rfl) fu (by simpa using mu)
    (by decide) (by decide) 41 (by decide) (by rw [ZMod.card]; decide) (by decide) (by decide)
  obtain ⟨y,my,fy,cy⟩:=fixed_flat_quotient w 217 4 187 8 (-47) 1 16 (by decide) fw mw (by decide) (by decide)
    [⟨7,1,31,41⟩,⟨31,1,13,41⟩] (by dsimp [compatibleFactors,factorProduct]; decide +kernel) (by decide)
  exact no_fixed_249 y my fy cy

theorem reduced_7719_871 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=7719) :
    ¬∃f:G→ℤ,IsSDS 871 3 f := by
  rintro ⟨f,hf⟩
  obtain ⟨φ,onto⟩:=exists_quotient_249 (hg ▸ (by decide : 3∣7719)) (hg ▸ (by decide : 83∣7719))
  obtain ⟨u,mu,fu⟩:=normalized_proj_word hf φ onto 7719 249 31 868 93 155 hg (ZMod.card 249) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact reduced_249_contradiction u mu fu

theorem reduced_23157_869 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=23157) :
    ¬∃f:G→ℤ,IsSDS 869 1 f := by
  rintro ⟨f,hf⟩
  obtain ⟨φ,onto⟩:=exists_quotient_249 (hg ▸ (by decide : 3∣23157)) (hg ▸ (by decide : 83∣23157))
  obtain ⟨u,mu,fu⟩:=normalized_proj_word hf φ onto 23157 249 93 868 93 155 hg (ZMod.card 249) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact reduced_249_contradiction u mu fu

#print axioms reduced_7719_871
#print axioms reduced_23157_869

end Signed39.Contraction

