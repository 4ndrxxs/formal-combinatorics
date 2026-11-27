import SignedFibreFactorization
import SignedFullConjugacy

namespace Signed39.Contraction

open Finset
variable {G:Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {q:ℕ} [Fact q.Prime]

theorem flat_center_divisible (u:G→ℤ) (n l:ℤ) (flat:∀x,corr u x=(if x=0 then n else 0)+l)
    (dv:(q:ℤ)∣n) (e:ℕ) (ep:0<e) (inv:∀x:G,q^e • x= -x) (x:G) :
    (q:ℤ)∣(Fintype.card G:ℤ)*u x-mass u := by
  let m:ℤ:=Fintype.card G
  let v:=fun i=>m*u i-mass u
  have total:=mass_from_flat u n l flat
  have cor (a:G→ℤ) (t:G) : corr a t=matched a a (-t) := by simp [corr,matched]
  have all (t:G) : (q:ℤ)∣corr v t := by
    rw [cor]; dsimp only [v,m]; rw [centered_match,←cor,flat]
    obtain ⟨z,hz⟩:=dv
    by_cases zero:t=0
    · simp only [zero,ite_true]; refine ⟨(m^2-m)*z,?_⟩; change m^2*(n+l)-m*mass u*mass u=_
      change (mass u)^2=n+m*l at total
      linear_combination -m*total+(m^2-m)*hz
    · simp only [ite_eq_right zero,zero_add]; refine ⟨-m*z,?_⟩; change m^2*l-m*mass u*mass u=_
      change (mass u)^2=n+m*l at total
      linear_combination -m*total-m*hz
  exact self_conjugate_coefficients v e ep inv all x

omit [DecidableEq G] in
theorem corr_affine (u:G→ℤ) (c a:ℤ) (t:G) :
    corr (fun x=>c+a*u x) t=(Fintype.card G:ℤ)*c^2+2*c*a*mass u+a^2*corr u t := by
  have eq (x:G) : (c+a*u x)*(c+a*u (x+t))=c^2+c*a*u x+c*a*u (x+t)+a^2*(u x*u (x+t)) := by ring
  simp only [corr,eq,sum_add_distrib,←mul_sum,sum_translate,sum_const,card_univ,nsmul_eq_mul,mass]
  ring

theorem reduced_flat_word (u:G→ℤ) (m n l c A n' l':ℤ) (hm:(Fintype.card G:ℤ)=m)
    (flat:∀x,corr u x=(if x=0 then n else 0)+l) (total:mass u=m*c+q*A)
    (nd:(q:ℤ)∣n) (qm:¬(q:ℤ)∣m) (e:ℕ) (ep:0<e) (inverse:Fintype.card G∣q^e+1)
    (norm:n=(q:ℤ)^2*n') (offset:l=m*c^2+2*c*q*A+(q:ℤ)^2*l') :
    ∃w:G→ℤ,mass w=A ∧ ∀t,corr w t=(if t=0 then n' else 0)+l' := by
  have inv (x:G) : q^e • x= -x := by
    have nil: (q^e+1) • x=0:=(addOrderOf_dvd_iff_nsmul_eq_zero).mp ((addOrderOf_dvd_card (x:=x)).trans inverse)
    rw [add_smul,one_smul] at nil; exact eq_neg_of_add_eq_zero_left nil
  have d (x:G) : (q:ℤ)∣u x-c := by
    have b:=flat_center_divisible u n l flat nd e ep inv x
    rw [hm,total] at b
    have z:(q:ℤ)∣m*(u x-c) := by
      convert dvd_add b (dvd_mul_right (q:ℤ) A) using 1; ring
    exact ((Nat.prime_iff_prime_int.mp (Fact.out:q.Prime)).dvd_or_dvd z).resolve_left qm
  choose w hw using d
  have eq:u=fun x=>c+q*w x := funext (fun x=>by have:=hw x; omega)
  have qnz:(q:ℤ)≠0:=by exact_mod_cast (Fact.out:q.Prime).ne_zero
  have ms:mass w=A := by
    rw [eq] at total
    simp only [mass,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,hm] at total
    apply mul_left_cancel₀ qnz; change (q:ℤ)*∑i,w i=(q:ℤ)*A; linarith only [total]
  refine ⟨w,ms,fun t=>?_⟩
  have F:=flat t
  rw [eq,corr_affine,hm,ms] at F
  apply mul_left_cancel₀ (pow_ne_zero 2 qnz)
  by_cases z:t=0 <;> simp only [z,ite_true,ite_false,zero_add] at F ⊢
  · linear_combination F+norm+offset
  · linear_combination F+offset

theorem choose_mass (u:G→ℤ) (n l M:ℤ) (flat:∀x,corr u x=(if x=0 then n else 0)+l)
    (square:M^2=n+(Fintype.card G:ℤ)*l) :
    ∃v:G→ℤ,mass v=M ∧ ∀x,corr v x=(if x=0 then n else 0)+l := by
  have h:=mass_from_flat u n l flat
  rw [←square] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with pos|neg
  · exact ⟨u,pos,flat⟩
  · exact ⟨fun x=> -u x,by simpa [mass] using congrArg Neg.neg neg,fun x=>by simpa [corr] using flat x⟩

#print axioms reduced_flat_word
#print axioms choose_mass

end Signed39.Contraction
