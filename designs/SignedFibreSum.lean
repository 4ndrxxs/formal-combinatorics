import SignedLongMultiplier

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {p:ℕ} [Fact p.Prime]

omit [DecidableEq H] in
theorem project_matched (f g:ZMod p×H→ℤ) (i:ZMod p) :
    (∑x:H,matched f g (i,x))=matched (rowMass f) (rowMass g) i := by
  simp only [matched_shift,Fintype.sum_prod_type,Prod.mk_add_mk]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  calc
    _=∑y:H,rowMass f (i+j)*g (j,y) := by
      apply sum_congr rfl; intro y _
      rw [←sum_mul]
      congr 1
      exact Fintype.sum_equiv (Equiv.addRight y) _ _ (fun x=>rfl)
    _=_ := by simp [rowMass,row,mass,mul_sum]

omit [DecidableEq H] in
theorem projected_scalar (f:ZMod p×H→ℤ) (A:ZMod p≃+ZMod p) (B:H≃+H) :
    rowMass (fun x=>f ((A.prodCongr B).symm x))=fun i=>rowMass f (A.symm i) := by
  funext i
  exact Fintype.sum_equiv B.symm.toEquiv _ _ (fun x=>rfl)

omit [AddCommGroup H] [DecidableEq H] in
theorem uniform_fibre_divides (T:ZMod p×H→ℤ) (cop:p.Coprime (Fintype.card H))
    (same:∀i t u,(p:ℤ)∣T (i,t)-T (i,u)) (all:∀i,(p:ℤ)∣∑u:H,T (i,u)) (x:ZMod p×H) :
    (p:ℤ)∣T x := by
  obtain ⟨i,t⟩:=x
  have diff:=dvd_sum (s:=univ) (fun u _=>same i t u)
  rw [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul] at diff
  have prod:(p:ℤ)∣(Fintype.card H:ℤ)*T (i,t) := by simpa using dvd_add diff (all i)
  exact ((Nat.prime_iff_prime_int.mp (Fact.out:p.Prime)).dvd_or_dvd prod).resolve_left
    (fun h=>((Fact.out:p.Prime).coprime_iff_not_dvd.mp cop) (by exact_mod_cast h))

theorem fixed_quotient_multiplier {k l s:ℤ} {f:ZMod p×H→ℤ} (hf:IsSDS k l f)
    (hn:k-l=(p:ℤ)*s) (hs:¬(p:ℤ)∣s) (pos:0<s) (cop:p.Coprime (Fintype.card H))
    (B:H≃+H) (r:ℕ) (act:∀x:H,p^r • x=B x)
    (aux:∀t,s∣matched (fun x=>f (((AddEquiv.refl (ZMod p)).prodCongr B).symm x)) f t-l) :
    ∃t:ZMod p×H,∀x,f (((AddEquiv.refl (ZMod p)).prodCongr B).symm x)=f (x-t) := by
  let A:=AddEquiv.refl (ZMod p)
  let E:=A.prodCongr B
  let T:=fun t=>matched (fun x=>f (E.symm x)) f t-l
  have flat (x:ZMod p×H) : corr f x=(if x=0 then k-l else 0)+l := by rw [hf.flat]; split <;> omega
  have same (i:ZMod p) (t u:H) : (p:ℤ)∣T (i,t)-T (i,u) := by
    simpa only [T,E,sub_sub_sub_cancel_right] using horizontal_frobenius hf hn hs cop A B r act i t u
  have projected (i:ZMod p) : (∑u:H,T (i,u))=(if i=0 then (p:ℤ)*s else 0) := by
    simp only [T,sum_sub_distrib,project_matched,projected_scalar,sum_const,card_univ,nsmul_eq_mul,E,A,
      AddEquiv.refl_symm,AddEquiv.refl_apply]
    have eq : matched (rowMass f) (rowMass f) i=corr (rowMass f) i := by
      rw [matched_shift]; simp only [corr]; apply sum_congr rfl; intro x _; rw [add_comm i x,mul_comm]
    rw [eq,rowmass_corr hf,hn]; ring
  have dp (i:ZMod p) : (p:ℤ)∣∑u:H,T (i,u) := by rw [projected]; split <;> simp
  have dv (x:ZMod p×H) : k-l∣T x := by
    rw [hn]
    obtain ⟨z,hz⟩:=aux x
    have d:=uniform_fibre_divides T cop same dp x
    change T x=s*z at hz
    rw [hz] at d
    obtain ⟨a,ha⟩:=((Nat.prime_iff_prime_int.mp (Fact.out:p.Prime)).dvd_or_dvd d).resolve_left hs
    exact ⟨a,by rw [hz,ha]; ring⟩
  have pn:(0:ℤ)<p := by exact_mod_cast (Fact.out:p.Prime).pos
  exact integral_match_translation f _ _ (hn ▸ mul_pos pn pos) flat E dv

#print axioms fixed_quotient_multiplier

end Signed39.Contraction
