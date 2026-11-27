import SignedClassicalMultiplier
import SignedSplit

/-! A residue class test for the multiplier on a quotient of prime order. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [Fintype H] [DecidableEq H]

theorem orbit_mass_dvd (e : H ≃ H) (g W : H → ℤ) (d : ℤ) (base : H) (fix : ∀x, g (e x)=g x)
    (weight : ∀x, d∣(if x=base then (0:ℤ) else 1)+W (e x)-W x) : d∣mass g-g base := by
  have all := dvd_sum (s:=univ) (fun x _ => dvd_mul_of_dvd_left (weight x) (g x))
  have translate : (∑ x, W (e x)*g x)=∑ x, W x*g x := by
    calc
      _=∑ x, W (e x)*g (e x) := by simp only [fix]
      _=_ := Fintype.sum_equiv e _ _ (fun _=>rfl)
  have bit (x : H) : (if x=base then (0:ℤ) else 1)*g x=g x-(if x=base then g base else 0) := by
    by_cases h : x=base <;> simp [h]
  simpa only [sub_mul,add_mul,bit,sum_sub_distrib,sum_add_distrib,translate,
    sum_ite_eq',mem_univ,ite_true,add_sub_cancel_right,mass] using all

variable {r q : ℕ} [Fact r.Prime] [Fact q.Prime]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def threeEquiv (nz : (3:ZMod r)≠0) : ZMod r ≃+ ZMod r where
  toFun x := 3*x
  invFun x := 3⁻¹*x
  left_inv x := by simp only [← mul_assoc,inv_mul_cancel₀ nz,one_mul]
  right_inv x := by simp only [← mul_assoc,mul_inv_cancel₀ nz,one_mul]
  map_add' := by intro x y; ring

def orbitCertificate (r q e d : ℕ) [NeZero r] (mass : ℤ) (W : ℕ → ℤ) : Prop :=
  r.Prime ∧ q.Prime ∧ Nat.Coprime 3 q ∧ ¬3∣r ∧ ¬q∣r ∧ (2:ZMod r)≠0 ∧ (3:ZMod r)≠0 ∧
  q^e≡3 [MOD r] ∧
  (∀x : ZMod r, (d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W (3*x).val-W x.val) ∧
  ∀ j : Fin 7, ¬(d:ℤ)∣mass-((j.val:ℤ)-3)

instance (r q e d : ℕ) [NeZero r] (m : ℤ) (W : ℕ → ℤ) : Decidable (orbitCertificate r q e d m W) := by
  unfold orbitCertificate; infer_instance

theorem semiprime_three_orbit {e d : ℕ} {mass0 l : ℤ} (W : ℕ → ℤ) (cert : orbitCertificate r q e d mass0 W)
    (u : ZMod r → ℤ) (flat : ∀t, corr u t=(if t=0 then (3:ℤ)*q else 0)+l)
    (hmass : mass u=mass0) (bound : ∀x, -3≤u x ∧ u x≤3) : False := by
  obtain ⟨rp,qp,cp,nd3,ndq,nz2,nz3,power,check,miss⟩ := cert
  let E := threeEquiv nz3
  have c3 : ¬(3:ℤ)∣(Fintype.card (ZMod r):ℤ) := by rw [ZMod.card]; exact_mod_cast nd3
  have cq : ¬(q:ℤ)∣(Fintype.card (ZMod r):ℤ) := by rw [ZMod.card]; exact_mod_cast ndq
  have powE (x : ZMod r) : q^e • x=E x := by
    change q^e • x=(3:ZMod r)*x
    rw [nsmul_eq_mul,(ZMod.natCast_eq_natCast_iff _ _ r).mpr power]
    rfl
  have div (t : ZMod r) : (3:ℤ)*q∣matched (fun x=>u (E.symm x)) u t-l := by
    apply cp.isCoprime.mul_dvd
    · exact prime_multiplier_dvd u _ l flat (dvd_mul_right _ _) c3 E 1 (fun x=>by simp [E,threeEquiv,nsmul_eq_mul]) t
    · exact prime_multiplier_dvd u _ l flat (dvd_mul_left _ _) cq E e powE t
  have npos : (0:ℤ)<3*(q:ℤ) := by exact_mod_cast (Nat.mul_pos (by decide : 0<3) qp.pos)
  obtain ⟨t,ht⟩ := integral_match_translation u _ l npos flat E div
  let base : ZMod r := t/2
  let g (x : ZMod r) := u (x+base)
  have twice : 2*base=t := by dsimp [base]; field_simp
  have fix (x : ZMod r) : g (E x)=g x := by
    have h := ht (E (x+base))
    rw [E.symm_apply_apply] at h
    change u (x+base)=u (3*(x+base)-t) at h
    change u (3*x+base)=u (x+base)
    rw [show 3*(x+base)-t=3*x+base by linear_combination twice] at h
    exact h.symm
  have dvd := orbit_mass_dvd E.toEquiv g (fun x=>W x.val) (d:ℤ) 0 fix check
  have mg : mass g=mass0 := (sum_translate u base).trans hmass
  change (d:ℤ)∣mass g-u (0+base) at dvd
  rw [mg,zero_add] at dvd
  obtain ⟨lo,hi⟩ := bound base
  let j : Fin 7 := ⟨(u base+3).toNat,by omega⟩
  have eq : (j.val:ℤ)-3=u base := by dsimp [j]; omega
  exact miss j (eq ▸ dvd)

theorem abelian_semiprime_three (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (r q e d : ℕ) [NeZero r] (k l mass0 : ℤ) (W : ℕ → ℤ) (hg : Fintype.card G=r*3)
    (hn : k-l=(3:ℤ)*q) (sq : mass0^2=k-l+(r:ℤ)*3*l)
    (cert : orbitCertificate r q e d mass0 W) : ¬∃ f : G → ℤ, IsSDS k l f := by
  classical
  have : Fact r.Prime := ⟨cert.1⟩
  have : Fact q.Prime := ⟨cert.2.1⟩
  have cop : r.Coprime 3 := (Nat.coprime_comm.mp ((show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr cert.2.2.2.1))
  obtain ⟨K,hK,⟨E⟩⟩ := split_prime_factor hg cop
  have hm : Fintype.card (Additive K)=3 := Nat.card_eq_fintype_card.symm.trans hK
  rintro ⟨f,hf⟩
  let F := fun x=>f (E x)
  have hF : IsSDS k l F := pullback hf E
  have m2 : (mass F)^2=mass0^2 := by
    have h := sds_mass hF
    rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,Nat.cast_ofNat] at h
    exact h.trans sq.symm
  obtain ⟨g,hg,mg⟩ : ∃ g : ZMod r × Additive K → ℤ, IsSDS k l g ∧ mass g=mass0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp m2 with h|h
    · exact ⟨F,hF,h⟩
    · exact ⟨fun x=> -F x,hF.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using h⟩
  apply semiprime_three_orbit W cert (rowMass g) (l:=(3:ℤ)*l) (fun t=>by simpa [hm,hn] using rowmass_corr hg t)
    ((mass_rowmass g).trans mg)
  intro x
  have le := sum_le_sum (s:=univ) (fun t _=>show g (x,t)≤1 by rcases hg.ternary (x,t) with h|h|h <;> omega)
  have ge := sum_le_sum (s:=univ) (fun t _=>show -1≤g (x,t) by rcases hg.ternary (x,t) with h|h|h <;> omega)
  simp only [sum_const,card_univ,nsmul_eq_mul,hm,Nat.cast_ofNat] at le ge
  exact ⟨by change _ ≤ ∑ t,g (x,t); linarith,by change (∑ t,g (x,t)) ≤ _; linarith⟩

#print axioms abelian_semiprime_three

end Signed39.Contraction
