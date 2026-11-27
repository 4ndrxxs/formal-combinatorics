import SignedWeightedMultiplier

namespace Signed39.Contraction

open Finset

variable {G H:Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem normalized_proj_word {k l:ℤ} {f:G→ℤ} (hf:IsSDS k l f)
    (φ:G→+H) (surj:Function.Surjective φ) (v m a:ℕ) (n o M:ℤ)
    (hg : Fintype.card G = v) (hh : Fintype.card H = m) (hmpos : 0 < m) (quo : v = a*m)
    (norm:k-l=n) (off:(a:ℤ)*l=o) (square:M^2=n+(m:ℤ)*o) :
    ∃u:H→ℤ,mass u=M ∧ ∀z,corr u z=(if z=0 then n else 0)+o := by
  have kard:=AddSubgroup.card_ker_mul_card_of_surjective surj
  rw [Nat.card_eq_fintype_card (α:=G),hg,Nat.card_eq_fintype_card (α:=H),hh,quo] at kard
  have ker:Nat.card φ.ker=a:=Nat.eq_of_mul_eq_mul_right hmpos kard
  refine choose_mass (projected φ f) n o M (fun z=>?_) (by simpa [hh] using square)
  simpa only [norm,ker,off] using projected_flat φ surj hf z

omit [DecidableEq G] in
theorem exists_quotient_249 (h3:3∣Fintype.card G) (h83:83∣Fintype.card G) :
    ∃φ:G→+ZMod 249,Function.Surjective φ := by
  obtain ⟨a,ha⟩:=exists_prime_quotient 3 (by decide) h3
  obtain ⟨b,hb⟩:=exists_prime_quotient 83 (by decide) h83
  let π:=a.prod b
  have onto:Function.Surjective π := by
    rintro ⟨x,y⟩
    obtain ⟨u,hu⟩:=ha x
    obtain ⟨v,hv⟩:=hb y
    refine ⟨166 • u+84 • v,Prod.ext ?_ ?_⟩
    · change a (166 • u+84 • v)=x
      simp only [map_add,map_nsmul,nsmul_eq_mul,hu]
      rw [show ((166:ℕ):ZMod 3)=1 by decide,show ((84:ℕ):ZMod 3)=0 by decide]; simp
    · change b (166 • u+84 • v)=y
      simp only [map_add,map_nsmul,nsmul_eq_mul,hv]
      rw [show ((166:ℕ):ZMod 83)=0 by decide,show ((84:ℕ):ZMod 83)=1 by decide]; simp
  let e:ZMod 249≃+ZMod 3×ZMod 83:=(ZMod.chineseRemainder (by decide : Nat.Coprime 3 83)).toAddEquiv
  exact ⟨e.symm.toAddMonoidHom.comp π,e.symm.surjective.comp onto⟩

omit [DecidableEq G] in
theorem coeff_square_le (u:G→ℤ) (x:G) : (u x)^2≤corr u 0 := by
  simpa [corr,pow_two] using (Finset.single_le_sum (s:=univ) (f:=fun y=>u y*u y)
    (fun y _=>mul_self_nonneg (u y)) (mem_univ x))

omit [DecidableEq G] [DecidableEq H] in
theorem integral_pullback_corr (u:G→ℤ) (e:H≃+G) (x:H) : corr (fun y=>u (e y)) x=corr u (e x) := by
  unfold corr
  exact Fintype.sum_equiv e.toEquiv _ _ (fun y=>by simp)

#print axioms normalized_proj_word
#print axioms exists_quotient_249

end Signed39.Contraction

