import SignedLongCertificate

namespace Signed39.Contraction

def factorProduct (L:List AuxPower) : ℕ := (L.map (fun z=>z.q^z.j)).prod

def compatibleFactors (order t norm:ℕ) : List AuxPower → Prop
  | [] => True
  | z::zs => powerConditions order t norm z ∧ (z.q^z.j).Coprime (factorProduct zs) ∧
      compatibleFactors order t norm zs

theorem all_aux_dvd {G:Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (f:G→ℤ)
    (v t n:ℕ) (l:ℤ) (flat:∀x,corr f x=(if x=0 then (n:ℤ) else 0)+l)
    (E:G≃+G) (hg:Fintype.card G=v) (act:∀x:G,t • x=E x) (L:List AuxPower)
    (good:compatibleFactors v t n L) (x:G) :
    (factorProduct L:ℤ)∣matched (fun y=>f (E.symm y)) f x-l := by
  induction L with
  | nil=>simp [factorProduct]
  | cons z zs ih=>
    obtain ⟨h,c,tail⟩:=good
    have prod:(factorProduct (z::zs):ℤ)=(z.q:ℤ)^z.j*(factorProduct zs:ℤ) := by simp [factorProduct]
    rw [prod]
    have cp:IsCoprime ((z.q:ℤ)^z.j) (factorProduct zs:ℤ) := by simpa using c.isCoprime
    exact cp.mul_dvd (aux_dvd f v t n l flat E hg act z h x) (ih tail)

theorem prime_fibre_multiplier {H:Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p m s t r inv:ℕ) [Fact p.Prime] {k l:ℤ} {f:ZMod p×H→ℤ} (hf:IsSDS k l f)
    (hm:Fintype.card H=m) (hn:k-l=(p:ℤ)*s) (hs:¬p∣s) (pos:0<s) (cop:p.Coprime m)
    (first:t ≡ 1 [MOD p]) (rest:p^r ≡ t [MOD m]) (inverse:t*inv ≡ 1 [MOD m])
    (L:List AuxPower) (product:factorProduct L=s) (good:compatibleFactors (p*m) t (p*s) L) :
    ∃g:ZMod p×H,∀x,f (t • x+g)=f x := by
  let B:=scalarPerm (H:=H) t inv (hm ▸ inverse)
  let E:=(AddEquiv.refl (ZMod p)).prodCongr B
  have total:Fintype.card (ZMod p×H)=p*m:=by rw [Fintype.card_prod,ZMod.card,hm]
  have act (x:ZMod p×H) : t • x=E x := by
    apply Prod.ext
    · change t • x.1=x.1
      exact (scalar_congr (by rwa [ZMod.card]) x.1).trans (one_nsmul _)
    · rfl
  have flat (x:ZMod p×H) : corr f x=(if x=0 then ((p*s:ℕ):ℤ) else 0)+l := by
    rw [hf.flat]; push_cast; split <;> omega
  have aux (z:ZMod p×H) : (s:ℤ)∣matched (fun x=>f (E.symm x)) f z-l := by
    rw [←product]; exact all_aux_dvd f _ _ _ _ flat E total act L good z
  obtain ⟨g,tr⟩:=fixed_quotient_multiplier hf hn (by exact_mod_cast hs) (by exact_mod_cast pos) (hm ▸ cop)
    B r (fun x=>scalar_congr (hm ▸ rest) x) aux
  refine ⟨-g,fun x=>?_⟩
  have row:=tr (E x)
  change f (E.symm (E x))=f (E x-g) at row
  rw [E.symm_apply_apply] at row
  simpa only [act,←sub_eq_add_neg] using row.symm

#print axioms all_aux_dvd
#print axioms prime_fibre_multiplier

end Signed39.Contraction
