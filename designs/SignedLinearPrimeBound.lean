import SignedModularSupport

/-! The square of a common prime occurring once in the norm is less than twice the norm at composite order. -/

namespace Signed39.Contraction

open Finset Signed39.ModularSupport

variable {p : ℕ} [Fact p.Prime]

private theorem subtract_constant (w : ZMod p → ZMod p) (h : ∑ i, w i=0) (a t : ZMod p) :
    rcorr (fun i => w i-a) t=rcorr w t := by
  have ht : (∑ i, w (i+t))=0 := (Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)).trans h
  calc
    _=∑ i, (w i*w (i+t)-a*w i-a*w (i+t)+a^2) := by apply sum_congr rfl; intros; ring
    _=_ := by
      simp [rcorr,sum_add_distrib,sum_sub_distrib,← mul_sum,h,ht,ZMod.card,nsmul_eq_mul]

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- No residue occurs among more than half the p row masses. -/
theorem residue_capacity {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (r : ZMod p) :
    2*(univ.filter (fun i : ZMod p => (rowMass f i:ZMod p)=r)).card ≤ p := by
  classical
  obtain ⟨c,_,_,hz,hcor⟩ := centered_row_corr hf hn
  let u := fun i : ZMod p => rowMass f i-c
  let w := fun i : ZMod p => (u i:ZMod p)
  have hsum : ∑ i, w i=0 := by
    simpa [mass,w,u] using congrArg (fun x : ℤ => (x:ZMod p)) hz
  have each (t : ZMod p) : rcorr w t = -(s:ZMod p) := by
    have h := congrArg (fun x : ℤ => (x:ZMod p)) (hcor t)
    by_cases ht : t=0 <;> simpa [rcorr,w,u,corr,ht] using h
  let b := fun i : ZMod p => (rowMass f i:ZMod p)-r
  have form : b = fun i => w i-(r-(c:ZMod p)) := by
    funext i; simp [b,w,u]
  have flat (t : ZMod p) : rcorr b t = -(s:ZMod p) := by rw [form,subtract_constant w hsum,each]
  have ns : -(s:ZMod p)≠0 := neg_ne_zero.mpr (fun h => hs ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h))
  have cap := support_lower b (-(s:ZMod p)) ns flat
  simp only [b,ne_eq,sub_eq_zero] at cap
  have hcount := card_filter_add_card_filter_not (s:=univ) (fun i : ZMod p => (rowMass f i:ZMod p)=r)
  rw [card_univ,ZMod.card] at hcount
  omega

omit [DecidableEq H] in
private theorem unique_constant_mass {s c : ℤ} {f : ZMod p × H → ℤ}
    (hen : energy (fun i => rowMass f i-c)=((p:ℤ)-1)*s) (hsmall : 2*s ≤ (p:ℤ))
    (hm : p < Fintype.card H) (i j : ZMod p)
    (hi : ∀ x, row f i x=row f i 0) (hj : ∀ x, row f j x=row f j 0) :
    rowMass f i=rowMass f j := by
  classical
  let m : ℤ := Fintype.card H
  let P : ℤ := p
  let D := fun z : ZMod p => (rowMass f z-c)^2
  by_contra uneq
  have hij : i≠j := fun eq => uneq (eq ▸ rfl)
  have pair : D i+D j ≤ ∑ z, D z := calc
    _ = ∑ z ∈ ({i,j} : Finset (ZMod p)), D z := by simp [hij]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z _ _ => sq_nonneg _)
  change ∑ z, D z=(P-1)*s at hen
  rw [hen] at pair
  change (rowMass f i-c)^2+(rowMass f j-c)^2≤(P-1)*s at pair
  have up : (rowMass f i-rowMass f j)^2≤2*((P-1)*s) := by
    nlinarith [sq_nonneg ((rowMass f i-c)+(rowMass f j-c))]
  have ai : rowMass f i=m*row f i 0 := by simp [rowMass,mass,hi,m]
  have aj : rowMass f j=m*row f j 0 := by simp [rowMass,mass,hj,m]
  let z := row f i 0-row f j 0
  have repr : rowMass f i-rowMass f j=m*z := by rw [ai,aj]; dsimp [z]; ring
  have nonzero : z≠0 := by intro hz; apply uneq; apply sub_eq_zero.mp; rw [repr,hz,mul_zero]
  have sq : 1≤z^2 := by have := sq_pos_of_ne_zero nonzero; omega
  have down : m^2≤(rowMass f i-rowMass f j)^2 := by rw [repr,mul_pow]; nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr sq)]
  have pp : 2≤P := by dsimp [P]; exact_mod_cast (Fact.out : p.Prime).two_le
  have mp : P < m := by dsimp [P,m]; exact_mod_cast hm
  change 2*s≤P at hsmall
  nlinarith [mul_le_mul_of_nonneg_left hsmall (by omega : 0≤P-1),
    mul_pos (sub_pos.mpr mp) (show 0 < m+P by omega)]

/-- Suppose p|v and p∥n. If the group order exceeds p, then p<2(n/p). -/
theorem product_linear_prime_bound {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (hc : p.Coprime (Fintype.card H))
    (hm : 1 < Fintype.card H) : (p:ℤ)<2*s := by
  classical
  by_contra! small
  have prime : p.Prime := Fact.out
  have pos : (0:ℤ)<p := by exact_mod_cast prime.pos
  have greater := cofactor_bound hf hn hs hc hm
  have podd : Odd p := prime.odd_of_ne_two (by
    rintro rfl
    have sq := even_norm_square hf (by simp [Fintype.card_prod,ZMod.card])
    exact nonsquare_of_valuation_one prime hs (hn ▸ sq))
  let C := univ.filter (fun i : ZMod p => ∀ x, row f i x=row f i 0)
  have count : (p:ℤ)-s ≤ (C.card:ℤ) := constant_row_count hf hn hs hc hm
  obtain ⟨i,hi⟩ := (show C.Nonempty from card_pos.mp (by omega))
  obtain ⟨c,_,_,_,cc⟩ := centered_row_corr hf hn
  have en : energy (fun z => rowMass f z-c)=((p:ℤ)-1)*s := by rw [energy_zero,cc]; simp; ring
  let A := (rowMass f i:ZMod p)
  let matching := univ.filter (fun z : ZMod p => (rowMass f z:ZMod p)=A)
  have subset : C⊆matching := by
    intro j hj
    have eq := unique_constant_mass en small greater j i
      (mem_filter.mp hj).2 (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,congrArg (fun z : ℤ => (z:ZMod p)) eq⟩
  have upper : 2*matching.card≤p := residue_capacity hf hn hs A
  have smaller := card_le_card subset
  obtain ⟨q,hq⟩ := podd
  omega

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem abelian_linear_prime_bound {k lam s : ℤ} {p m : ℕ} [Fact p.Prime] {f : G → ℤ}
    (hf : IsSDS k lam f) (hG : Fintype.card G=p*m) (hm : 1 < m)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) : (p:ℤ)<2*s := by
  classical
  have cop := valuation_one_coprime hf hG hn hs
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hG cop
  have size : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  exact product_linear_prime_bound (pullback hf e) hn hs (size ▸ cop) (size ▸ hm)

#print axioms residue_capacity
#print axioms abelian_linear_prime_bound

end Signed39.Contraction

