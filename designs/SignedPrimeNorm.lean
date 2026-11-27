import SignedObstruction

/-! Variance concentration when the common prime equals the order of a signed difference set. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

def row (f : ZMod p × H → ℤ) (i : ZMod p) (x : H) : ℤ := f (i,x)
def rowMass (f : ZMod p × H → ℤ) (i : ZMod p) : ℤ := mass (row f i)

omit [DecidableEq H] in
theorem energy_zero (f : H → ℤ) : energy f = corr f 0 := by simp [energy,corr,pow_two]

theorem sds_mass {k lam : ℤ} {f : H → ℤ} (hf : IsSDS k lam f) :
    (mass f)^2 = k-lam+(Fintype.card H:ℤ)*lam := by
  apply mass_from_flat
  intro t
  rw [hf.flat]
  split <;> omega

theorem rowmass_corr {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f) (t : ZMod p) :
    corr (rowMass f) t = (if t=0 then k-lam else 0)+(Fintype.card H:ℤ)*lam := by
  exact fiber_flat (pullback hf (AddEquiv.prodComm : H × ZMod p ≃+ ZMod p × H)) t

theorem total_row_variance {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f) :
    ∑ i : ZMod p, variance (row f i) = ((Fintype.card H:ℤ)-1)*(k-lam) := by
  have he : ∑ i : ZMod p, energy (row f i) = k := by
    simpa [energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have hs : ∑ i : ZMod p, (mass (row f i))^2 = k-lam+(Fintype.card H:ℤ)*lam := by
    change energy (rowMass f) = _
    simpa only [energy_zero,ite_true] using rowmass_corr hf 0
  simp only [variance,sum_sub_distrib, ← mul_sum,he,hs]
  ring

omit [AddCommGroup H] [DecidableEq H] in
theorem mass_rowmass (f : ZMod p × H → ℤ) : mass (rowMass f) = mass f := by
  simp [mass,rowMass,row,Fintype.sum_prod_type]

theorem row_variance_lower {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hc : p.Coprime (Fintype.card H)) (hm : 1 < Fintype.card H)
    {i : ZMod p} {x y : H} (hxy : f (i,x) ≠ f (i,y)) :
    (p:ℤ)*((Fintype.card H:ℤ)-1) ≤ variance (row f i) := by
  have hp : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨b,hb⟩ := row_scale hf (hn ▸ dvd_refl _) hc i
  rw [hn,pow_two,mul_assoc] at hb
  have eq : (p:ℤ)*variance b = variance (row f i) := mul_left_cancel₀ hp.ne' hb
  have hmin := variance_minimum (row f i) hxy
  have hv : 0 < variance (row f i) := by omega
  have hbpos : 0 < variance b := by rw [← eq] at hv; exact (mul_pos_iff_of_pos_left hp).mp hv
  obtain ⟨r,s,hrs⟩ : ∃ r s : H, b r ≠ b s := by
    by_contra! h
    exact hbpos.ne' (variance_constant b (b 0) (fun r => h r 0))
  rw [← eq]
  exact mul_le_mul_of_nonneg_left (variance_minimum b hrs) hp.le

theorem remaining_rows_constant {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hc : p.Coprime (Fintype.card H)) (hm : 1 < Fintype.card H) :
    ∃ j : ZMod p, ∀ i, i ≠ j → ∀ x, f (i,x) = f (i,0) := by
  have hp : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨j,x,y,hxy⟩ := varying_row hf (by omega) hm
  refine ⟨j,?_⟩
  have he := total_row_variance hf
  rw [hn,mul_comm] at he
  have lower := row_variance_lower hf hn hc hm hxy
  intro i hij z
  by_contra hnz
  have hi := variance_minimum (row f i) hnz
  have hle : variance (row f i) ≤ ∑ u ∈ univ.erase j, variance (row f u) :=
    single_le_sum (fun u _ => variance_nonneg (row f u)) (mem_erase.mpr ⟨hij, mem_univ _⟩)
  have hsum := sum_erase_add (s := univ) (fun u => variance (row f u)) (mem_univ j)
  omega

/-- A centered integer vector of energy p−1, whose p−1 ordinary entries are
nonzero modulo m, contains an ordinary entry of each sign. -/
theorem centering_bound (a : ZMod p → ℤ) (m c : ℤ) (j : ZMod p)
    (hc : ¬m ∣ c) (hm : ∀ i, i ≠ j → m ∣ a i)
    (hzero : ∑ i, (a i-c) = 0) (hen : ∑ i, (a i-c)^2 = (p:ℤ)-1) : m ≤ 2 := by
  classical
  let d := fun i => a i-c
  let unit := fun i : ZMod p => if i=j then (0:ℤ) else 1
  have units (i : ZMod p) : unit i ≤ (d i)^2 := by
    by_cases h : i=j
    · simp [unit,h,sq_nonneg]
    · have hd : d i ≠ 0 := fun e => hc ((sub_eq_zero.mp e) ▸ hm i h)
      have hs := sq_pos_of_ne_zero hd
      simp only [unit,ite_eq_right h]
      omega
  have sumunits : (∑ i : ZMod p, unit i) = (p:ℤ)-1 := by
    simp [unit,sum_ite,filter_ne',card_erase_of_mem,ZMod.card,Nat.cast_sub (Fact.out : p.Prime).one_le]
  have eq (i : ZMod p) : d i ^ 2 = unit i := by
    have hz : ∑ t : ZMod p, (d t^2-unit t) = 0 := by rw [sum_sub_distrib,sumunits]; exact sub_eq_zero.mpr hen
    have hle : d i^2-unit i ≤ ∑ t : ZMod p, (d t^2-unit t) :=
      single_le_sum (fun t _ => sub_nonneg.mpr (units t)) (mem_univ i)
    rw [hz] at hle
    exact le_antisymm (by omega) (units i)
  have dj : d j=0 := by have h := eq j; simp [unit] at h; exact h
  have signs (i : ZMod p) (hi : i≠j) : d i=1 ∨ d i= -1 := by
    have he : d i^2=1 := by simpa [unit,hi] using eq i
    rcases le_total (d i) 0 with h|h <;> [right; left] <;> nlinarith
  have hp : 1 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨x,hx,ex⟩ : ∃ i, i ≠ j ∧ d i=1 := by
    by_contra! h
    have all (i : ZMod p) : d i = -(unit i) := by
      by_cases hi : i=j
      · simp [hi,dj,unit]
      · simp [unit,hi,(signs i hi).resolve_left (h i hi)]
    have ht : (∑ i, d i) = -((p:ℤ)-1) := by simp only [all,sum_neg_distrib,sumunits]
    change (∑ i, d i)=0 at hzero
    omega
  obtain ⟨y,hy,ey⟩ : ∃ i, i ≠ j ∧ d i= -1 := by
    by_contra! h
    have all (i : ZMod p) : d i = unit i := by
      by_cases hi : i=j
      · simp [hi,dj,unit]
      · simp [unit,hi,(signs i hi).resolve_right (h i hi)]
    have ht : (∑ i, d i) = (p:ℤ)-1 := by simp only [all,sumunits]
    change (∑ i, d i)=0 at hzero
    omega
  have he : a x - a y = 2 := by dsimp [d] at ex ey; omega
  have hd := dvd_sub (hm x hx) (hm y hy)
  rw [he] at hd
  exact Int.le_of_dvd (by decide) hd

theorem prime_norm_cofactor_le_two {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hc : p.Coprime (Fintype.card H)) (hm : 1 < Fintype.card H) :
    Fintype.card H ≤ 2 := by
  let m : ℤ := Fintype.card H
  let a := rowMass f
  have hp : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨j,hj⟩ := remaining_rows_constant hf hn hc hm
  obtain ⟨c,hc'⟩ := mass_dvd hf (hn ▸ dvd_refl _)
  change mass f = p*c at hc'
  have he := sds_mass hf
  rw [hc',hn,Fintype.card_prod,ZMod.card,Nat.cast_mul] at he
  change ((p:ℤ)*c)^2 = p + ((p:ℤ)*m)*lam at he
  have eq : (p:ℤ)*c^2=1+m*lam := by
    apply mul_left_cancel₀ hp.ne'
    linear_combination he
  have hnc : ¬ m ∣ c := by
    rintro ⟨z,hz⟩
    have hh : m ∣ 1 := ⟨(p:ℤ)*m*z^2-lam, by rw [hz] at eq; linear_combination -eq⟩
    have bound := Int.le_of_dvd (by decide : (0:ℤ)<1) hh
    dsimp [m] at bound
    omega
  have hdiv (i : ZMod p) (hi : i ≠ j) : m ∣ a i := by
    refine ⟨f (i,0),?_⟩
    simp [a,rowMass,mass,row,hj i hi,m]
  have hsum : (∑ i : ZMod p, a i) = p*c := (mass_rowmass f).trans hc'
  have hs : (∑ i : ZMod p, (a i)^2) = (p:ℤ)+m*lam := by
    change energy (rowMass f) = _
    simpa only [← energy_zero,ite_true,hn] using rowmass_corr hf 0
  have deviation : (∑ i, (a i-c)) = 0 := by
    simp [sum_sub_distrib,hsum,ZMod.card]
  have centered : (∑ i, (a i-c)^2) = (p:ℤ)-1 := by
    calc
      _ = ∑ i : ZMod p, ((a i)^2+c^2-2*c*a i) := by apply sum_congr rfl; intro i _; ring
      _ = _ := by
        simp only [sum_sub_distrib,sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,
          ← mul_sum,hs,hsum]
        linear_combination -eq
  have h := centering_bound a m c j hnc hdiv deviation centered
  change (Fintype.card H:ℤ) ≤ (2:ℤ) at h
  exact_mod_cast h

/-- The nonprincipal character of a group of order two has integral values. -/
theorem two_flat_square (s : H → ℤ) {n l : ℤ} (hm : Fintype.card H=2)
    (hh : ∀ t, corr s t = (if t=0 then n else 0)+l) : IsSquare n := by
  have hc : Nat.card H=2 := (Nat.card_eq_fintype_card).trans hm
  let e : ZMod 2 ≃+ H := (ZMod.ringEquivCongr hc.symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hc))
  let a := fun t : ZMod 2 => s (e t)
  have cor (t : ZMod 2) : corr a t = corr s (e t) := by
    apply Fintype.sum_equiv e.toEquiv
    intro i
    simp [a]
  have hz := (cor 0).trans (hh (e 0))
  have ho := (cor 1).trans (hh (e 1))
  simp only [map_zero,ite_true] at hz
  have hn : e 1 ≠ 0 := fun h => (by decide : (1:ZMod 2) ≠ 0) (e.injective (h.trans e.map_zero.symm))
  simp only [ite_eq_right hn,zero_add] at ho
  have c0 : corr a 0 = (a 0)^2+(a 1)^2 := by
    change (∑ i : Fin 2, a i*a (i+(0:Fin 2))) = _
    simp [Fin.sum_univ_two,pow_two]
    rfl
  have c1 : corr a 1 = 2*a 0*a 1 := by
    change (∑ i : Fin 2, a i*a (i+(1:Fin 2))) = _
    simp only [Fin.sum_univ_two]
    change a 0*a 1 + a 1*a 0 = _
    ring
  refine ⟨a 0-a 1,?_⟩
  rw [c0] at hz
  rw [c1] at ho
  linear_combination ho-hz

theorem no_prime_norm_product {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hc : p.Coprime (Fintype.card H)) (hm : 1 < Fintype.card H) : False := by
  have bound := prime_norm_cofactor_le_two hf hn hc hm
  have hs := two_flat_square (fiber f) (by omega) (fiber_flat hf)
  rw [hn] at hs
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_isSquare hs

#print axioms no_prime_norm_product

end Signed39.Contraction
