import SignedSevenRows
import SignedPrimeFibre

namespace Signed39.Profiles

open Finset Contraction

local instance : Fact (Nat.Prime 7):=⟨by decide⟩

theorem seven_reduction (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l c : ℤ} (hg : Fintype.card G=7*m) (cop : Nat.Coprime 7 m)
    (sq : (7*c)^2=k-l+(7:ℤ)*m*l)
    (reject : ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H], Fintype.card H=m →
      ∀ (f : ZMod 7 × H → ℤ), IsSDS k l f → mass f=7*c → False) : ¬∃f : G → ℤ, IsSDS k l f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg cop
  let H:=Additive K
  have hm : Fintype.card H=m := Nat.card_eq_fintype_card.symm.trans hK
  have h:=pullback hf E
  have am:=sds_mass h
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,Nat.cast_ofNat,←sq] at am
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp am with hp|hn
  · exact reject H hm _ h hp
  · exact reject H hm _ h.neg (by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem seven_low_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m : ℕ) (k l c inv w : ℤ) (hg : Fintype.card G=7*m) (cop : Nat.Coprime 7 m) (h4 : Nat.Coprime 28 m)
    (sq : (7*c)^2=k-l+(7:ℤ)*m*l) (hn : k-l=112) (hu : 7*inv=1+(m:ℤ)*w)
    (test : ∀L∈sevenPatterns,k<lowTotal m k l c inv (shifted c L)) : ¬∃f : G → ℤ, IsSDS k l f := by
  apply seven_reduction G hg cop sq
  intro H _ _ _ hm f hf hs
  obtain ⟨L,mem,_,_,low⟩:=seven_rows (inv:=inv) (w:=w) hf hm cop h4 hn hs hu
  exact (not_lt_of_ge low) (test L mem)

theorem no_259_160_48 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=259) : ¬∃ f : G → ℤ, IsSDS 160 48 f :=
  seven_low_exclusion G 37 160 48 16 16 3 hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem no_413_116_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=413) : ¬∃ f : G → ℤ, IsSDS 116 4 f :=
  seven_low_exclusion G 59 116 4 6 17 2 hg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

theorem no_189_128_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=189) : ¬∃f : G → ℤ, IsSDS 128 16 f := by
  apply seven_reduction G (m:=27) (c:=8) hg (by decide) (by decide)
  intro H _ _ _ hm f hf hs
  obtain ⟨L,mem,_,_,low⟩:=seven_rows (inv:=4) (w:=1) hf hm (by decide) (by decide) (by decide) hs (by decide)
  have rule : ∀L∈sevenPatterns,128<lowTotal 27 128 16 8 4 (shifted 8 L) := by decide +kernel
  exact (not_lt_of_ge low) (rule L mem)

theorem no_329_113_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=329) : ¬∃f : G → ℤ, IsSDS 113 1 f := by
  apply seven_reduction G (m:=47) (c:=3) hg (by decide) (by decide)
  intro H _ _ _ hm f hf hs
  obtain ⟨L,mem,_,_,low⟩:=seven_rows (inv:=27) (w:=4) hf hm (by decide) (by decide) (by decide) hs (by decide)
  have rule : ∀L∈sevenPatterns,113<lowTotal 47 113 1 3 27 (shifted 3 L) := by decide +kernel
  exact (not_lt_of_ge low) (rule L mem)

private def profile203 : List ℤ := [0,10,10,10,11,11,11]

theorem no_203_131_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=203) : ¬∃f : G → ℤ, IsSDS 131 19 f := by
  apply seven_reduction G (m:=29) (c:=9) hg (by decide) (by decide)
  intro H _ _ _ hm f hf hσ
  obtain ⟨L,mem,actual,localB,low⟩:=seven_rows (inv:=25) (w:=6) hf hm (by decide) (by decide) (by decide) hσ (by decide)
  have rule : ∀L∈sevenPatterns, lowTotal 29 131 19 9 25 (shifted 9 L)≤131 → shifted 9 L=profile203 := by decide +kernel
  have eq:=rule L mem low
  rw [eq] at actual localB
  let a:=rowMass f
  let b (i:ZMod 7):=energy (row f i)
  have inside (i:ZMod 7) : a i∈profile203 := actual.mem_iff.mp ((seven_mem a _).mpr ⟨i,rfl⟩)
  have weight : ∀a∈profile203,∀b∈weights 29 131 19 9 25 profile203 a,
      a=0 ∨ (a=10 ∧ b=16) ∨ (a=11 ∧ b=23) := by decide +kernel
  obtain ⟨i,ai⟩ : ∃i,a i=10 := (seven_mem a 10).mp (actual.mem_iff.mpr (by decide : (10:ℤ)∈profile203))
  have bi : b i=16 := by have h:=weight _ (inside i) _ (localB i); change _ ∨ (_∧b i=16) ∨ (_∧b i=23) at h; omega
  obtain ⟨j,aj,bj⟩ : ∃j,a j=0 ∧ b j≠0 := by
    by_contra! empty
    let F (x:ℤ):=if x=0 then (0:ℤ) else if x=10 then 16 else 23
    have same (u:ZMod 7) : b u=F (a u) := by
      rcases weight _ (inside u) _ (localB u) with zero|⟨ten,w⟩|⟨eleven,w⟩
      · simpa [F,zero] using empty u zero
      · simpa [F,ten,b] using w
      · simpa [F,eleven,b] using w
    have total : (∑u,b u)=131 := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
    have num (z : List ℤ) (h : z=profile203) : (z.map F).sum=117 := h ▸ (by decide : (profile203.map F).sum=117)
    have inputs:=(actual.map F).sum_eq
    rw [seven_map,seven_sum] at inputs
    change (∑z,F (a z))=(profile203.map F).sum at inputs
    simp only [←same] at inputs
    have hh:=num _ rfl
    omega
  have ij : i≠j := by rintro rfl; omega
  have cop : Nat.Coprime 7 (Fintype.card H) := hm ▸ (by decide : Nat.Coprime 7 29)
  have hn : (131:ℤ)-19=(7:ℤ)*16 := by decide
  obtain ⟨D,hD,self⟩:=self_pair_bound hf hn (by decide) cop i
  have exc:=two_excess_bound (inv:=25) (w:=6) hf hn (by decide) cop (by rw [hm]; decide) i j ij
  let E (z:ZMod 7):=variance (cross (row f i) (row f z))
  let R (x:ℤ):=(7:ℤ)^2*residueCost 25 29 10 x
  have suma : (∑z,R (a z))=(profile203.map R).sum := by have := (actual.map R).sum_eq; rwa [seven_map,seven_sum] at this
  have sum_num : (profile203.map R).sum=37926 := by decide
  rw [sum_num] at suma
  have vv : variance (row f i)=364 := by change (Fintype.card H:ℤ)*b i-(a i)^2=364; rw [hm,ai,bi]; decide
  rw [vv] at hD
  have dx : D=52 := by omega
  rw [hm,dx] at self
  change (7:ℤ)^2*(52^2+29*(52%28)*(28-52%28))≤28*E i at self
  norm_num at self
  dsimp only at exc
  rw [hm,vv] at exc
  change (E i-7^2*residueCost 25 29 (a i) (a i))+(E j-7^2*residueCost 25 29 (a i) (a j))≤
    (131-19)*364-(∑z,7^2*residueCost 25 29 (a i) (a z)) at exc
  rw [ai,aj] at exc
  change (E i-R 10)+(E j-R 0)≤(131-19)*364-(∑z,R (a z)) at exc
  rw [suma] at exc
  have r10 : R 10=6762 := by decide
  have r0 : R 0=0 := by decide
  rw [r10,r0] at exc
  let h:=cross (row f i) (row f j)
  have mh : mass h=0 := by rw [show mass h=a i*a j from cross_mass _ _,aj,mul_zero]
  have ev : E j=29*energy h := by change (Fintype.card H:ℤ)*energy h-(mass h)^2=_; rw [hm,mh]; ring
  have en : energy h≤0 := by omega
  have zero (x:H) : h x=0 := by
    have one : (h x)^2≤energy h := single_le_sum (fun z _=>sq_nonneg (h z)) (mem_univ x)
    nlinarith [sq_nonneg (h x-1),sq_nonneg (h x+1)]
  let : Fact (Nat.Prime 29):=⟨by decide⟩
  have unit : ¬(29:ℤ)∣mass (row f i) := by change ¬(29:ℤ)∣a i; rw [ai]; decide
  have dy := prime_fibre_invertible (q:=29) (row f i) (row f j) hm unit (fun x=>by change (29:ℤ)∣h x; rw [zero]; exact dvd_zero _)
  have vanish (x:H) : row f j x=0 := by
    have dvd:=dy x
    rcases hf.ternary (j,x) with m|z|p
    · change row f j x= -1 at m; rw [m] at dvd; norm_num at dvd
    · exact z
    · change row f j x=1 at p; rw [p] at dvd; norm_num at dvd
  exact bj (by simp [b,energy,vanish])

#print axioms no_189_128_16
#print axioms no_203_131_19
#print axioms no_329_113_1
#print axioms no_259_160_48
#print axioms no_413_116_4

end Signed39.Profiles
