import SignedSevenProfiles

namespace Signed39.Profiles

open Finset Contraction

theorem seven_map (u : ZMod 7 → ℤ) (g : ℤ → ℤ) : (seven u).map g=seven (fun i=>g (u i)) := rfl

theorem seven_mem (u : ZMod 7 → ℤ) (a : ℤ) : a∈seven u ↔ ∃i,u i=a := by
  constructor
  · intro h
    simp only [seven,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨_,rfl⟩
  · rintro ⟨i,rfl⟩
    have all : ∀j : ZMod 7,j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6 := by decide
    rcases all i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [seven]

def shifted (c : ℤ) (L : List ℤ) := L.map (fun d=>c+d)

def weights (m : ℕ) (k l c inv : ℤ) (A : List ℤ) (a : ℤ) : List ℤ :=
  ((List.range (m+1)).map (fun b : ℕ=>(b:ℤ))).filter (fun b=>
    decide (rowBudget 7 m k c a b ∧ admissibleRow 7 m 16 l c a b ∧ admissibleShift 7 m a b ∧ admissibleFull 7 m a b ∧
      7*(A.map (residueCost inv m a)).sum≤16*((m:ℤ)*b-a^2)))

def lowerWeight (k : ℤ) : List ℤ → ℤ
  | [] => k+1
  | a::as => min a (lowerWeight k as)

theorem lowerWeight_le {k x : ℤ} {xs : List ℤ} (h : x∈xs) : lowerWeight k xs≤x := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

def lowTotal (m : ℕ) (k l c inv : ℤ) (A : List ℤ) : ℤ := (A.map (fun a=>lowerWeight k (weights m k l c inv A a))).sum

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
local instance : Fact (Nat.Prime 7):=⟨by decide⟩

theorem seven_rows {m : ℕ} {k l c inv w : ℤ} {f : ZMod 7 × H → ℤ} (hf : IsSDS k l f)
    (hm : Fintype.card H=m) (hc : Nat.Coprime 7 m) (h4 : Nat.Coprime 28 m)
    (hn : k-l=112) (hσ : mass f=7*c) (hu : 7*inv=1+(m:ℤ)*w) :
    ∃ L∈sevenPatterns, let A:=shifted c L
       (seven (rowMass f)).Perm A ∧ (∀i,energy (row f i)∈weights m k l c inv A (rowMass f i)) ∧ lowTotal m k l c inv A≤k := by
  let a:=rowMass f
  let b (i : ZMod 7):=energy (row f i)
  let x (i : ZMod 7):=a i-c
  have norm : k-l=(7:ℤ)*16 := hn
  obtain ⟨c',h',_,_,hcor⟩:=centered_row_corr hf norm
  have eq : c'=c := by change mass f=7*c' at h'; omega
  subst c'
  have smA : (∑i,a i)=7*c := (mass_rowmass f).trans hσ
  have sm : mass x=0 := by simp [mass,x,sum_sub_distrib,smA,ZMod.card]
  have sq : energy x=96 := by rw [energy_zero]; have he:=hcor 0; norm_num at he; exact he
  have signed (t : ZMod 7) (n : t≠0) : corr x t= -16 := by simpa [n] using hcor t
  obtain ⟨L,hL,perm⟩:=seven_classified x sm sq (signed 1 (by decide)) (signed 2 (by decide)) (signed 3 (by decide))
  let A:=shifted c L
  have actual : (seven a).Perm A := by
    have h:=perm.map (fun d=>c+d)
    rw [seven_map] at h
    simpa [A,shifted,x] using h
  have ok (i:ZMod 7) : b i∈weights m k l c inv A (a i) := by
    have raw:=row_admissible hf norm hσ (hm ▸ hc) i
    have sh:=row_shift_admissible hf norm (by decide) (hm ▸ hc) i
    have fu:=full_row_admissible hf norm (by decide) (hm ▸ hc) (hm ▸ h4) (by decide : IsCoprime (4:ℤ) 7) i
    have budget:=row_budget hf norm hσ (hm ▸ hc) i
    have cap:=mixed_anchor_bound hf norm (by decide) (hm ▸ hc) (hm ▸ hu) i
    rw [hm] at raw sh fu budget
    rw [variance,hm] at cap
    change admissibleRow 7 m 16 l c (a i) (b i) at raw
    have bounds : 0≤b i ∧ b i ≤ m := ⟨raw.2.2.1,raw.2.2.2.1⟩
    have e : ((b i).toNat:ℤ)=b i := Int.toNat_of_nonneg bounds.1
    have idx : (b i).toNat < m+1 := by omega
    have pm := (actual.map (residueCost inv m (a i))).sum_eq
    rw [seven_map,seven_sum] at pm
    change 7*(∑j, residueCost inv m (a i) (a j))≤16*((m:ℤ)*b i-(a i)^2) at cap
    rw [pm] at cap
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨(b i).toNat,List.mem_range.mpr idx,e⟩,decide_eq_true ⟨budget,raw,sh,fu,cap⟩⟩
  refine ⟨L,hL,actual,ok,?_⟩
  let minimum (a:ℤ):=lowerWeight k (weights m k l c inv A a)
  have lo := sum_le_sum (s:=univ) (fun i _=>lowerWeight_le (k:=k) (ok i))
  have sumB : (∑i,b i)=k := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  rw [sumB] at lo
  have cmp:=(actual.map minimum).sum_eq
  rw [seven_map,seven_sum] at cmp
  change (A.map minimum).sum≤k
  rw [←cmp]
  exact lo

end Signed39.Profiles
