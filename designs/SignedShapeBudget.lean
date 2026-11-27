import SignedMultiplierShapes
import SignedBudgetCertificate

namespace Signed39.Shape

open Finset Contraction

def lower (k:ℤ) : List ℤ→ℤ
  | []=>k+1
  | x::xs=>min x (lower k xs)

private theorem lower_le {k a:ℤ} {L:List ℤ} (ha:a∈L) : lower k L≤a := by
  induction L with
  | nil=>simp at ha
  | cons x xs ih=>
    rcases List.mem_cons.mp ha with rfl|h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

def options (p m : ℕ) (s k l c inv:ℤ) (L:List ℤ) (a:ℤ) : List ℤ :=
  ((List.range (m+1)).map (fun x:ℕ=>(x:ℤ))).filter (fun b=>decide (
    rowBudget p m k c a b ∧ admissibleRow p m s l c a b ∧
    (p:ℤ)*(L.map (residueCost inv m a)).sum ≤ s*((m:ℤ)*b-a^2)))

def excludes (p m : ℕ) (s k l c inv:ℤ) (shapes : List (List ℤ)) : Prop := ∀L∈shapes,
  let A:=L.map (fun d=>c+d)
  k<(A.map (fun a=>lower k (options p m s k l c inv A a))).sum

instance (p m : ℕ) (s k l c inv:ℤ) (shapes : List (List ℤ)) :
    Decidable (excludes p m s k l c inv shapes) := by unfold excludes; infer_instance

theorem exclusion (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (p m:ℕ) [Fact p.Prime]
    (s k l c inv w:ℤ) (shapes : List (List ℤ)) (hg:Fintype.card G=p*m) (cop:Nat.Coprime p m)
    (hn:k-l=(p:ℤ)*s) (hs:¬(p:ℤ)∣s) (sq:((p:ℤ)*c)^2=k-l+(p:ℤ)*m*l) (hi:(p:ℤ)*inv=1+(m:ℤ)*w)
    (cover:∀u:ZMod p→ℤ,mass u=0 → (∀t,corr u t=(if t=0 then (p:ℤ)*s else 0)-s) →
      ∃L∈shapes,∀F:ℤ→ℤ,(∑i,F (u i))=(L.map F).sum)
    (bad:excludes p m s k l c inv shapes) : ¬∃f:G→ℤ, IsSDS k l f := by
  classical
  have pp :(0:ℤ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  rintro ⟨F,hF⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg cop
  let H:=Additive K
  have hm : Fintype.card H=m := Nat.card_eq_fintype_card.symm.trans hK
  let F':ZMod p×H→ℤ:=fun x=>F (E x)
  have h0:IsSDS k l F':=pullback hF E
  have hmass:=sds_mass h0
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,←sq] at hmass
  obtain ⟨f,hf,ms⟩ : ∃f:ZMod p×H→ℤ, IsSDS k l f ∧ mass f=(p:ℤ)*c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmass with hp|hn
    · exact ⟨F',h0,hp⟩
    · exact ⟨fun x=> -F' x,h0.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn⟩
  let a:=rowMass f
  let b (i:ZMod p):=energy (row f i)
  let u (i:ZMod p):=a i-c
  obtain ⟨c',mc,_,mu,cor⟩:=centered_row_corr hf hn
  rw [ms] at mc
  have cc:c'=c:=(mul_left_cancel₀ pp.ne' mc).symm
  subst c'
  obtain ⟨L,mem,profile⟩:=cover u mu cor
  let U:=L.map (fun z=>c+z)
  have suma (F:ℤ→ℤ) : (∑i:ZMod p,F (a i))=(U.map F).sum := by
    have eq:=profile (fun z=>F (c+z))
    simpa only [U,u,add_sub_cancel,List.map_map,Function.comp_def] using eq
  have hc : Nat.Coprime p (Fintype.card H):=hm ▸ cop
  have allowed (i:ZMod p) : b i∈options p m s k l c inv U (a i) := by
    have raw:=row_admissible (c:=c) hf hn ms hc i
    have budget:=row_budget hf hn ms hc i
    have mixed:=mixed_anchor_bound (inv:=inv) (w:=w) hf hn hs hc (hm ▸ hi) i
    change admissibleRow p (Fintype.card H) s l c (a i) (b i) at raw
    change rowBudget p (Fintype.card H) k c (a i) (b i) at budget
    change (p:ℤ)*(∑j:ZMod p,residueCost inv (Fintype.card H) (a i) (a j)) ≤ s*((Fintype.card H:ℤ)*b i-(a i)^2) at mixed
    rw [hm] at raw budget mixed
    rw [suma] at mixed
    have lo:0≤b i:=raw.2.2.1
    have up : b i ≤ m :=raw.2.2.2.1
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(b i).toNat,List.mem_range.mpr (by omega),Int.toNat_of_nonneg lo⟩,
      decide_eq_true ⟨budget,raw,mixed⟩⟩
  have low:=sum_le_sum (s:=univ) (fun i _=>lower_le (k:=k) (allowed i))
  have total : (∑i,b i)=k := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  rw [total,suma (fun z=>lower k (options p m s k l c inv U z))] at low
  exact (not_lt_of_ge low) (bad L mem)

#print axioms exclusion

end Signed39.Shape

