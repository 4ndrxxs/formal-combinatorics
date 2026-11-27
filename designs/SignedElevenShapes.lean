import Signed473
import SignedBudgetCertificate

namespace Signed39.Template

open Finset Contraction

def shapes : List (List ℤ) := [
  [-11,-3,-3,-1,-1,1,1,2,3,5,7],[-10,-6,-2,-1,-1,1,2,3,3,4,7],[-10,-5,-4,-2,0,1,3,3,4,5,5],
  [-7,-5,-3,-2,-1,-1,1,1,3,3,11],[-7,-4,-3,-3,-2,-1,1,1,2,6,10],[-5,-5,-5,-5,-5,4,4,4,4,4,5],
  [-5,-5,-4,-3,-3,-1,0,2,4,5,10],[-5,-4,-4,-4,-4,-4,5,5,5,5,5]]

def entries (u:P→ℤ) : List ℤ := List.ofFn (n:=11) u

private theorem entries_map (u:P→ℤ) (F:ℤ→ℤ) : (entries u).map F=entries (fun i=>F (u i)) :=
  List.map_ofFn (n:=11) (f:=u) (g:=F)

private theorem entries_sum (u:P→ℤ) : (entries u).sum=∑i:P,u i := Fin.sum_ofFn u

private theorem shapesCover : ∀n:Fin 32,∀sg∈([1,-1]:List ℤ),∃L∈shapes,
    (entries (fun i=>sg*word (templates n).W i)).Perm L := by decide +kernel

theorem classify_eleven (u:P→ℤ) (mu:mass u=0) (eu:energy u=230)
    (flat:∀t,corr u t=(if t=0 then 253 else 0)-23) : ∃ L∈shapes,(entries u).Perm L := by
  obtain ⟨b,hb⟩:=choose_roots u flat
  obtain ⟨n,bn⟩:=all_masks b
  have be:b=bits n:=funext bn
  subst b
  let W:=(templates n).W
  have good : valid W (bits n):=(all_checked n).1
  have dm:=template_modulus u flat (bits n) hb W good
  obtain ⟨t,sg,hsg,form⟩:=template_match_11 u (word W) mu eu good.1 good.2.1 dm
  obtain ⟨L,mem,perm⟩:=shapesCover n sg (by simpa using hsg)
  let f:=fun i:P=>sg*word W i
  let e:P≃P:=Equiv.addRight (-t)
  have eq : u=f ∘ e := funext (fun i=>by simpa only [f,e,Function.comp_apply,Equiv.coe_addRight,sub_eq_add_neg] using form i)
  rw [eq]
  exact ⟨L,mem,(Equiv.Perm.ofFn_comp_perm (n:=11) e f).trans perm⟩

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

def options (m:ℕ) (k l c inv:ℤ) (L:List ℤ) (a:ℤ) : List ℤ :=
  ((List.range (m+1)).map (fun x:ℕ=>(x:ℤ))).filter (fun b=>decide (
    rowBudget 11 m k c a b ∧ admissibleRow 11 m 23 l c a b ∧
    11*(L.map (residueCost inv m a)).sum≤23*((m:ℤ)*b-a^2)))

def excludes (m:ℕ) (k l c inv:ℤ) : Prop := ∀L∈shapes,
  let A:=L.map (fun d=>c+d)
  k<(A.map (fun a=>lower k (options m k l c inv A a))).sum

instance (m:ℕ) (k l c inv:ℤ) : Decidable (excludes m k l c inv) := by unfold excludes; infer_instance

theorem eleven_shape_exclusion (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m:ℕ) (k l c inv w:ℤ) (hg:Fintype.card G=11*m) (cop:Nat.Coprime 11 m) (hn:k-l=253)
    (sq:(11*c)^2=k-l+(11:ℤ)*m*l) (hi:11*inv=1+(m:ℤ)*w) (bad:excludes m k l c inv) :
    ¬∃f:G→ℤ, IsSDS k l f := by
  classical
  let : Fact (Nat.Prime 11):=⟨by decide⟩
  rintro ⟨F,hF⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg cop
  let H:=Additive K
  have hm : Fintype.card H=m := Nat.card_eq_fintype_card.symm.trans hK
  let F':P×H→ℤ:=fun x=>F (E x)
  have h0:IsSDS k l F':=pullback hF E
  have hmass:=sds_mass h0
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,Nat.cast_ofNat,←sq] at hmass
  obtain ⟨f,hf,ms⟩ : ∃f:P×H→ℤ, IsSDS k l f ∧ mass f=11*c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmass with hp|hn
    · exact ⟨F',h0,hp⟩
    · exact ⟨fun x=> -F' x,h0.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn⟩
  let a:=rowMass f
  let b (i:P):=energy (row f i)
  let u (i:P):=a i-c
  have norm : k-l=(11:ℤ)*23 := hn
  obtain ⟨c',mc,_,mu,cor⟩:=centered_row_corr hf norm
  rw [ms] at mc
  have cc:c'=c:=by omega
  subst c'
  have flat (t:P) : corr u t=(if t=0 then 253 else 0)-23 := cor t
  have eu : energy u=230 := by rw [energy_zero,flat]; decide
  obtain ⟨L,mem,perm⟩:=classify_eleven u mu eu flat
  let U:=L.map (fun z=>c+z)
  have act : (entries a).Perm U := by
    have h:=perm.map (fun z=>c+z)
    rw [entries_map] at h
    simpa [u,U] using h
  have suma (F:ℤ→ℤ) : (∑i:P,F (a i))=(U.map F).sum := by
    have h:=(act.map F).sum_eq
    rwa [entries_map,entries_sum] at h
  have hc : Nat.Coprime 11 (Fintype.card H):=hm ▸ cop
  have allowed (i:P) : b i∈options m k l c inv U (a i) := by
    have raw:=row_admissible (s:=23) (c:=c) hf norm ms hc i
    have budget:=row_budget hf norm ms hc i
    have mixed:=mixed_anchor_bound (inv:=inv) (w:=w) hf norm (by decide) hc (hm ▸ hi) i
    change admissibleRow 11 (Fintype.card H) 23 l c (a i) (b i) at raw
    change rowBudget 11 (Fintype.card H) k c (a i) (b i) at budget
    change (11:ℤ)*(∑j:P,residueCost inv (Fintype.card H) (a i) (a j))≤23*((Fintype.card H:ℤ)*b i-(a i)^2) at mixed
    rw [hm] at raw budget mixed
    rw [suma] at mixed
    have lo:0≤b i:=raw.2.2.1
    have up : b i ≤ m :=raw.2.2.2.1
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(b i).toNat,List.mem_range.mpr (by omega),Int.toNat_of_nonneg lo⟩,
      decide_eq_true ⟨budget,raw,mixed⟩⟩
  have low:=sum_le_sum (s:=univ) (fun i _=>lower_le (k:=k) (allowed i))
  have total : (∑i,b i)=k := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  rw [total,suma (fun z=>lower k (options m k l c inv U z))] at low
  exact (not_lt_of_ge low) (bad L mem)

#print axioms classify_eleven
#print axioms eleven_shape_exclusion

end Signed39.Template
