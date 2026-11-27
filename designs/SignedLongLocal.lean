import SignedLongTransfer
import SignedBudgetCertificate

namespace Signed39.Contraction

open Finset

def orbitLocal (d:ℕ) (a b:ℤ) : Prop :=
  ((d:ℤ)∣(b+a)/2 ∧ (d:ℤ)∣(b-a)/2) ∨
  ((d:ℤ)∣(b+a)/2-1 ∧ (d:ℤ)∣(b-a)/2) ∨
  ((d:ℤ)∣(b+a)/2 ∧ (d:ℤ)∣(b-a)/2-1)
instance (d:ℕ) (a b:ℤ) : Decidable (orbitLocal d a b) := by unfold orbitLocal; infer_instance

variable {H:Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {p:ℕ} [Fact p.Prime]

theorem fixed_local_signs {k l:ℤ} {f:ZMod p×H→ℤ} (hf:IsSDS k l f)
    (B:H≃+H) (base:H) (fix:∀i x,f (i,B x+base)=f (i,x+base)) (d:ℕ) (W:H→ℤ)
    (levels:∀x,(d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W (B x)-W x) (i:ZMod p) :
    orbitLocal d (rowMass f i) (energy (row f i)) := by
  let mark (sg:ℤ) (x:H):=signBit (f (i,x+base)) sg
  have rule (sg:ℤ) (ss:sg=1∨sg= -1) : (d:ℤ)∣(energy (row f i)+sg*rowMass f i)/2-signBit (f (i,base)) sg := by
    have dv:=orbit_mass_dvd B.toEquiv (mark sg) W _ 0
      (fun x=>by change signBit (f (i,B x+base)) sg=signBit (f (i,x+base)) sg; rw [fix]) levels
    have eq0 : mark sg 0=signBit (f (i,base)) sg := by simp [mark]
    have shift : mass (mark sg)=∑x:H,signBit (f (i,x)) sg :=
      sum_translate (fun x:H=>signBit (f (i,x)) sg) base
    have pt (x:H) : 2*signBit (f (i,x)) sg=(f (i,x))^2+sg*f (i,x) := by
      rcases hf.ternary (i,x) with h|h|h <;> rcases ss with rfl|rfl <;> simp [h,signBit]
    have twice : 2*mass (mark sg)=energy (row f i)+sg*rowMass f i := by
      rw [shift,mul_sum]; simp only [pt,sum_add_distrib,←mul_sum,energy,rowMass,row,mass]
    simpa only [←twice,Int.mul_ediv_cancel_left _ (by decide:(2:ℤ)≠0),←eq0] using dv
  have pos:=rule 1 (Or.inl rfl)
  have neg:=rule (-1) (Or.inr rfl)
  simp only [one_mul,neg_one_mul,←sub_eq_add_neg] at pos neg
  rcases hf.ternary (i,base) with hz|hz|hz
  · right; right; simpa [hz,signBit] using And.intro pos neg
  · left; simpa [hz,signBit] using And.intro pos neg
  · right; left; simpa [hz,signBit] using And.intro pos neg

theorem long_local_exclusion (p m s t inv step r d:ℕ) [Fact p.Prime]
    (k l c:ℤ) (u v:AuxPower) (hm:Fintype.card H=m) (W:H→ℤ)
    (levels:∀x:H,(d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W (t • x)-W x)
    (head:longHeader p m s t inv step r d k l ((p:ℤ)*c) u v) (D J:ℕ) (a b:ℤ) (cut:Separator)
    (short:shortHeader p m D J 1 0 k l s c a b) (total:cut.value p ((p:ℤ)*c) k (k-l+(m:ℤ)*l)<0)
    (cover:shortCover p m D J 1 k l s c a
      (fun z=>orbitLocal d z.1 z.2 → 0≤cut.value 1 z.1 z.2 (z.1^2))) :
    ¬∃f:ZMod p×H→ℤ,IsSDS k l f := by
  apply capacity_family_false (h:=cut) (z:=fun _=>0) hm short.2.2.1 short.2.2.2.1 short.2.2.2.2.1 (by simp) (by simpa using total)
  intro f hf ms i
  obtain ⟨base,fix⟩:=long_fixed_word p m s t inv step r d k l ((p:ℤ)*c) u v hm head f hf
  let B:=scalarPerm (H:=H) t inv (hm ▸ head.2.2.2.2.2.2.2.2.2.1)
  have allowed:=fixed_local_signs hf B base fix d W levels i
  simpa only [rowType,add_zero] using (short_cover_sound hm short cover hf ms i) allowed

#print axioms fixed_local_signs
#print axioms long_local_exclusion

end Signed39.Contraction
