import SignedCapacityCertificate
import SignedSelfConjugacy

/-! The row contraction applied to two possibly different rows. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def cross (a b : H → ℤ) (t : H) : ℤ := ∑ x, a x*b (x+t)

theorem matched_cross (a b s : H → ℤ) (n l : ℤ)
    (hh : ∀ t, corr s t=(if t=0 then n else 0)+l) (t : H) :
    cross (matched a s) (matched b s) t=n*cross a b t+l*(mass a)*(mass b) := by
  have inner (x y : H) : (∑ z : H, s (x-z)*s (y-(z+t)))=corr s (y-(x+t)) := by
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro z
    change s (x-z)*s (y-(z+t))=s (x-z)*s ((x-z)+(y-(x+t)))
    rw [show (x-z)+(y-(x+t))=y-(z+t) by abel]
  calc
    _=∑ z, ∑ x, ∑ y, a x*b y*(s (x-z)*s (y-(z+t))) := by
      simp only [cross,matched,sum_mul,mul_sum]
      apply sum_congr rfl; intro z _
      rw [sum_comm]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intros
      ring
    _=∑ x, ∑ y, ∑ z, a x*b y*(s (x-z)*s (y-(z+t))) := by
      rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]
    _=∑ x, ∑ y, ((if y=x+t then n*(a x*b (x+t)) else 0)+l*(a x*b y)) := by
      simp only [← mul_sum,inner,hh]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      by_cases h : y=x+t <;> simp [h,sub_eq_zero] <;> ring
    _=_ := by simp [sum_add_distrib,← mul_sum,← sum_mul,cross,mass,mul_assoc]

variable {p : ℕ} [Fact p.Prime]

theorem row_cross_dvd {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hp : p.Coprime (Fintype.card H)) (i j : ZMod p) (t : H) :
    (p:ℤ) ∣ s*cross (row f i) (row f j) t+lam*rowMass f i*rowMass f j := by
  choose a ha using matched_dvd hf ⟨s,hn⟩ hp i
  choose b hb using matched_dvd hf ⟨s,hn⟩ hp j
  have ai : matched (row f i) (fiber f)=fun z => (p:ℤ)*a z := funext ha
  have bj : matched (row f j) (fiber f)=fun z => (p:ℤ)*b z := funext hb
  have h := matched_cross (row f i) (row f j) (fiber f) (k-lam) ((Fintype.card (ZMod p):ℤ)*lam) (fiber_flat hf) t
  rw [ai,bj,ZMod.card,hn] at h
  have scale : cross (fun x => (p:ℤ)*a x) (fun x => (p:ℤ)*b x) t=(p:ℤ)^2*cross a b t := by
    simp only [cross,mul_sum]; apply sum_congr rfl; intros; ring
  rw [scale] at h
  refine ⟨cross a b t,?_⟩
  apply mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p:ℤ)≠0)
  dsimp only [rowMass]
  linear_combination -h

#print axioms row_cross_dvd

end Signed39.Contraction

