import SignedCenteredCertificate

/-! An occupied full-support row takes only the values ±1, adding a factor four to each displacement. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem full_displacement_four {u : H → ℤ} (ht : ∀ x, u x= -1 ∨ u x=0 ∨ u x=1)
    (hw : energy u=Fintype.card H) (t : H) : (4:ℤ)∣displacement u t := by
  let z := fun x => if u x= -1 then (1:ℤ) else 0
  have e : (∑ x, (1-(u x)^2))=0 := by
    rw [sum_sub_distrib]; change _-energy u=0; simp [hw]
  have non (x : H) : 0≤1-(u x)^2 := by rcases ht x with h|h|h <;> norm_num [h]
  have form (x : H) : u x=1-2*z x := by
    have eq := (sum_eq_zero_iff_of_nonneg (fun x _ => non x)).mp e x (mem_univ _)
    rcases ht x with h|h|h <;> simp_all [z]
  have sq (x : H) : (u x-u (x+t))^2=4*(z x-z (x+t))^2 := by rw [form x,form (x+t)]; ring
  have h := displacement_squares u t
  simp only [sq,← mul_sum,← displacement_squares] at h
  exact ⟨displacement z t,by omega⟩

def admissibleFull (p m a b : ℤ) : Prop := b=m → admissibleShift (4*p) m a b
instance (p m a b : ℤ) : Decidable (admissibleFull p m a b) := by unfold admissibleFull; infer_instance

variable {p : ℕ} [Fact p.Prime]

theorem full_row_admissible {k l s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬(p:ℤ)∣s) (hc : p.Coprime (Fintype.card H))
    (ho : (4*p).Coprime (Fintype.card H)) (hp4 : IsCoprime (4:ℤ) (p:ℤ)) (i : ZMod p) :
    admissibleFull p (Fintype.card H) (rowMass f i) (energy (row f i)) := by
  intro full
  let u := row f i
  have ht (x : H) : u x= -1 ∨ u x=0 ∨ u x=1 := hf.ternary (i,x)
  have d (t : H) : ((4*p:ℕ):ℤ)∣displacement u t := by
    exact_mod_cast hp4.mul_dvd (full_displacement_four ht full t) (row_displacement_dvd hf hn hs hc i t)
  by_cases h : ∃ x y : H, u x≠u y
  · obtain ⟨x,y,hxy⟩ := h
    have low := variation_lower u ho d hxy
    have high := variation_upper (show 0<4*p by have := (Fact.out : p.Prime).pos; omega) u ht d
    exact Or.inr ⟨by simpa only [Nat.cast_mul,Nat.cast_ofNat,variance,u,rowMass] using low,
      by simpa only [Nat.cast_mul,Nat.cast_ofNat,variance,u,rowMass] using high⟩
  · push Not at h
    exact Or.inl (variance_constant u (u 0) (fun x => h x 0))

#print axioms full_row_admissible

end Signed39.Contraction
