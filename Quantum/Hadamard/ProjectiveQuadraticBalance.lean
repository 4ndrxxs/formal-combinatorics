import Quantum.Hadamard.Paley

/-! Quadratic signings on the projective line over a finite field of odd
characteristic. A nonsingular binary quadratic form has total quadratic
character zero on the projective line. Opposite signs on its two roots
therefore give a balanced signing in the split case. -/

noncomputable section
open Finset

namespace Hadamard.ProjectiveSigning

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The affine character sum for a translated square. -/
theorem square_shift_sum (hc : ringChar F ≠ 2) (d : F) (hd : d ≠ 0) :
    (∑ x : F, quadraticChar F (x^2-d)) = -1 := by
  classical
  let χ := quadraticChar F
  have fibers (t : F) : (∑ x : F, if x^2=t then (1:ℤ) else 0) = χ t+1 := by
    rw [Finset.sum_boole]
    have eq : (univ.filter fun x : F ↦ x^2=t) = {x : F | x^2=t}.toFinset := by ext; simp
    rw [eq]
    exact quadraticChar_card_sqrts hc t
  have shift : (∑ t : F, χ (t-d))=0 :=
    ((Equiv.subRight d).sum_comp χ).trans (quadraticChar_sum_zero hc)
  have corr : (∑ t : F, χ t * χ (t-d))= -1 := by
    simpa [χ, sub_eq_add_neg, hd] using Hadamard.Paley.character_corr hc (-d)
  calc
    _ = ∑ x : F, ∑ t : F, if x^2=t then χ (t-d) else 0 := by simp [χ]
    _ = ∑ t : F, (∑ x : F, if x^2=t then (1:ℤ) else 0)*χ (t-d) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      by_cases h : x^2=t <;> simp [h]
    _ = -1 := by simp [fibers, add_mul, sum_add_distrib, shift, corr]

/-- Values at the standard representatives (x,1) and (1,0). -/
def quadraticValue (a b c : F) : Option F → F
  | none => a
  | some x => a*x^2+b*x+c

theorem projective_character_sum (hc : ringChar F ≠ 2) (a b c : F) (disc : b^2-4*a*c ≠ 0) :
    (∑ s : Option F, quadraticChar F (quadraticValue a b c s)) = 0 := by
  classical
  let χ := quadraticChar F
  rw [Fintype.sum_option]
  change χ a + ∑ x : F, χ (a*x^2+b*x+c) = 0
  by_cases ha : a=0
  · subst a
    have hb : b ≠ 0 := by simpa using disc
    let e := (Equiv.mulLeft₀ b hb).trans (Equiv.addRight c)
    have h := e.sum_comp χ
    change (∑ x : F, χ (b*x+c)) = _ at h
    simpa [χ, h, quadraticChar_sum_zero hc] using h.trans (quadraticChar_sum_zero hc)
  · have two : (2:F) ≠ 0 := fun h ↦ hc (CharP.ringChar_of_prime_eq_zero Nat.prime_two h)
    let d := b^2-4*a*c
    let e := (Equiv.mulLeft₀ (2*a) (mul_ne_zero two ha)).trans (Equiv.addRight b)
    have translated := e.sum_comp (fun y ↦ χ (y^2-d))
    change (∑ x : F, χ ((2*a*x+b)^2-d)) = _ at translated
    have eval : (∑ x : F, χ ((2*a*x+b)^2-d))= -1 :=
      translated.trans (square_shift_sum hc d disc)
    have factor (x : F) : χ (a*x^2+b*x+c) = χ a * χ ((2*a*x+b)^2-d) := by
      have id : (2:F)^2*a*(a*x^2+b*x+c)=(2*a*x+b)^2-d := by dsimp [d]; ring
      have h := congrArg χ id
      rw [map_mul, map_mul, map_pow, show χ 2 ^ 2 = 1 from quadraticChar_sq_one two, one_mul] at h
      rw [←h, ←mul_assoc, ←pow_two, show χ a ^ 2 = 1 from quadraticChar_sq_one ha, one_mul]
    simp only [factor, ←mul_sum, eval]
    ring

/-- A balanced resolution of the zeros produces equally many positive and
negative signs for either orientation of the quadratic character. -/
theorem balanced_resolved_quadratic (hc : ringChar F ≠ 2) (a b c : F)
    (disc : b^2-4*a*c ≠ 0) (s : Option F → Bool) (orientation : ℤ)
    (agree : ∀ i, quadraticValue a b c i ≠ 0 →
      (if s i then (1:ℤ) else -1) = orientation * quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i : Option F, if quadraticValue a b c i=0
      then (if s i then (1:ℤ) else -1) else 0) = 0) :
    2*(univ.filter (fun i ↦ s i = true)).card = Fintype.card F+1 := by
  classical
  let w (i : Option F) : ℤ := if s i then 1 else -1
  have identity (i : Option F) : w i = orientation * quadraticChar F (quadraticValue a b c i) +
      if quadraticValue a b c i=0 then w i else 0 := by
    by_cases hi : quadraticValue a b c i=0
    · simp [hi]
    · simpa [hi, w] using agree i hi
  have total : (∑ i, w i)=0 := by
    calc
      _ = ∑ i, (orientation * quadraticChar F (quadraticValue a b c i) +
          if quadraticValue a b c i=0 then w i else 0) := sum_congr rfl (fun i _ ↦ identity i)
      _ = 0 := by
        rw [sum_add_distrib, ←mul_sum, projective_character_sum hc a b c disc, mul_zero, zero_add]
        exact ties
  have point (i : Option F) : w i = 2*(if s i then (1:ℤ) else 0)-1 := by
    dsimp [w]
    cases h : s i <;> norm_num
  simp only [point, sum_sub_distrib, ←mul_sum, sum_boole, sum_const, card_univ, nsmul_eq_mul,
    mul_one, Fintype.card_option] at total
  omega

#print axioms square_shift_sum
#print axioms projective_character_sum
#print axioms balanced_resolved_quadratic

end Hadamard.ProjectiveSigning
