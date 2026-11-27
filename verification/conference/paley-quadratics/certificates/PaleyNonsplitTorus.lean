import PaleyAllOrders
import Quantum.Hadamard.ProjectiveNonsplitTorus

/-! Determinant bounds for two explicit circulants from the odd norm-one
subgroup of a quadratic finite field extension. -/

noncomputable section
open Matrix Finset
open Hadamard.ProjectiveSigning Hadamard.ProjectiveSigning.Coordinates
namespace Hadamard.NonsplitTorus

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : F} [Fact (¬ IsSquare d)]

theorem torus_four_fifths (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (h : (Ext d)ˣ) [NeZero (orderOf h)] (ho : orderOf h=(Fintype.card F+1)/2)
    (hn : (h:Ext d).norm=1) (α : ℤ) (unit : α^2=1) :
    (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
      |(twoCirculant h α).det| := by
  have hc : ringChar F≠2 := by
    intro eq
    have even := FiniteField.even_card_of_char_two eq
    omega
  have two : (2:F)≠0 := fun eq ↦ hc (CharP.ringChar_of_prime_eq_zero Nat.prime_two eq)
  have hm : quadraticChar F (-1)=1 := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have dn : d≠0 := by intro eq; exact (Fact.out : ¬IsSquare d) (eq ▸ IsSquare.zero)
  have disc : (0:F)^2-4*1*(-d)≠0 := by
    rw [show (0:F)^2-4*1*(-d)=2*2*d by ring]
    exact mul_ne_zero (mul_ne_zero two two) dn
  have val (p : Option F) : quadraticValue 1 0 (-d) p=normAt d p := by
    cases p <;> simp [normAt,x,y,quadraticValue,sub_eq_add_neg]
  have nz (p : Option F) : normAt d p≠0 := by
    cases p with
    | none => simp [normAt,x,y]
    | some t =>
      simpa [normAt,x,y,sub_ne_zero] using (show t^2≠d by
        intro eq; exact (Fact.out : ¬IsSquare d) ⟨t,by rw [←eq,pow_two]⟩)
  let sign (p : Option F) := decide (α*quadraticChar F (normAt d p)=1)
  have signs (p) : (if sign p then (1:ℤ) else -1)=α*quadraticChar F (normAt d p) := by
    have z : (α*quadraticChar F (normAt d p))^2=1 := by rw [mul_pow,unit,quadraticChar_sq_one (nz p),one_mul]
    unfold sign
    rcases sq_eq_one_iff.mp z with e|e <;> rw [e] <;> decide
  have lower := quadratic_paley_four_fifths_all q4 lo (1:F) 0 (-d) disc sign α unit
    (fun p _ ↦ by rw [val]; exact signs p) (by simp [val,nz])
  have castSign (p) : (if sign p then (1:ℝ) else -1)=((α*quadraticChar F (normAt d p):ℤ):ℝ) := by
    exact_mod_cast signs p
  rw [two_circulant_det q4 hm _ ho hn,signedDet]
  simpa only [castSign] using lower

/-- Such a generator exists in every eligible field, and both choices of
the diagonal sign satisfy the bound. -/
theorem exists_torus_four_fifths (d : F) [Fact (¬IsSquare d)]
    (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F) :
    ∃ h : (Ext d)ˣ, ∃ pos : orderOf h≠0, orderOf h=(Fintype.card F+1)/2 ∧ (h:Ext d).norm=1 ∧
      ∀ α : ℤ, α^2=1 → letI : NeZero (orderOf h) := ⟨pos⟩
        (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
          |(twoCirculant h α).det| := by
  obtain ⟨h,ho,hn⟩ := norm_one_generator d q4 (by omega)
  have nz : orderOf h≠0 := by omega
  refine ⟨h,nz,ho,hn,?_⟩
  let _ : NeZero (orderOf h) := ⟨nz⟩
  exact torus_four_fifths q4 lo h ho hn

#print axioms torus_four_fifths
#print axioms exists_torus_four_fifths


/-- Starting with the field and its order alone, construct a nonsquare, a
generator, and a circulant sign matrix attaining the bound for either sign. -/
theorem every_field_torus (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F) :
    ∃ d : F, ∃ ns : ¬IsSquare d, letI : Fact (¬IsSquare d) := ⟨ns⟩
      ∃ h : (Ext d)ˣ, ∃ pos : orderOf h≠0, orderOf h=(Fintype.card F+1)/2 ∧ (h:Ext d).norm=1 ∧
        ∀ α : ℤ, α^2=1 → letI : NeZero (orderOf h) := ⟨pos⟩
          (∀ i j, twoCirculant h α i j=1 ∨ twoCirculant h α i j= -1) ∧
          (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
            |(twoCirculant h α).det| := by
  have hc : ringChar F≠2 := by
    intro e; have hn := FiniteField.even_card_of_char_two e; omega
  have hm : quadraticChar F (-1)=1 := (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
    (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  obtain ⟨d,ns⟩ := FiniteField.exists_nonsquare hc
  refine ⟨d,ns,?_⟩
  let _ : Fact (¬IsSquare d) := ⟨ns⟩
  obtain ⟨h,ho,hn⟩ := norm_one_generator d q4 (by omega)
  have pos : orderOf h≠0 := by omega
  let _ : NeZero (orderOf h) := ⟨pos⟩
  exact ⟨h,pos,ho,hn,fun α unit ↦ ⟨sign_entries q4 hm h ho hn α unit,torus_four_fifths q4 lo h ho hn α unit⟩⟩

#print axioms every_field_torus

end Hadamard.NonsplitTorus
