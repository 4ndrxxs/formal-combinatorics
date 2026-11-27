import PaleySourceBorders
import Quantum.Hadamard.LinPhoaCharacterProduct

/-! Determinants of the explicit bordered arrays in Lin and Phoa's equation (3.1)
with circulants obtained by signed incidence of the four sets of MSX Theorem 4.1. -/

noncomputable section
open Matrix Finset Hadamard.NearBorder Hadamard.MSXCore
namespace Hadamard.LinPhoa

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-- The magnitude depends only on the first support column's coset index. -/
theorem source_array_det (hc : ringChar F≠2) (q4 : Fintype.card F%4=1) (hm : 2 ≤ m)
    (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (i j c : Bool) (valid : i=true ∨ c=true) :
    |(array c (sourcePair w i j e)).det|=|(reference (F:=F) i).det| := by
  have p := source_partition hc q4 w hw i j c valid e cyc
  have part : Partition (bordered ((layout m).core (sourcePair w i j e)) strip strip (corner c)*
      (bordered ((layout m).core (sourcePair w i j e)) strip strip (corner c)).transpose) := by
    rw [layout_core]
    exact p
  simpa only [layout_core,array] using compare_source_layout hc q4 hm w hw e cyc i j (layout m)
    strip strip (corner c) strip_sign strip_sign (corner_sign c) part

theorem source_array_four_fifths (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (i j c : Bool) (valid : i=true ∨ c=true) :
    (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
      |(array c (sourcePair w i j e)).det| := by
  have hc : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  have size : m=(Fintype.card F-1)/2 := by
    simpa only [Fintype.card_fin,square_index_card w hw] using Fintype.card_congr e
  rw [source_array_det hc q4 (by omega) w hw e cyc i j c valid]
  have h := split_resolves (F:=F) i
  have lower := ProjectiveSigning.quadratic_paley_four_fifths_all q4 lo (0:F) 1 0 (by simp)
    (splitSign i) (-cosetSign i) (by cases i <;> norm_num [cosetSign]) h.1 h.2
  simpa only [reference,signInt,Int.cast_ite,Int.cast_neg,Int.cast_one] using lower

/-- The field alone supplies the nonsquare and a cyclic order, for all six
admissible choices of the two sets and the corner sign simultaneously. -/
theorem every_field_source_array (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F) :
    ∃ w : F, quadraticChar F w= -1 ∧ ∃ n : ℕ, n+1=(Fintype.card F-1)/2 ∧
      ∃ e : Fin (n+1) ≃ SquareIndex F, (∀ k l, (e (k-l)).val=(e k).val/(e l).val) ∧
        ∀ i j c : Bool, (i=true ∨ c=true) →
          (∀ a b, array c (sourcePair w i j e) a b=1 ∨ array c (sourcePair w i j e) a b= -1) ∧
          (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
            |(array c (sourcePair w i j e)).det| := by
  have hc : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨w,hw⟩ := quadraticChar_exists_neg_one (F:=F) hc
  let n := (Fintype.card F-1)/2-1
  have nn : n+1=(Fintype.card F-1)/2 := by dsimp [n]; omega
  obtain ⟨e,cyc⟩ := exists_square_enumeration ((square_index_card w hw).trans nn.symm)
  refine ⟨w,hw,n,nn,e,cyc,?_⟩
  intro i j c valid
  exact ⟨source_entry_sign w i j c e,source_array_four_fifths q4 lo w hw e cyc i j c valid⟩

/-- Direct four-fifths bounds for the two Jacobi products, with explicit
prefactors (q-1)^2 and (q+1)^2+4. No matrix occurs in the conclusion. -/
theorem two_jacobi_bounds (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (e : Fin m ≃ SquareIndex F) (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (ψ : AddChar (Fin m) ℂ → MulChar F ℂ) (extendsOn : ∀ θ k, ψ θ (e k).val=θ k) (i : Bool) :
    (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
      (if i then ((Fintype.card F:ℝ)-1)^2 else ((Fintype.card F:ℝ)+1)^2+4)*
      ‖∏ θ ∈ (univ : Finset (AddChar (Fin m) ℂ)).erase 0,
        ((Fintype.card F:ℂ)+1-(cosetSign i:ℂ)*
          (jacobiSum (ψ θ) (eta F)+jacobiSum (ψ θ*eta F) (eta F)))‖ := by
  have hc : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨w,hw⟩ := quadraticChar_exists_neg_one (F:=F) hc
  have cardq : Fintype.card F=2*m+1 := by
    have h := Fintype.card_congr e
    rw [Fintype.card_fin,square_index_card w hw] at h
    omega
  have pref : 2*((orientation true*(if i then 0 else -2)-(m:ℝ))^2+(m:ℝ)^2)=
      (if i then ((Fintype.card F:ℝ)-1)^2 else ((Fintype.card F:ℝ)+1)^2+4) := by
    rw [cardq]; cases i <;> norm_num [orientation] <;> ring
  have eq := congrArg (norm (E:=ℂ)) (array_jacobi_product hc q4 w hw i false true e cyc ψ extendsOn)
  have pos : 0≤(if i then ((Fintype.card F:ℝ)-1)^2 else ((Fintype.card F:ℝ)+1)^2+4) := by
    split <;> positivity
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs,pref,abs_of_nonneg pos] at eq
  rw [←eq]
  exact source_array_four_fifths q4 lo w hw e cyc i false true (Or.inr rfl)

#print axioms two_jacobi_bounds
#print axioms source_array_det
#print axioms source_array_four_fifths
#print axioms every_field_source_array

end Hadamard.LinPhoa
