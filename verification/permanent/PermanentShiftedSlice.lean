import PermanentSlice
import ProductDegreeDrop
import DegreeDropIntegral

/-! Each translate of the five-parameter slice meets the singular scheme in
a finite scheme. The relations for pure sixth powers persist with error of
total degree at most five. -/
noncomputable section
open Finset MvPolynomial
namespace PermanentFive
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

private def sliceVars (K : Type*) [Field K] : Cell → MvPolynomial Idx K :=
  slice fun i ↦ X i

omit [CharZero K] in
private theorem sliceVars_degree (e : Cell) : (sliceVars K e).totalDegree ≤ 1 := by
  unfold sliceVars slice
  split <;> simp

omit [CharZero K] in
/-- The unshifted partial differs from a translated one by a cubic. -/
private theorem gradient_translation (z : Cell → K) (e : Cell) :
    ∃ q : MvPolynomial Idx K, q.totalDegree ≤ 3 ∧
      gradAt (sliceVars K) e = gradAt (fun j ↦ sliceVars K j + C (z j)) e + q := by
  let T := (Finset.univ : Finset Idx).erase e.2
  have size : T.card = 4 := by simp [T]
  let V (j : Cell) := sliceVars K j + C (z j)
  have bound (j : Cell) : (V j).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (sliceVars_degree j) (by simp))
  have step (p : Equiv.Perm Idx) : ∃ q : MvPolynomial Idx K, q.totalDegree ≤ 3 ∧
      (if p e.2 = e.1 then ∏ j ∈ T, sliceVars K (p j,j) else 0) =
      (if p e.2 = e.1 then ∏ j ∈ T, V (p j,j) else 0)+q := by
    by_cases ok : p e.2 = e.1
    · obtain ⟨q,d,eq⟩ := DegreeDrop.product_add_constants T (fun j ↦ V (p j,j))
        (fun j ↦ -z (p j,j)) (fun j ↦ bound (p j,j))
      refine ⟨q,by simpa [size] using d,?_⟩
      simpa [V,add_assoc,ok] using eq
    · exact ⟨0,by simp,by simp [ok]⟩
  choose q deg eq using step
  refine ⟨∑ p, q p,totalDegree_finsetSum_le (fun p _ ↦ deg p),?_⟩
  unfold gradAt
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ ↦ eq p)

private theorem combination_map {B T : Type*} [CommRing B] [CommRing T] (f : B →+* T)
    (x : Idx → B) (g : Cell → B) :
    f (sliceCombine x g) = sliceCombine (f ∘ x) (f ∘ g) := by
  simp [sliceCombine,map_list_sum,List.map_map,Function.comp_def]

omit [CharZero K] in
private theorem combo_degree (t : Idx) (q : Cell → MvPolynomial Idx K)
    (bound : ∀ e, (q e).totalDegree ≤ 3) :
    (sliceCombine (fun j ↦ X (j+t)) q).totalDegree ≤ 5 := by
  let val (a : SliceCoeffTerm) : MvPolynomial Idx K :=
    (a.coeff : MvPolynomial Idx K)*X (a.first+t)*X (a.second+t)*q a.entry
  have term (a : SliceCoeffTerm) : (val a).totalDegree ≤ 5 := by
    have eq : (C (a.coeff : K) : MvPolynomial Idx K) = a.coeff := map_intCast C _
    have coef : (a.coeff : MvPolynomial Idx K).totalDegree = 0 := by rw [← eq,totalDegree_C]
    have one := totalDegree_mul (a.coeff : MvPolynomial Idx K) (X (a.first+t))
    have two := totalDegree_mul ((a.coeff : MvPolynomial Idx K)*X (a.first+t)) (X (a.second+t))
    have h := totalDegree_mul ((a.coeff : MvPolynomial Idx K)*X (a.first+t)*X (a.second+t)) (q a.entry)
    change _ ≤ 5
    dsimp only [val]
    simp only [coef,totalDegree_X] at one two
    have d := bound a.entry
    omega
  have list (l : List SliceCoeffTerm) : (l.map val).sum.totalDegree ≤ 5 := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (totalDegree_add _ _).trans (max_le (term a) ih)
  exact list sliceCoeffTerms

/-- Every coordinate of a singular point on a translated slice is integral
over the ground field, uniformly over all target algebras. -/
theorem translated_slice_integral (z : Cell → K) (x : Idx → A)
    (zero : ∀ e, gradAt (fun j ↦ slice x j + algebraMap K A (z j)) e = 0) (i : Idx) :
    IsIntegral K (x i) := by
  let f := eval₂Hom (algebraMap K A) x
  have at_vars : f ∘ sliceVars K = slice x := by
    funext e
    by_cases h : e.2 ≠ 2*e.1 <;> simp [f,sliceVars,slice,h]
  have at_shift : f ∘ (fun j ↦ sliceVars K j + C (z j)) =
      (fun j ↦ slice x j + algebraMap K A (z j)) := by
    funext j
    change f (sliceVars K j + C (z j)) = _
    rw [map_add,show f (sliceVars K j) = slice x j from congrFun at_vars j]
    simp [f]
  choose q bound eq using gradient_translation z
  have at_q (e : Cell) : f (q e) = gradAt (slice x) e := by
    have h := congrArg f (eq e)
    rw [map_add,← grad_map,← grad_map,at_vars,at_shift,zero,zero_add] at h
    exact h.symm
  apply DegreeDrop.integral_of_power_degree_drop x 6 _ i
  intro t
  let B := sliceCombine (fun j ↦ X (j+t) : Idx → MvPolynomial Idx K)
    (fun e ↦ q (e.1+t,e.2+2*t))
  refine ⟨C ((8 : K)⁻¹)*B,?_,?_⟩
  · have b := combo_degree t (fun e ↦ q (e.1+t,e.2+2*t)) (fun e ↦ bound _)
    have h := totalDegree_mul (C ((8 : K)⁻¹) : MvPolynomial Idx K) B
    rw [totalDegree_C,zero_add] at h
    change B.totalDegree ≤ 5 at b
    omega
  · have valB : f B = sliceCombine (fun j ↦ x (j+t))
        (fun e ↦ gradAt (slice x) (e.1+t,e.2+2*t)) := by
      unfold B
      rw [combination_map]
      congr 1
      · funext j; simp [f]
      · funext e; exact at_q _
    change x t ^ 6 = f (C ((8 : K)⁻¹)*B)
    rw [map_mul,valB,← slice_power_combination]
    have eight : (8 : K) ≠ 0 := by norm_num
    have inv : f (C ((8 : K)⁻¹)) * (8 : A) = 1 := by
      rw [show f (C ((8 : K)⁻¹)) = (algebraMap K A) ((8 : K)⁻¹) by simp [f]]
      simpa only [map_mul,map_ofNat,map_one] using congrArg (algebraMap K A) (inv_mul_cancel₀ eight)
    rw [← mul_assoc,inv,one_mul]

#print axioms translated_slice_integral
end PermanentFive
