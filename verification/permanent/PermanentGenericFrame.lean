import QuinticGenericSpan
import PermanentJetFrame

/-! Pad the pivot paths by constant coordinate vectors to a prescribed
coordinate frame. Over the rational function field the pulled-back frame contains
the entire endpoint kernel. Its first jet is the prescribed coordinate frame. -/

noncomputable section
open Matrix Module Polynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [Infinite K] [Fintype n] [DecidableEq n]

theorem padded_generic_frame_weighted (w : Cell → ℕ) {J : Type*} (b c : n → Cell → K) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker w S)
    (v : J → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) :
    ∃ Q : J → Cell → K[X],
      (∀ i j, firstJet K (Q i j) = (Pi.single (v i) 1 : Cell → DualNumber K) j) ∧
      (endpoints (fun a i ↦ algebraMap K (RatFunc K) (b a i))
        (fun a i ↦ algebraMap K (RatFunc K) (c a i))).ker ≤
        Submodule.span (RatFunc K) (Set.range (fun i : J ↦ fun j ↦
          (algebraMap K[X] (RatFunc K) (Q i j)) / (algebraMap K[X] (RatFunc K) X)^(2*w j))) := by
  classical
  have supported (i : S) (j : Cell) (hj : j ∉ S) : (Pi.single i.val 1 : Cell → K) j = 0 := by
    have ne : j ≠ i.val := fun h ↦ hj (h ▸ i.property)
    simp [ne]
  choose q origin away using fun i : S ↦ paths (Pi.single i.val 1) (supported i)
  let q2 (s : S) (j : Cell) := (q s j).comp (X^2)
  let base (i : J) (j : Cell) : K[X] :=
    if h : v i ∈ S then q ⟨v i,h⟩ j else Polynomial.C ((Pi.single (v i) 1 : Cell → K) j)
  let Q (i : J) (j : Cell) := (base i j).comp (X^2)
  have bzero (i : J) (j : Cell) : (base i j).eval 0 = (Pi.single (v i) 1 : Cell → K) j := by
    by_cases h : v i ∈ S <;> simp [base,h,origin]
  refine ⟨Q,?_,?_⟩
  · intro i j
    rw [show Q i j = (base i j).comp (X^2) from rfl,jet_even_path,bzero]
    by_cases h : j = v i <;> simp [h]
  · let f := algebraMap K[X] (RatFunc K)
    let τ := f X
    let g (j : Cell) := τ^(2*w j)
    let U := (endpoints (fun a i ↦ algebraMap K (RatFunc K) (b a i))
      (fun a i ↦ algebraMap K (RatFunc K) (c a i))).ker
    have nt : τ ≠ 0 := fun h ↦ Polynomial.X_ne_zero (RatFunc.algebraMap_injective K (h.trans f.map_zero.symm))
    have qzero (s : S) (j : Cell) : (q2 s j).eval 0 = (Pi.single s.val 1 : Cell → K) j := by
      simp [q2,Polynomial.eval_comp,origin]
    have qin (s : S) : (fun j ↦ f (q2 s j) / g j) ∈ U := by
      have h := unscale_path b c (fun i ↦ 2*w i) (q2 s) (doubled_path (q s) w (away s)) τ nt
      simpa only [τ,f,eval_rational_parameter] using h
    have eq := span_generic_kernel S q2 qzero g (fun j ↦ pow_ne_zero _ nt) U
      (extended_endpoint_dimension b c S card lift) qin
    change U ≤ _
    rw [eq]
    apply Submodule.span_mono
    rintro _ ⟨s,rfl⟩
    obtain ⟨i,hi⟩ := cover s.val s.property
    refine ⟨i,?_⟩
    funext j
    simp [Q,base,hi,s.property,q2,g,τ,f]

theorem padded_generic_frame {J : Type*} (b c : n → Cell → K) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S)
    (v : J → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j) :
    ∃ Q : J → Cell → K[X],
      (∀ i j, firstJet K (Q i j) = (Pi.single (v i) 1 : Cell → DualNumber K) j) ∧
      (endpoints (fun a i ↦ algebraMap K (RatFunc K) (b a i))
        (fun a i ↦ algebraMap K (RatFunc K) (c a i))).ker ≤
        Submodule.span (RatFunc K) (Set.range (fun i : J ↦ fun j ↦
          (algebraMap K[X] (RatFunc K) (Q i j)) / (algebraMap K[X] (RatFunc K) X)^(2*weight j))) := by
  exact padded_generic_frame_weighted weight b c S card lift paths v cover

#print axioms padded_generic_frame
end PermanentFive
