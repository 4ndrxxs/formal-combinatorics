import QuinticGenericPath
import PermanentDegeneration

/-! A specified echelon support of an endpoint kernel persists under extension of the base field. -/

noncomputable section
open Module Matrix Polynomial
namespace QuinticPencil
variable {K E I n : Type*} [Field K] [Infinite K] [Field E] [Algebra K E]
  [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

theorem extend_endpoint_pivots (b c : n → I → K) (w : I → ℕ) (S : Finset I)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : I → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker w S) :
    let L := (endpoints (fun a i ↦ algebraMap K E (b a i)) (fun a i ↦ algebraMap K E (c a i))).ker
    S.card = finrank E L ∧ (∀ z : I → E, ∃ x ∈ L, ∀ i ∈ S, x i = z i) ∧
      PermanentDegeneration.HasCoordinatePaths L w S := by
  classical
  let f := algebraMap K E
  let L := (endpoints (fun a i ↦ f (b a i)) (fun a i ↦ f (c a i))).ker
  let e (s : S) : I → K := Pi.single s.val 1
  have basis_sum (z : I → E) {j : I} (hj : j ∈ S) :
      (∑ i : S, z i.val * f (e i j)) = z j := by
    let k : S := ⟨j,hj⟩
    rw [Finset.sum_eq_single k]
    · simp [k,e]
    · intro i _ ne
      have neq : j ≠ i.val := fun eq ↦ ne (Subtype.ext eq.symm)
      simp [e,neq]
    · simp
  choose u hu coord using fun s : S ↦ lift (e s)
  have umem (s : S) : (f ∘ u s) ∈ L := by
    obtain ⟨hb,hc⟩ := (endpoint_zero_iff b c (u s)).mp (hu s)
    apply (endpoint_zero_iff _ _ _).mpr
    constructor <;> intro a
    · simpa [f,value,Function.comp_def] using congrArg f (hb a)
    · simpa [f,value,Function.comp_def] using congrArg f (hc a)
  have liftE (z : I → E) : ∃ x ∈ L, ∀ j ∈ S, x j = z j := by
    let x := ∑ i : S, z i.val • (f ∘ u i)
    refine ⟨x,L.sum_mem (fun i _ ↦ L.smul_mem _ (umem i)),?_⟩
    intro j hj
    simpa only [x,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,
      fun i ↦ coord i j hj] using basis_sum z hj
  let P : L →ₗ[E] (S → E) := LinearMap.pi fun i ↦ (LinearMap.proj i.val).comp L.subtype
  have surj : Function.Surjective P := by
    intro z
    obtain ⟨x,hx,eq⟩ := liftE (fun j ↦ if h : j ∈ S then z ⟨j,h⟩ else 0)
    exact ⟨⟨x,hx⟩,funext fun i ↦ by simpa [P,i.property] using eq i.val i.property⟩
  have lower := P.finrank_le_finrank_of_surjective surj
  rw [Module.finrank_pi,Fintype.card_coe] at lower
  refine ⟨lower.antisymm (extended_endpoint_dimension b c S card lift),liftE,?_⟩
  have offsupport (i : S) (j : I) (h : j ∉ S) : e i j = 0 := by
    have ne : j ≠ i.val := fun eq ↦ h (eq ▸ i.property)
    simp [e,ne]
  choose q at0 away using fun i : S ↦ paths (e i) (offsupport i)
  intro z supported
  let Q (j : I) : E[X] := ∑ i : S, C (z i.val) * (q i j).map f
  have evalQ (t : E) (j : I) : (Q j).eval t = ∑ i : S, z i.val * (q i j).eval₂ f t := by
    simp [Q,Polynomial.eval_finsetSum,Polynomial.eval_map]
  refine ⟨Q,?_,?_⟩
  · intro j
    rw [evalQ]
    have at0E (i : S) : (q i j).eval₂ f 0 = f (e i j) := by
      simp only [← at0 i j,Polynomial.eval₂_at_zero,← coeff_zero_eq_eval_zero]
    simp only [at0E]
    by_cases h : j ∈ S
    · exact basis_sum z h
    · simp [fun i ↦ offsupport i j h,supported j h]
  · intro t nt
    let u' (i : S) (j : I) := (q i j).eval₂ f t / t^(w j)
    have inside (i : S) : u' i ∈ L := unscale_path b c w (q i) (away i) t nt
    refine ⟨∑ i : S, z i.val • u' i,L.sum_mem (fun i _ ↦ L.smul_mem _ (inside i)),?_⟩
    intro j
    rw [evalQ]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,u']
    apply Finset.sum_congr rfl
    intro i _
    field_simp [nt]

#print axioms extend_endpoint_pivots
end QuinticPencil
