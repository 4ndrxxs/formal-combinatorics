import RationalPrimitiveVector

/-! Anisotropic diagonal forms in two different parameter parities remain anisotropic
over a rational function field. The proof uses polynomial vectors with primitive reduction. -/

noncomputable section
open Module Polynomial
namespace RationalSpecialization
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def DiagAnisotropic (a : I → K) : Prop :=
  ∀ x : I → K, (∑ i, a i * (x i)^2) = 0 → x = 0

/-- The unramified and ramified summands over one rational function variable. -/
def paritySum (a : I → K) (b : J → K) : I ⊕ J → RatFunc K :=
  let φ := algebraMap K[X] (RatFunc K)
  Sum.elim (fun i ↦ φ (C (a i))) (fun j ↦ φ X * φ (C (b j)))

theorem paritySum_anisotropic {a : I → K} {b : J → K}
    (ha : DiagAnisotropic a) (hb : DiagAnisotropic b) :
    DiagAnisotropic (paritySum a b) := by
  classical
  intro v hv
  by_contra nv
  obtain ⟨c,p,_,hp,j,hj⟩ := primitive_vector v nv
  let φ := algebraMap K[X] (RatFunc K)
  let A : K[X] := ∑ i, C (a i) * (p (Sum.inl i))^2
  let B : K[X] := ∑ j, C (b j) * (p (Sum.inr j))^2
  have scaled : ∑ k, paritySum a b k * (φ (p k))^2 = 0 := by
    calc
      _ = ∑ k, c^2 * (paritySum a b k * (v k)^2) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [show φ (p k) = c * v k from hp k]
        ring
      _ = 0 := by rw [← Finset.mul_sum,hv,mul_zero]
  have pol : A + X*B = 0 := by
    apply RatFunc.algebraMap_injective K
    rw [Fintype.sum_sum_type] at scaled
    simpa only [A,B,map_zero,map_add,map_mul,map_sum,map_pow,Finset.mul_sum,
      paritySum,Sum.elim_inl,Sum.elim_inr,φ,mul_assoc] using scaled
  have leftzero : (fun i ↦ (p (Sum.inl i)).eval 0) = 0 := by
    apply ha
    have e := congrArg (evalRingHom (0 : K)) pol
    simpa [A,eval_finsetSum] using e
  have divs (i : I) : X ∣ p (Sum.inl i) := X_dvd_iff.mpr (by
    rw [coeff_zero_eq_eval_zero]
    exact congrFun leftzero i)
  choose q hq using divs
  let A' : K[X] := ∑ i, C (a i) * (q i)^2
  have divisible : A = X^2*A' := by
    dsimp [A,A']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hq i]
    ring
  have cancel : X*A' + B = 0 := by
    apply (mul_eq_zero.mp (show X*(X*A' + B) = 0 by
      rw [divisible] at pol
      linear_combination pol)).resolve_left X_ne_zero
  have rightzero : (fun j ↦ (p (Sum.inr j)).eval 0) = 0 := by
    apply hb
    have e := congrArg (evalRingHom (0 : K)) cancel
    simpa [B,eval_finsetSum] using e
  cases j with
  | inl i => exact hj (congrFun leftzero i)
  | inr j => exact hj (congrFun rightzero j)

theorem point_anisotropic {a : K} (ha : a ≠ 0) :
    DiagAnisotropic (fun _ : Unit ↦ a) := by
  intro x zero
  funext j
  cases j
  simpa [ha] using zero

#print axioms paritySum_anisotropic
end RationalSpecialization
