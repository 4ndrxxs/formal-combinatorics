import QuinticScalarExtension
import QuinticOddZero

/-! Polynomial echelon paths give vectors in the scaled endpoint kernel
at an arbitrary nonzero parameter in an extension field. -/

noncomputable section
open Matrix Module Polynomial
namespace QuinticPencil
variable {K E I n : Type*} [Field K] [Field E] [Fintype I] [Fintype n] [DecidableEq n]

private theorem zero_off_origin [Infinite K] (f : K[X]) (off : ∀ t : K, t ≠ 0 → f.eval t = 0) :
    f = 0 := by
  have h : X*f = 0 := Polynomial.funext (fun t ↦ by by_cases ht : t = 0 <;> simp [ht,off])
  exact (mul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero

/-- Evaluate a list of polynomial coordinates at a nonzero extension
parameter and undo the diagonal weights. Clearing the common denominator
gives polynomial identities tested over the original infinite field. -/
theorem unscale_path [Infinite K] [Algebra K E] (b c : n → I → K) (w : I → ℕ) (q : I → K[X])
    (away : ∀ t : K, t ≠ 0 → ∃ x ∈ (endpoints b c).ker, ∀ j, (q j).eval t = t^(w j)*x j)
    (t : E) (nt : t ≠ 0) :
    (fun j ↦ (q j).eval₂ (algebraMap K E) t / t^(w j)) ∈
      (endpoints (fun a i ↦ algebraMap K E (b a i)) (fun a i ↦ algebraMap K E (c a i))).ker := by
  classical
  let W := Finset.univ.sup w
  have le (j : I) : w j ≤ W := Finset.le_sup (Finset.mem_univ j)
  have row (l : I → K) (zero : ∀ x ∈ (endpoints b c).ker, value l x = 0) :
      value (fun i ↦ algebraMap K E (l i)) (fun j ↦ (q j).eval₂ (algebraMap K E) t / t^(w j)) = 0 := by
    let g : K[X] := ∑ j, Polynomial.C (l j) * X^(W-w j) * q j
    have gz : g = 0 := by
      apply zero_off_origin
      intro u nu
      obtain ⟨x,hx,eq⟩ := away u nu
      have term (j : I) : l j * u^(W-w j) * (u^(w j)*x j) = u^W * (l j*x j) := by
        have pw : u^(W-w j) * u^(w j) = u^W := by rw [← pow_add,Nat.sub_add_cancel (le j)]
        linear_combination l j * x j * pw
      simp only [g,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
        Polynomial.eval_X,eq,term,← Finset.mul_sum]
      change u^W * value l x = 0
      rw [zero x hx,mul_zero]
    have eval := congrArg (Polynomial.eval₂ (algebraMap K E) t) gz
    simp only [g,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_zero] at eval
    have term (j : I) : t^W * (algebraMap K E (l j) * ((q j).eval₂ (algebraMap K E) t / t^(w j))) =
        algebraMap K E (l j) * t^(W-w j) * (q j).eval₂ (algebraMap K E) t := by
      have pw : t^W = t^(W-w j)*t^(w j) := by rw [← pow_add,Nat.sub_add_cancel (le j)]
      rw [pw]
      field_simp
    apply (mul_eq_zero.mp (show t^W * _ = 0 from ?_)).resolve_left (pow_ne_zero _ nt)
    simpa only [value,Finset.mul_sum,term] using eval
  exact (endpoint_zero_iff _ _ _).mpr
    ⟨fun a ↦ row (b a) (fun x hx ↦ ((endpoint_zero_iff b c x).mp hx).1 a),
     fun a ↦ row (c a) (fun x hx ↦ ((endpoint_zero_iff b c x).mp hx).2 a)⟩

omit [Fintype I] in
/-- Reparameterization by the square kills all first-order changes in
the path coordinates. -/
theorem doubled_path {L : Submodule K (I → K)} (q : I → K[X]) (w : I → ℕ)
    (away : ∀ t : K, t ≠ 0 → ∃ x ∈ L, ∀ j, (q j).eval t = t^(w j)*x j) (t : K) (nt : t ≠ 0) :
    ∃ x ∈ L, ∀ j, ((q j).comp (X^2)).eval t = t^(2*w j)*x j := by
  obtain ⟨x,hx,eq⟩ := away (t^2) (pow_ne_zero _ nt)
  exact ⟨x,hx,fun j ↦ by simp [Polynomial.eval_comp,eq,pow_mul]⟩

#print axioms unscale_path
#print axioms doubled_path
end QuinticPencil
