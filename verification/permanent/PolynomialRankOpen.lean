import QuinticTorus

/-! The locus of a nonzero polynomial is dense in a linear space over an
infinite field. A polynomial identity verified on a nonempty maximal-rank
open subset of a polynomial matrix extends to the entire linear space. -/

noncomputable section
open Matrix MvPolynomial
namespace PolynomialRankOpen
variable {K I n : Type*} [Field K] [Infinite K] [Fintype n] [DecidableEq n]

private def along (w z : I → K) : MvPolynomial I K →+* Polynomial K :=
  eval₂Hom Polynomial.C (fun i ↦ Polynomial.C (w i) + Polynomial.X*Polynomial.C (z i-w i))

omit [Infinite K] in
private theorem eval_along (w z : I → K) (t : K) (f : MvPolynomial I K) :
    Polynomial.eval t (along w z f) = MvPolynomial.eval (w + t • (z-w)) f := by
  have h : (Polynomial.evalRingHom t).comp (along w z) = MvPolynomial.eval (w + t • (z-w)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [along]
    · intro i
      simp [along,smul_eq_mul]
  exact RingHom.congr_fun h f

theorem vanish_on_linear_space (L : Submodule K (I → K)) (A : Matrix n n (MvPolynomial I K))
    (r : ℕ) (w : I → K) (hw : w ∈ L) (large : r < ((MvPolynomial.eval w).mapMatrix A).rank)
    (q : MvPolynomial I K)
    (van : ∀ x ∈ L, r < ((MvPolynomial.eval x).mapMatrix A).rank → MvPolynomial.eval x q = 0)
    (z : I → K) (hz : z ∈ L) : MvPolynomial.eval z q = 0 := by
  by_contra nz
  let S : Set (I → K) := {x | x ∈ L ∧ MvPolynomial.eval x q ≠ 0}
  have spec (f : MvPolynomial I K) (h : ∀ x ∈ S, MvPolynomial.eval x f = 0) :
      MvPolynomial.eval w f = 0 := by
    have qnz : along w z q ≠ 0 := by
      intro zero
      have e := eval_along w z 1 q
      rw [zero,Polynomial.eval_zero,one_smul,add_sub_cancel] at e
      exact nz e.symm
    have prod : along w z f * along w z q = 0 := by
      apply Polynomial.funext
      intro t
      rw [Polynomial.eval_mul,Polynomial.eval_zero,eval_along,eval_along]
      by_cases eq : MvPolynomial.eval (w+t • (z-w)) q = 0
      · simp [eq]
      · rw [h _ ⟨L.add_mem hw (L.smul_mem t (L.sub_mem hz hw)),eq⟩,zero_mul]
    have zero := (mul_eq_zero.mp prod).resolve_right qnz
    have e := eval_along w z 0 f
    rw [zero,Polynomial.eval_zero,zero_smul,add_zero] at e
    exact e.symm
  have small (x : I → K) (hx : x ∈ S) : ((MvPolynomial.eval x).mapMatrix A).rank ≤ r :=
    Nat.le_of_not_lt (fun greater ↦ hx.2 (van x hx.1 greater))
  exact (Nat.not_lt_of_ge (QuinticPencil.rank_specialization A S w spec r small)) large

#print axioms vanish_on_linear_space
end PolynomialRankOpen
