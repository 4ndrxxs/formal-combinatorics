import QuinticTorus

/-! Specialization of the even second difference along a diagonal group
that scales the polynomial. The centre of the difference is arbitrary. -/

noncomputable section
open MvPolynomial
namespace QuinticPencil
variable {K I : Type*} [Field K]

private def evenPolynomial (p : MvPolynomial I K) (y : I → K) : MvPolynomial I K :=
  MvPolynomial.eval₂Hom C (fun i ↦ C (y i) + X i) p +
  MvPolynomial.eval₂Hom C (fun i ↦ C (y i) - X i) p - C (2 * MvPolynomial.eval y p)

private theorem eval_even (p : MvPolynomial I K) (y z : I → K) :
    MvPolynomial.eval z (evenPolynomial p y) =
      MvPolynomial.eval (y+z) p + MvPolynomial.eval (y-z) p - 2 * MvPolynomial.eval y p := by
  have composition : (MvPolynomial.eval z).comp (C : K →+* MvPolynomial I K) = RingHom.id K := by
    ext a; simp
  simp only [evenPolynomial,map_add,map_sub,MvPolynomial.eval_C,MvPolynomial.map_eval₂Hom,
    composition,MvPolynomial.eval_X]
  rfl

theorem specialize_even (L : Submodule K (I → K)) (S : Finset I) (w : I → ℕ)
    (p : MvPolynomial I K)
    (scale : ∀ t : K, t ≠ 0 → ∃ a : K, ∀ v : I → K,
      MvPolynomial.eval (fun i ↦ t^(w i)*v i) p = a * MvPolynomial.eval v p)
    (special : ∀ q : MvPolynomial I K,
      (∀ x ∈ L, ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun i ↦ t^(w i)*x i) q = 0) →
      ∀ z : I → K, (∀ j ∉ S, z j = 0) → MvPolynomial.eval z q = 0)
    (even : ∀ z ∈ L, ∀ y : I → K,
      MvPolynomial.eval (y+z) p + MvPolynomial.eval (y-z) p = 2 * MvPolynomial.eval y p)
    (z : I → K) (supported : ∀ j ∉ S, z j = 0) (y : I → K) :
    MvPolynomial.eval (y+z) p + MvPolynomial.eval (y-z) p = 2 * MvPolynomial.eval y p := by
  apply sub_eq_zero.mp
  rw [← eval_even]
  apply special _ _ z supported
  intro x hx t nt
  obtain ⟨a,sc⟩ := scale t nt
  let u : I → K := fun i ↦ y i / t^(w i)
  have back (i : I) : t^(w i)*u i = y i := by dsimp [u]; field_simp
  have pos : (fun i ↦ t^(w i)*(u+x) i) = y + (fun i ↦ t^(w i)*x i) := by
    funext i; simp [mul_add,back]
  have neg : (fun i ↦ t^(w i)*(u-x) i) = y - (fun i ↦ t^(w i)*x i) := by
    funext i; simp [mul_sub,back]
  have h1 := sc (u+x)
  have h2 := sc (u-x)
  have h0 := sc u
  rw [pos] at h1
  rw [neg] at h2
  simp only [back] at h0
  rw [eval_even,h1,h2,h0]
  linear_combination a * even x hx u

#print axioms specialize_even
end QuinticPencil
