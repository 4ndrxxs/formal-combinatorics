import PermanentWitnesses

/-! Encode the terms of a restricted permanent Hessian by an integer and two exponents.
An affine coefficient table can then be checked using integer arithmetic in the kernel. -/

noncomputable section
open Matrix Finset
namespace PermanentFive.Rectangle
abbrev Token := ℤ × ℕ × ℕ
def value {R : Type*} [CommRing R] (s t : R) (m : Token) : R :=
  (m.1 : R) * s^m.2.1 * t^m.2.2

private def product {I : Type*} (A : Finset I) (v : I → Token) : Token :=
  (∏ i ∈ A, (v i).1, ∑ i ∈ A, (v i).2.1, ∑ i ∈ A, (v i).2.2)

private theorem value_product {R I : Type*} [CommRing R] (s t : R) (A : Finset I) (v : I → Token) :
    value s t (product A v) = ∏ i ∈ A, value s t (v i) := by
  simp only [product,value,Int.cast_prod,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

def termToken (centre : Cell → Token) (e f : Cell) (p : Equiv.Perm Idx) : Token :=
  if p f.2 = f.1 ∧ e.2 ≠ f.2 ∧ p e.2 = e.1 then
    product ((univ.erase f.2).erase e.2) (fun j ↦ centre (p j,j))
  else (0,0,0)

def affineTag (m : Token) : Prop :=
  m.1 = 0 ∨ m.2 = (0,0) ∨ m.2 = (1,0) ∨ m.2 = (0,1)
instance (m : Token) : Decidable (affineTag m) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def coefficient (m : Token) (u : ℕ × ℕ) : ℤ := if m.2 = u then m.1 else 0

private theorem eval_affine {R : Type*} [CommRing R] (s t : R) (m : Token) (h : affineTag m) :
    value s t m = (coefficient m (0,0) : R) + (coefficient m (1,0) : R) * s +
      (coefficient m (0,1) : R) * t := by
  rcases m with ⟨a,i,j⟩
  rcases h with h|h|h|h
  · change a = 0 at h
    subst a
    simp [value,coefficient]
  all_goals cases h; simp [value,coefficient]

def blockCoefficient (centre : Cell → Token) (e f : Cell) (u : ℕ × ℕ) : ℤ :=
  ∑ p : Equiv.Perm Idx, coefficient (termToken centre e f p) u

theorem affine_second {R : Type*} [CommRing R] (s t : R) (centre : Cell → Token) (e f : Cell)
    (tags : ∀ p, affineTag (termToken centre e f p)) :
    secondAt (value s t ∘ centre) e f =
      (blockCoefficient centre e f (0,0) : R) +
      (blockCoefficient centre e f (1,0) : R) * s +
      (blockCoefficient centre e f (0,1) : R) * t := by
  have typed : secondAt (value s t ∘ centre) e f =
      ∑ p : Equiv.Perm Idx, value s t (termToken centre e f p) := by
    unfold secondAt
    apply sum_congr rfl
    intro p _
    by_cases h : p f.2 = f.1 ∧ e.2 ≠ f.2 ∧ p e.2 = e.1
    · simp [termToken,h,value_product]
    · simp [termToken,h,value]
  rw [typed]
  simp_rw [fun p ↦ eval_affine s t _ (tags p)]
  simp [blockCoefficient,Finset.sum_add_distrib,Finset.sum_mul]

#print axioms affine_second
end PermanentFive.Rectangle
