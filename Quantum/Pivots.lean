module

public import Quantum.Coefficients

/-! A single nonzero pivot coordinate per representative suffices for
checking projective separation by two-coordinate minors. -/

@[expose] public section
namespace QuantumCertificate.Coefficients

variable {T : Type} [AddCommMonoid T] (a : Coefficients T)

def PivotTest {n c : ℕ} (r : Fin c → Fin n → T) (p : Fin c → Fin n) : Prop :=
  ∀ i j, i < j → ∃ y, a.mul (r i (p i)) (r j y) ≠ a.mul (r i y) (r j (p i))

instance [DecidableEq T] {n c : ℕ} (r : Fin c → Fin n → T) (p : Fin c → Fin n) :
    Decidable (a.PivotTest r p) :=
  inferInstanceAs (Decidable (∀ i j : Fin c, i < j → ∃ y : Fin n,
    a.mul (r i (p i)) (r j y) ≠ a.mul (r i y) (r j (p i))))

theorem distinct_of_pivots {n c : ℕ} {r : Fin c → Fin n → T} (p : Fin c → Fin n)
    (h : a.PivotTest r p) : a.DistinctLines r := by
  have comm (u v : T) : a.mul u v = a.mul v u := by
    apply a.faithful
    simp [a.mul_eval, mul_comm]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨y,hy⟩ := h i j hij
    exact ⟨p i,y,hy⟩
  · obtain ⟨y,hy⟩ := h j i hji
    refine ⟨y,p j,?_⟩
    simpa only [comm (r i y), comm (r i (p j))] using hy

end QuantumCertificate.Coefficients

namespace QuantumCertificate

noncomputable def integerModel : Coefficients ℤ where
  eval := (Int.castRingHom ℂ).toAddMonoidHom
  faithful := by
    intro a b h
    change (a : ℂ) = (b : ℂ) at h
    exact_mod_cast h
  mul := (· * ·)
  mul_eval := by simp
  bar := id
  bar_eval := by simp

end QuantumCertificate
