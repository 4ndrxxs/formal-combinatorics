import SignedDivisorGrid
import Mathlib.Tactic.Primality.Lucas

namespace Signed39.Contraction

private def smallPrime (n : ℕ) : Decidable n.Prime :=
  decidable_of_iff (2≤n ∧ ∀j:Fin (n.sqrt+1),2≤j.val → ¬j.val∣n) (by
    rw [Nat.prime_def_le_sqrt]
    constructor
    · rintro ⟨lo,h⟩
      exact ⟨lo,fun m mn mx=>h ⟨m,by omega⟩ mn⟩
    · rintro ⟨lo,h⟩
      exact ⟨lo,fun j hj=>h j.val hj (by omega)⟩)

private def smallQuotient (v n : ℕ) (d : QuotientInput) : Decidable (d.valid v n) := by
  unfold QuotientInput.valid quotientCertificate
  letI := smallPrime d.r
  letI := smallPrime d.q
  letI : Decidable (d.q^d.e≡d.r-1 [MOD d.r]) :=
    decidable_of_iff (Mathlib.Tactic.Primality.powMod d.q d.e d.r=(d.r-1)%d.r)
      (by rw [Mathlib.Tactic.Primality.powMod_def]; rfl)
  infer_instance

private def smallDivisor (p s d m : ℕ) (keep : List (ℕ × ℤ)) (w : Option QuotientInput) :
    Decidable (oneDivisor p s d m keep w) :=
  match w with
  | some z => smallQuotient (p*m) (p*s) z
  | none => inferInstanceAs (Decidable (oneDivisor p s d m keep none))

def divisorGridSlice (p s B : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) (d : ℕ) : Prop :=
  let N := endpointValue p s d
  N<B^2 ∧ ∀ j : Fin B, 0<j.val → j.val∣N → ∀ other : Bool,
    let m := if other then N/j.val else j.val
    p < m → ¬2∣m → ¬p∣m → oneDivisor p s d m keep (w m)

instance (p s B : ℕ) (w : ℕ → Option QuotientInput) (keep : List (ℕ × ℤ)) (d : ℕ) :
    Decidable (divisorGridSlice p s B w keep d) := by
  unfold divisorGridSlice
  letI (m:ℕ) : Decidable (oneDivisor p s d m keep (w m)) := smallDivisor p s d m keep (w m)
  infer_instance

end Signed39.Contraction
