import Quantum.Hadamard.TorusOddCompositeConsequences
import Quantum.Hadamard.ArithmeticSingularNecessity

/-! The precise progression obstruction for odd modular Hadamard orders. -/
noncomputable section
namespace HadamardMod.TorusOddComposite

/-- A progression contains arbitrarily large odd integer sign-matrix orders
    exactly when it permits odd numbers and meets a square class modulo m. -/
theorem odd_progression_iff {m A n:ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) (ap : 0 < A) :
    (∀ B:ℕ, ∃ h>B, Odd h ∧ IntegralSolution m h ∧ h ≡ n [MOD A]) ↔
      (Odd A ∨ Odd n) ∧ IsSquare (n:ZMod (A.gcd m)) := by
  let g := A.gcd m
  have gp : 0 < g := Nat.gcd_pos_of_pos_right _ mp
  letI : NeZero g := ⟨gp.ne'⟩
  constructor
  · intro seq
    obtain ⟨h,_,oh,H,hn⟩ := seq 0
    constructor
    · rcases Nat.even_or_odd A with ea|oa
      · right
        apply Nat.odd_iff.mpr
        rw [← (show h%2=n%2 from hn.of_dvd ea.two_dvd)]
        exact Nat.odd_iff.mp oh
      · exact Or.inl oa
    · have ht := (odd_integral_necessary mp oh H).map
          (ZMod.castHom (Nat.gcd_dvd_right A m) (ZMod g))
      rw [map_natCast] at ht
      rwa [← (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hn.of_dvd (Nat.gcd_dvd_left A m))]
  · rintro ⟨parity,square⟩
    obtain ⟨root,hr⟩ := square
    have ng : n ≡ root.val^2 [MOD A.gcd m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp
      (by simpa only [Nat.cast_pow,Nat.cast_mul,ZMod.natCast_zmod_val,pow_two] using hr)
    obtain ⟨z,za,zm⟩ := Nat.chineseRemainder' ng
    have use {u:ℕ} (ua : u ≡ n [MOD A]) (um : u ≡ root.val^2 [MOD m]) (uo : Odd u) :
        ∀ B:ℕ, ∃ h>B, Odd h ∧ IntegralSolution m h ∧ h ≡ n [MOD A] := by
      have sq : IsSquare (u:ZMod m) := by
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr um,Nat.cast_pow]
        exact ⟨(root.val:ZMod m),pow_two _⟩
      intro B
      obtain ⟨h,big,H,hu⟩ := square_progression mp om (Nat.mul_pos (by decide : 0<2) ap) sq B
      have eq : h%2=u%2 := hu.of_dvd (dvd_mul_right 2 A)
      exact ⟨h,big,Nat.odd_iff.mpr (eq.trans (Nat.odd_iff.mp uo)),integer_gram H,
        (hu.of_dvd (dvd_mul_left A 2)).trans ua⟩
    by_cases zo : Odd z
    · exact use za zm zo
    have ze : Even z := Nat.not_odd_iff_even.mp zo
    have ao : Odd A := by
      rcases parity with oa|on
      · exact oa
      · rcases Nat.even_or_odd A with ea|oa
        · have eq : z%2=n%2 := za.of_dvd ea.two_dvd
          exact (zo (Nat.odd_iff.mpr (eq.trans (Nat.odd_iff.mp on)))).elim
        · exact oa
    have az : z+A*m ≡ z [MOD A] := by simp [Nat.ModEq]
    have mz : z+A*m ≡ z [MOD m] := by simp [Nat.ModEq]
    exact use (az.trans za) (mz.trans zm) (ze.add_odd (ao.mul (Nat.coprime_two_left.mp om)))

#print axioms odd_progression_iff
end HadamardMod.TorusOddComposite



