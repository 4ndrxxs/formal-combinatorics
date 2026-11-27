import Quantum.Hadamard.TorusOddComposite

/-! Unbounded progression seeds and the companion to a fixed modular extender. -/
noncomputable section
namespace HadamardMod.TorusOddComposite

theorem square_dense_above {m A n:ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) (ap : 0 < A)
    (ma : m∣A) (sq : IsSquare (n:ZMod m)) (B : ℕ) :
    ∃ h>B, AtOrder m h ∧ h ≡ n [MOD A] := by
  let u := n + A*(B+1)
  have un : u ≡ n [MOD A] := by simp [u,Nat.ModEq]
  have sn : IsSquare (u:ZMod m) := by
    rwa [(ZMod.natCast_eq_natCast_iff u n m).mpr (un.of_dvd ma)]
  let P := A*(u+1)
  have au : A∣P := dvd_mul_right A _
  have up : u<P := by dsimp [P];nlinarith
  obtain ⟨h,_,H,hu⟩ := odd_square_dense mp om (by omega : 0<P) (ma.trans au) sn
  have low : u≤h := by
    have e : h%P=u := Eq.trans (show h%P=u%P from hu) (Nat.mod_eq_of_lt up)
    rw [←e]
    exact Nat.mod_le _ _
  refine ⟨h,?_,H,(hu.of_dvd au).trans un⟩
  change n + A*(B+1) ≤ h at low
  nlinarith

/-- Every progression whose representative is a square modulo m has unbounded
    supported orders, with an arbitrary positive period. -/
theorem square_progression {m A n:ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) (ap : 0 < A)
    (sq : IsSquare (n:ZMod m)) (B : ℕ) :
    ∃ h>B, AtOrder m h ∧ h ≡ n [MOD A] := by
  obtain ⟨h,hh,H,hn⟩ := square_dense_above mp om (Nat.mul_pos ap mp) (dvd_mul_left m A) sq B
  exact ⟨h,hh,H,hn.of_dvd (dvd_mul_right A m)⟩

theorem square_class_of_extender {m r:ℕ} {I:Type*} [Fintype I]
    (mp : 0 < m) (om : (2:ℕ).Coprime m) (sq : IsSquare (r:ZMod m))
    (D : Extender m I (r:ZMod m)) (large : 1 < Fintype.card I) :
    ∃ B, ∀ n ≥ B, n ≡ r [MOD m] → AtOrder m n := by
  apply large_of_progression_seeds D large
  intro A ap ma n nr
  apply odd_square_dense mp om ap ma
  rwa [(ZMod.natCast_eq_natCast_iff n r m).mpr nr]

#print axioms square_dense_above
#print axioms square_progression
#print axioms square_class_of_extender
end HadamardMod.TorusOddComposite





