module

public import Quantum.OddInduction
public import Quantum.Bounds

/-! A six-order base interval suffices for every order at least six. -/
@[expose] public section
namespace QuantumCertificate

theorem good_above_six (base : ∀ m, 6 ≤ m → m < 12 → Good m) (n : ℕ) (hn : 6 ≤ n) :
    Good n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases small : n < 12
    · exact base n hn small
    let m := n/2
    have hm : 6 ≤ m := by dsimp [m]; omega
    have hmLt : m < n := by dsimp [m]; omega
    have mid := ih m hmLt hm
    by_cases even : n%2=0
    · have eq : n=m+m := by dsimp [m]; omega
      rw [eq]
      exact mid.even (by omega)
    · have eq : n=(m+1)+m := by dsimp [m]; omega
      rw [eq]
      exact mid.odd (ih (m+1) (by omega) (by omega)) (by omega)

theorem spectrum_above_six_of_base (base : ∀ m, 6 ≤ m → m < 12 → Good m)
    (n : ℕ) (hn : 6 ≤ n) (c : ℕ) : Realized n c ↔ n ≤ c ∧ c ≤ n*n ∧ c ≠ n+1 := by
  let : NeZero n := ⟨by omega⟩
  exact ⟨fun h => by simpa only [pow_two] using h.bounds,
    fun ⟨lo,hi,hole⟩ => good_above_six base n hn c lo hi hole⟩

#print axioms spectrum_above_six_of_base
end QuantumCertificate
