import Quantum.Hadamard.ArithmeticDense

/-! A single extender and one sign matrix furnish a progression.  The two coin
weights come from varying the size of J - 2I and from iterating the extender. -/
namespace HadamardMod
open Hadamard.Arithmetic

theorem tensor_splice_progression {m h v g : ℕ} {r : ZMod m}
    (H : AtOrder m h) (hp : 0<h) (D : Extender m (Fin v) r)
    (step : 1<v) (gr : (m*h).gcd (v-1)=g) (gp : 0<g) (seed : ((4*h:ℕ):ZMod m)=r) :
    ∃ N, ∀ n ≥ N, n ≡ 4*h [MOD g] → AtOrder m n := by
  let a := (m*h)/g
  let b := (v-1)/g
  have dm : g ∣ m*h := gr ▸ Nat.gcd_dvd_left _ _
  have dv : g ∣ v-1 := gr ▸ Nat.gcd_dvd_right _ _
  have ga : g*a=m*h := Nat.mul_div_cancel' dm
  have gb : g*b=v-1 := Nat.mul_div_cancel' dv
  have cop : a.Coprime b := by
    change a.gcd b=1
    apply Nat.eq_of_mul_eq_mul_left gp
    simpa [← Nat.gcd_mul_left,ga,gb] using gr
  have bp : 0<b := by
    apply Nat.pos_of_ne_zero
    intro z
    rw [z,Nat.mul_zero] at gb
    omega
  refine ⟨4*h+g*(a*b),?_⟩
  intro n large congr
  have ge : 4*h ≤ n := by omega
  obtain ⟨w,hw⟩ := (Nat.modEq_iff_dvd' ge).mp congr.symm
  have eqn : n=4*h+g*w := by omega
  have big : a*b ≤ w := by
    apply Nat.le_of_mul_le_mul_left (c:=g)
    · omega
    · exact gp
  obtain ⟨x,y,hw'⟩ := coprime_coins cop bp big
  have decomposition : n=h*(4+m*x)+y*(v-1) := by
    rw [eqn,hw',Nat.mul_add,← Nat.mul_assoc,ga,← Nat.mul_assoc,gb]
    ring
  have J : AtOrder m (4+m*x) := by
    apply offdiag_four
    push_cast
    simp
  have mod0 : ((h*(4+m*x):ℕ):ZMod m)=r := by
    push_cast at seed ⊢
    simpa [mul_comm] using seed
  have pos : 0<h*(4+m*x) := Nat.mul_pos hp (by omega)
  rw [decomposition]
  simpa only [Fintype.card_fin] using D.iterate pos (at_mul H J) mod0 y

#print axioms tensor_splice_progression
end HadamardMod
