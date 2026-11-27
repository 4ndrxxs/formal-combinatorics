import Quantum.Hadamard.ArithmeticLinear
import Quantum.Hadamard.ArithmeticBase

/-! Reduction of unit square classes at odd prime powers and a linear-twist witness upstairs. -/
noncomputable section
namespace Hadamard.Arithmetic.PowerResidues
variable {p a : ℕ} [Fact p.Prime]

abbrev red (p a : ℕ) : ZMod (p^(a+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero a)) _

theorem unit_of_red {x : ZMod (p^(a+1))} (hx : red p a x≠0) : IsUnit x := by
  have hp : p.Prime := Fact.out
  have : NeZero (p^(a+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hx' : (x.val:ZMod p)≠0 := by
    rw [← ZMod.natCast_zmod_val x] at hx
    simpa only [map_natCast] using hx
  have cp := (hp.coprime_iff_not_dvd.mpr (fun d => hx' ((ZMod.natCast_eq_zero_iff _ _).mpr d))).symm
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.isUnit_iff_coprime _ _).mpr (cp.pow_right _)

theorem red_generator_nonsquare (po : 2<p) {g : (ZMod (p^(a+1)))ˣ}
    (gen : ∀ z, ∃ k:ℕ, g^k=z) : ¬ IsSquare (red p a (g:ZMod (p^(a+1)))) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p^(a+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨v,nv⟩ := FiniteField.exists_nonsquare (F:=ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using (show p≠2 by omega))
  have nz : v≠0 := by rintro rfl; exact nv ⟨0,by simp⟩
  obtain ⟨z,ez⟩ := ZMod.unitsMap_surjective (dvd_pow_self p (Nat.succ_ne_zero a)) (Units.mk0 v nz)
  obtain ⟨k,hk⟩ := gen z
  have redz : red p a (z:ZMod (p^(a+1)))=v := congrArg Units.val ez
  intro square
  apply nv
  rw [← redz,←hk,Units.val_pow_eq_pow_val,map_pow]
  exact square.pow _

theorem square_of_red (po : 2<p) {x : ZMod (p^(a+1))} (unit : IsUnit x)
    (square : IsSquare (red p a x)) : IsSquare x := by
  letI := ZMod.isCyclic_units_of_prime_pow p Fact.out (by omega) (a+1)
  obtain ⟨g,gen⟩ := IsCyclic.exists_monoid_generator (α:=(ZMod (p^(a+1)))ˣ)
  have all (z : (ZMod (p^(a+1)))ˣ) : ∃ k:ℕ, g^k=z := (Submonoid.mem_powers_iff _ _).mp (gen z)
  obtain ⟨k,hk⟩ := all unit.unit
  have sx : (g:ZMod (p^(a+1)))^k=x := by simpa only [Units.val_pow_eq_pow_val,IsUnit.unit_spec] using congrArg Units.val hk
  by_cases ev : Even k
  · exact sx ▸ ev.isSquare_pow _
  have ko := Nat.not_even_iff_odd.mp ev
  have gns := red_generator_nonsquare po all
  apply False.elim
  apply (quadraticChar_neg_one_iff_not_isSquare (a:=red p a x)).mp _ square
  rw [←sx,map_pow,map_pow,quadraticChar_neg_one_iff_not_isSquare.mpr gns,ko.neg_one_pow]

theorem nonsquare_ratio_unit (po : 2<p) {x y : ZMod (p^(a+1))}
    (ux:IsUnit x) (uy:IsUnit y) (nx:¬IsSquare x) (ny:¬IsSquare y) :
    ∃ z:ZMod (p^(a+1)), IsUnit z ∧ y*z^2=x := by
  let t := x*(↑uy.unit⁻¹:ZMod (p^(a+1)))
  have ut : IsUnit t := ux.mul uy.unit⁻¹.isUnit
  have tx : t*y=x := calc
    _ = t*(↑uy.unit:ZMod (p^(a+1))) := congrArg (t*·) uy.unit_spec.symm
    _ = x := by simp [t,mul_assoc]
  have rx : ¬ IsSquare (red p a x) := fun h => nx (square_of_red po ux h)
  have ry : ¬ IsSquare (red p a y) := fun h => ny (square_of_red po uy h)
  have rt : red p a t≠0 := (ut.map (red p a)).ne_zero
  have eq := congrArg (quadraticChar (ZMod p)) (congrArg (red p a) tx)
  rw [map_mul,map_mul,quadraticChar_neg_one_iff_not_isSquare.mpr rx,quadraticChar_neg_one_iff_not_isSquare.mpr ry] at eq
  obtain ⟨z,hz⟩ := square_of_red po ut ((quadraticChar_one_iff_isSquare rt).mp (by omega))
  refine ⟨z,?_,?_⟩
  · exact isUnit_of_mul_isUnit_left (hz ▸ ut : IsUnit (z*z))
  · rw [pow_two,←hz,mul_comm,tx]

#print axioms square_of_red
end Hadamard.Arithmetic.PowerResidues
