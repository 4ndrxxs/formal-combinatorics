import Quantum.Hadamard.ArithmeticSingularFrobenius

/-! Local representations by the two Frobenius quadratic forms. -/
noncomputable section
namespace HadamardMod.FrobeniusConic
open Hadamard.Arithmetic Hadamard.Arithmetic.PowerResidues

/-- A unit first parameter permits its simultaneous realization by a prime. -/
def Represents {R : Type*} [CommRing R] (b : Bool) (r : R) : Prop :=
  ∃ x y : R, IsUnit x ∧ r = 2 * (if b then 2 else 1) * (x^2+1) * y^2

private theorem from_square {R : Type*} [CommRing R] (u : Rˣ) (hu : (u:R)=2)
    {b : Bool} {r s : R} (hs : r = (if b then 2 else 1)*s^2) : Represents b r := by
  have inv : (2:R) * (↑u⁻¹:R) = 1 := by rw [←hu]; simp
  refine ⟨1, (↑u⁻¹:R)*s, isUnit_one, ?_⟩
  rw [hs, one_pow, show (1:R)+1=2 by norm_num]
  calc
    _ = (if b then (2:R) else 1)*(2*(↑u⁻¹:R))^2*s^2 := by rw [inv]; simp
    _ = _ := by ring

theorem represents_unit {p a : ℕ} [Fact p.Prime] (po : 2<p)
    {r : ZMod (p^(a+1))} (ur : IsUnit r) : ∃ b : Bool, Represents b r := by
  let m := p^(a+1)
  have pp : p.Prime := Fact.out
  let two := ZMod.unitOfCoprime 2 ((two_coprime_prime pp po).pow_right (a+1))
  have hu : (two:ZMod m) = 2 := by
    simpa only [Nat.cast_ofNat] using (ZMod.coe_unitOfCoprime 2 ((two_coprime_prime pp po).pow_right (a+1)))
  have u2 : IsUnit (2:ZMod m) := hu ▸ two.isUnit
  by_cases sr : IsSquare r
  · obtain ⟨s, eq⟩ := sr
    exact ⟨false,from_square two hu (by simpa only [Bool.false_eq_true,ite_false,one_mul,pow_two] using eq)⟩
  by_cases s2 : IsSquare (2:ZMod m)
  · let w := (↑two⁻¹:ZMod m)*r
    have uw : IsUnit w := two⁻¹.isUnit.mul ur
    have eq : 2*w=r := by dsimp only [w]; rw [←hu]; simp
    have ns : ¬IsSquare (red p a w) := fun h => sr (eq ▸ s2.mul (square_of_red po uw h))
    obtain ⟨x,y,xy⟩ := ZMod.sq_add_sq p (red p a w)
    have xx : x≠0 := by
      rintro rfl
      exact ns ⟨y,by simpa [pow_two] using xy.symm⟩
    have yy : y≠0 := by
      rintro rfl
      exact ns ⟨x,by simpa [pow_two] using xy.symm⟩
    let Y : ZMod m := y.val
    have ry : red p a Y=y := (map_natCast _ _).trans (ZMod.natCast_zmod_val y)
    have uy : IsUnit Y := unit_of_red (ry ▸ yy)
    have rx : red p a (w-Y^2)=x^2 := by rw [map_sub,map_pow,ry,←xy];ring
    have ux : IsUnit (w-Y^2) := unit_of_red (rx ▸ pow_ne_zero _ xx)
    obtain ⟨X, Xeq⟩ := square_of_red po ux (rx ▸ ⟨x,pow_two x⟩)
    have uX : IsUnit X := isUnit_of_mul_isUnit_left (Xeq ▸ ux : IsUnit (X*X))
    let T := X*(↑uy.unit⁻¹:ZMod m)
    have TY : T*Y=X := by
      calc
        _ = T*(↑uy.unit:ZMod m) := congrArg (T*·) uy.unit_spec.symm
        _ = X := by simp [T,mul_assoc]
    have sum : w=X^2+Y^2 := by rw [pow_two]; linear_combination Xeq
    refine ⟨false,T,Y,uX.mul uy.unit⁻¹.isUnit,?_⟩
    simp only [Bool.false_eq_true,ite_false,mul_one]
    rw [←eq,sum,←TY]
    ring
  · obtain ⟨z,_,eq⟩ := nonsquare_ratio_unit (p:=p) (a:=a) po ur u2 sr s2
    exact ⟨true,from_square two hu (by simpa only [ite_true] using eq.symm)⟩

/-- A split prime permits any singular target. At an inert prime the exact
valuation below the modulus exponent must be even. -/
theorem represents_primary {p r : ℕ} (pp : p.Prime) (po : 2<p) (e : ℕ)
    (eligible : p%4=1 ∨ p^e∣r ∨ Even (r.factorization p)) :
    ∃ b : Bool, Represents b (r:ZMod (p^e)) := by
  let : Fact p.Prime := ⟨pp⟩
  obtain _|a := e
  · have trivialRing (M : ℕ) (hm : M=1) : ∃ b : Bool, Represents b (r:ZMod M) := by
      subst M
      exact ⟨false,1,0,isUnit_one,Subsingleton.elim _ _⟩
    exact trivialRing _ (pow_zero p)
  let m := p^(a+1)
  by_cases full : m∣r
  · exact ⟨false,1,0,isUnit_one,by simp [(ZMod.natCast_eq_zero_iff _ _).mpr full]⟩
  by_cases singular : p∣r
  · by_cases split : p%4=1
    · obtain ⟨t,tp,_,tr⟩ := singular_frobenius_prime (a:=a) pp split singular
      have c : t.Coprime p := (pp.coprime_iff_not_dvd.mpr (fun pt => by
        have low := (tr.of_dvd (dvd_pow_self p (by omega : a+1≠0)))
        have eq := (ZMod.natCast_eq_natCast_iff _ _ _).mpr low
        push_cast at eq
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr pt,(ZMod.natCast_eq_zero_iff _ _).mpr singular] at eq
        have nz : (2:ZMod p)≠0 := (ZMod.isUnit_iff_coprime 2 p).mpr (two_coprime_prime pp po) |>.ne_zero
        exact nz (by simpa using eq))).symm
      refine ⟨false,(t:ZMod m),1,(ZMod.isUnit_iff_coprime _ _).mpr (c.pow_right _),?_⟩
      simpa using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr tr).symm
    have ev : Even (r.factorization p) := eligible.resolve_left split |>.resolve_left full
    obtain ⟨k,hk⟩ := ev
    have nz : r≠0 := fun z => full (z ▸ dvd_zero _)
    let u := r/(p^(r.factorization p))
    have ru : r=p^(r.factorization p)*u := (Nat.ordProj_mul_ordCompl_eq_self r p).symm
    have cu : u.Coprime m := (Nat.coprime_ordCompl pp nz).symm.pow_right _
    obtain ⟨b,x,y,xu,eq⟩ := represents_unit (p:=p) (a:=a) po ((ZMod.isUnit_iff_coprime _ _).mpr cu)
    refine ⟨b,x,(p:ZMod m)^k*y,xu,?_⟩
    calc
      (r:ZMod m) = (p:ZMod m)^(k+k)*(u:ZMod m) := by
        simpa only [Nat.cast_mul,Nat.cast_pow,hk] using congrArg (fun n:ℕ => (n:ZMod m)) ru
      _ = _ := by rw [eq,pow_add]; ring
  · exact represents_unit po ((ZMod.isUnit_iff_coprime _ _).mpr ((pp.coprime_iff_not_dvd.mpr singular).symm.pow_right _))

#print axioms represents_unit
#print axioms represents_primary
end HadamardMod.FrobeniusConic
