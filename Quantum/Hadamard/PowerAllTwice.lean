import Quantum.Hadamard.PowerUnitOrders
import Quantum.Hadamard.ArithmeticSingularSeeds
import Quantum.Hadamard.ArithmeticSingularNecessity
import Quantum.Hadamard.ArithmeticTwoPowers
import Quantum.Hadamard.Weaken

/-! Positive prime-power classes at twice-odd orders, including singular classes that
are a unit times a square. Four-divisible orders and all admissible odd orders are included. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

def SquareTimesUnit {m:ℕ} (r:ZMod m) : Prop := ∃ u:(ZMod m)ˣ, ∃ z:ZMod m, r=(u:ZMod m)*z^2

private theorem seed_unit_times_square {p e r:ℕ} (pp:p.Prime) (po : 2<p) (mh : 1<p^e)
    (fact : SquareTimesUnit (r:ZMod (p^e))) :
    ∃ h>0, AtOrder (p^e) h ∧ h ≡ 2 [MOD 4] ∧ h ≡ r [MOD p^e] := by
  let m := p^e
  have om : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right e
  have mp : 0 < m := pow_pos pp.pos _
  letI : NeZero m := ⟨mp.ne'⟩
  obtain ⟨u,z,rz⟩ := fact
  obtain ⟨N,all⟩ := prime_power_units_classification pp po e
  obtain ⟨t,t4,tu⟩ := Nat.chineseRemainder (om.pow_left 2 : (4:ℕ).Coprime m) 2 (u:ZMod m).val
  let k := t+(4*m)*(N+1)
  have c4 : k ≡ 2 [MOD 4] := by
    apply Nat.ModEq.trans _ t4
    simp [k,Nat.ModEq,Nat.mul_assoc]
  have cm : k ≡ (u:ZMod m).val [MOD m] := by
    apply Nat.ModEq.trans _ tu
    change (t+4*m*(N+1))%m=t%m
    rw [show 4*m*(N+1)=(4*(N+1))*m by ring,Nat.add_mul_mod_self_right]
  have cop := coprime_of_modEq cm (ZMod.val_coe_unit_coprime u)
  have even : Even k := by change k%4=2 at c4; rw [Nat.even_iff]; omega
  have big : N<k := by dsimp [k]; nlinarith
  have K := atOrder_of_integral ((all k big.le cop).mpr (Or.inl even))
  have mK := ((ZMod.natCast_eq_natCast_iff _ _ _).mpr cm).trans (ZMod.natCast_zmod_val (u:ZMod m))
  let s := (z^2).val
  have sz : (s:ZMod m)=z^2 := ZMod.natCast_zmod_val _
  have sq : IsSquare (s:ZMod m) := ⟨z,by rw [sz,pow_two]⟩
  obtain ⟨j,jp,J,j4,jm⟩ := square_seed_each_mod_four mh om sq (1:Fin 4)
  refine ⟨k*j,Nat.mul_pos (by omega) jp,at_mul K J,?_,?_⟩
  · simpa using c4.mul j4
  · apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
    rw [Nat.cast_mul,mK,(ZMod.natCast_eq_natCast_iff _ _ _).mpr jm,sz,rz]

theorem power_even_square_factor {p:ℕ} (pp:p.Prime) (po : 2<p) (e:ℕ) :
    ∃ B : ℕ, ∀ n ≥ B, Even n → SquareTimesUnit (n:ZMod (p^e)) → AtOrder (p^e) n := by
  classical
  let m := p^e
  have mp : 0 < m := pow_pos pp.pos _
  have om : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right _
  by_cases m1 : m=1
  · change ∃ B : ℕ, ∀ n ≥ B, Even n → SquareTimesUnit (n:ZMod m) → AtOrder m n
    rw [m1]
    exact ⟨0,fun _ _ _ _ => ones (Subsingleton.elim _ _)⟩
  have mh : 1 < m := by omega
  obtain ⟨U,units⟩ := prime_power_units_classification pp po e
  obtain ⟨A,fours⟩ := large_four_two_prime_powers pp pp po po e 0
  have all4 (n:ℕ) (lo:A≤n) (four:4∣n) : AtOrder m n := by
    apply at_weaker_modulus (dvd_mul_left m 4)
    simpa [m] using fours n lo four
  have cls (i:Fin m) : ∃ B : ℕ, ∀ n ≥ B, n ≡ i.val [MOD m] → Even n → SquareTimesUnit (n:ZMod m) → AtOrder m n := by
    by_cases cu : i.val.Coprime m
    · exact ⟨U,fun n hn ni en _ => atOrder_of_integral ((units n hn (coprime_of_modEq ni cu)).mpr (Or.inl en))⟩
    by_cases F : SquareTimesUnit (i.val:ZMod m)
    · let a := i.val+m-1
      have ri : i.val ≡ a+1 [MOD m] := by rw [show a+1=i.val+m by dsimp [a];omega]; simp [Nat.ModEq]
      have pi : p∣i.val := by by_contra h; exact cu ((pp.coprime_iff_not_dvd.mpr h).symm.pow_right e)
      have pm : p∣m := dvd_pow_self p (by rintro rfl; apply m1; simp [m])
      have pa : ¬p∣a := by
        intro dv
        have ds : p∣a+1 := by rw [show a+1=i.val+m by dsimp [a];omega]; exact dvd_add pi pm
        exact pp.not_dvd_one (by simpa using Nat.dvd_sub ds dv)
      obtain ⟨h,pos,H,h4,hr⟩ := seed_unit_times_square pp po mh F
      obtain ⟨V,all⟩ := composite_seed_class mh om ((pp.coprime_iff_not_dvd.mpr pa).symm.pow_right e)
        (hr.trans ri) (primeConstruction m) pos H
      refine ⟨max A V,?_⟩
      intro n hn ni en _
      by_cases four : 4∣n
      · exact all4 n ((le_max_left _ _).trans hn) four
      · have n2 : n ≡ 2 [MOD 4] := by
          have h := Nat.even_iff.mp en
          have nh := mt Nat.dvd_of_mod_eq_zero four
          change n%4=2; omega
        exact all n ((le_max_right _ _).trans hn) (n2.trans h4.symm) (ni.trans hr.symm)
    · exact ⟨0,fun n _ ni _ nw => (F ((ZMod.natCast_eq_natCast_iff _ _ _).mpr ni ▸ nw)).elim⟩
  choose bounds spec using cls
  refine ⟨Finset.univ.sup bounds,?_⟩
  intro n hn even f
  let i:Fin m := ⟨n%m,Nat.mod_lt _ mp⟩
  exact spec i n ((Finset.le_sup (f:=bounds) (Finset.mem_univ i)).trans hn) (Nat.mod_modEq n m).symm even f

#print axioms power_even_square_factor
end HadamardMod
