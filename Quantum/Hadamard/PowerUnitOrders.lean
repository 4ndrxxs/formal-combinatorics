import Quantum.Hadamard.PowerConference
import Quantum.Hadamard.ArithmeticUnitClassification
import Quantum.Hadamard.ArithmeticComposite

/-! The eventual classification of all unit orders at every odd prime-power modulus. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.Arithmetic.PowerResidues Finset

private theorem mixed_seed_progression {p a r : ℕ} [Fact p.Prime] (po : 2<p)
    (cr : r.Coprime (p^(a+1))) (ns : ¬ IsSquare (r : ZMod (p^(a+1))))
    {h : ℕ} (hp : 0<h) (H : AtOrder (p^(a+1)) h) (h4 : h ≡ 2 [MOD 4])
    (hn : ¬ IsSquare (h : ZMod p)) :
    ∃ B, ∀ n ≥ B, n ≡ 2 [MOD 4] → n ≡ r [MOD p^(a+1)] → AtOrder (p^(a+1)) n := by
  let m := p^(a+1)
  have pp : p.Prime := Fact.out
  have mp : 1 < m := lt_of_lt_of_le pp.one_lt (Nat.le_self_pow (Nat.succ_ne_zero _) _)
  have odd : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right _
  letI : NeZero m := ⟨by omega⟩
  have hu : IsUnit (h:ZMod m) := by
    apply unit_of_red (p:=p) (a:=a)
    intro z
    apply hn
    have zero : (h:ZMod p)=0 := by simpa only [map_natCast] using z
    simp [zero]
  have hns : ¬ IsSquare (h:ZMod m) := by
    rintro ⟨x,eq⟩
    exact hn ⟨red p a x,by simpa only [map_natCast,map_mul] using congrArg (red p a) eq⟩
  have ru : IsUnit (r:ZMod m) := (ZMod.isUnit_iff_coprime _ _).mpr cr
  obtain ⟨z,zu,eq⟩ := nonsquare_ratio_unit (p:=p) (a:=a) po ru hu ns hns
  obtain ⟨U,hU⟩ := all_large_unit_squares (by omega : 0 < m) odd
  obtain ⟨Q,big,prime,Qz,Q4⟩ := realize_unit_prime (by omega : 0 < m) odd zu 1 (by decide) U
  have cq : Q.Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (Qz ▸ zu)
  have Qsq : AtOrder m (Q^2) := hU _ (by nlinarith [prime.pos]) (cq.pow_left _)
    (by exact ⟨(Q:ZMod m),by push_cast; ring⟩)
  have s := at_mul H Qsq
  have sr : h*Q^2 ≡ r [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
    push_cast
    rw [Qz]
    exact eq)
  have s4 : h*Q^2 ≡ 2 [MOD 4] := by simpa using h4.mul (Q4.pow 2)
  let t := (r:ZMod m)-1
  have tu : IsUnit t := by
    apply unit_of_red (p:=p) (a:=a)
    intro zero
    have one : red p a (r:ZMod m)=1 := by
      apply sub_eq_zero.mp
      simpa only [t,map_sub,map_one] using zero
    exact ns (square_of_red (p:=p) (a:=a) po ru (by simp [one]))
  have tc : t.val.Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using tu)
  have tr : h*Q^2 ≡ t.val+1 [MOD m] := by
    apply sr.trans
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp [t]
  obtain ⟨B,hB⟩ := composite_seed_class mp odd tc tr (primeConstruction m)
    (Nat.mul_pos hp (pow_pos prime.pos _)) s
  exact ⟨B,fun n bn n4 nr => hB n bn (n4.trans s4.symm) (nr.trans sr.symm)⟩

private theorem power_unit_given_seed {p a : ℕ} [Fact p.Prime] (po : 2<p)
    (seed : ∃ h>0, AtOrder (p^(a+1)) h ∧ h ≡ 2 [MOD 4] ∧ ¬IsSquare (h:ZMod p)) :
    ∃ B : ℕ, ∀ n ≥ B, n.Coprime (p^(a+1)) →
      (IntegralSolution (p^(a+1)) n ↔ Even n ∨ IsSquare (n:ZMod (p^(a+1)))) := by
  classical
  let m := p^(a+1)
  have pp : p.Prime := Fact.out
  have mp : 1 < m := lt_of_lt_of_le pp.one_lt (Nat.le_self_pow (Nat.succ_ne_zero _) _)
  have odd : (2:ℕ).Coprime m := (two_coprime_prime pp po).pow_right _
  obtain ⟨h,hp,H,h4,hn⟩ := seed
  have cls (i:Fin m) : ∃ B : ℕ, ∀ n ≥ B, Even n → n.Coprime m → ¬IsSquare (n:ZMod m) →
      n ≡ i.val [MOD m] → AtOrder m n := by
    by_cases c : i.val.Coprime m ∧ ¬IsSquare (i.val:ZMod m)
    · obtain ⟨A,hA⟩ := four_orders_at_unit mp odd c.1
      obtain ⟨B,hB⟩ := mixed_seed_progression po c.1 c.2 hp H h4 hn
      refine ⟨max A B,?_⟩
      intro n bound ev _ _ res
      by_cases four : 4∣n
      · exact hA n ((le_max_left _ _).trans bound) four res
      · have e := Nat.even_iff.mp ev
        exact hB n ((le_max_right _ _).trans bound) (show n%4=2%4 by omega) res
    · refine ⟨0,?_⟩
      intro n _ _ cn ns res
      have cast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr res
      exact (c ⟨coprime_of_modEq res.symm cn,fun sq => ns (cast ▸ sq)⟩).elim
  choose B hb using cls
  obtain ⟨U,hU⟩ := all_large_unit_squares (by omega : 0 < m) odd
  refine ⟨max U (univ.sup B),?_⟩
  intro n bound cn
  refine ⟨fun H => ?_,?_⟩
  · by_cases e : Even n
    · exact Or.inl e
    · exact Or.inr (odd_unit_necessary cn (Nat.not_even_iff_odd.mp e) (atOrder_of_integral H))
  · intro a
    by_cases sq : IsSquare (n:ZMod m)
    · exact integer_gram (hU n ((le_max_left _ _).trans bound) cn sq)
    · let i : Fin m := ⟨n%m,Nat.mod_lt _ (by omega)⟩
      exact integer_gram (hb i n ((le_sup (mem_univ i)).trans ((le_max_right _ _).trans bound))
        (a.resolve_right sq) cn sq (Nat.mod_modEq n m).symm)

theorem prime_power_units_classification {p : ℕ} (prime : p.Prime) (po : 2<p) (e : ℕ) :
    ∃ B : ℕ, ∀ n ≥ B, n.Coprime (p^e) →
      (IntegralSolution (p^e) n ↔ Even n ∨ IsSquare (n:ZMod (p^e))) := by
  letI : Fact p.Prime := ⟨prime⟩
  obtain _|a := e
  · rw [pow_zero]
    exact (three_mod_four_units_classification (m:=1) (by decide) (by decide)
      (by intro q qp d; have := Nat.dvd_one.mp d; have := qp.two_le; omega))
  rcases prime_residue_bridge po with eight|three|two
  · exact power_unit_given_seed po (power_nonsquare_seed a eight)
  · apply three_mod_four_units_classification (pow_pos prime.pos _) ((two_coprime_prime prime po).pow_right _)
    intro q qp d
    have eq := (Nat.prime_dvd_prime_iff_eq qp prime).mp (qp.dvd_of_dvd_pow d)
    simpa [eq] using three
  · exact power_unit_given_seed po ⟨2,by decide,order_two _,Nat.ModEq.refl _,by simpa using two⟩

#print axioms prime_power_units_classification
end HadamardMod


