import Quantum.Hadamard.ArithmeticSingularCompositeConic
import Quantum.Hadamard.ComplementaryCutPrescribed

/-! The primary obstructions at twice-odd orders and global Frobenius parameters. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

/-- At each inert prime, the valuation is even whenever it falls below the
exponent in the modulus. This includes the residue zero at every factor. -/
def TwiceLocallyAdmissible (m r : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p%4=1 ∨ p^m.factorization p ∣ r ∨ Even (r.factorization p)

private theorem primary_dvd_modulus {m p : ℕ} (mp : 0 < m) (hp : p∈m.primeFactors) :
    p^m.factorization p ∣ m := by
  have dv := Finset.dvd_prod_of_mem (fun q => q^m.factorization q) hp
  exact dv.trans (dvd_of_eq (Nat.prod_primeFactors_pow_factorization mp.ne').symm)

theorem twice_admissible_of_congr {m r s : ℕ} (mp : 0 < m) (res : r ≡ s [MOD m])
    (ok : TwiceLocallyAdmissible m r) : TwiceLocallyAdmissible m s := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  let e := m.factorization p
  have pe : p^e ∣ m := primary_dvd_modulus mp hp
  rcases ok p hp with h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((res.dvd_iff pe).mp h))
  by_cases full : p^e ∣ s
  · exact Or.inr (Or.inl full)
  have nfull : ¬p^e ∣ r := fun d => full ((res.dvd_iff pe).mp d)
  have rn : r≠0 := fun eq => nfull (eq ▸ dvd_zero _)
  have sn : s≠0 := fun eq => full (eq ▸ dvd_zero _)
  have rv : r.factorization p < e := by
    by_contra! lo
    exact nfull ((pp.pow_dvd_iff_le_factorization rn).mpr lo)
  have sv : s.factorization p < e := by
    by_contra! lo
    exact full ((pp.pow_dvd_iff_le_factorization sn).mpr lo)
  have a : r.factorization p ≤ s.factorization p :=
    (pp.pow_dvd_iff_le_factorization sn).mp ((res.dvd_iff ((pow_dvd_pow p rv.le).trans pe)).mp
      ((pp.pow_dvd_iff_le_factorization rn).mpr le_rfl))
  have b : s.factorization p ≤ r.factorization p :=
    (pp.pow_dvd_iff_le_factorization rn).mp ((res.dvd_iff ((pow_dvd_pow p sv.le).trans pe)).mpr
      ((pp.pow_dvd_iff_le_factorization sn).mpr le_rfl))
  exact Or.inr (Or.inr (le_antisymm a b ▸ h))

theorem twice_necessary_at_odd_modulus {m n : ℕ} (mp : 0 < m)
    (om : (2:ℕ).Coprime m) (two : n%4=2) (H : IntegralSolution m n) :
    TwiceLocallyAdmissible m n := by
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pm := Nat.dvd_of_mem_primeFactors hp
  have pn : p≠2 := fun eq => Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2) (dvd_refl _) (eq ▸ pm) om
  by_cases split : p%4=1
  · exact Or.inl split
  right
  by_cases full : p^m.factorization p ∣ n
  · exact Or.inl full
  right
  by_contra bad
  have lo : n.factorization p < m.factorization p := by
    by_contra! rev
    exact full ((pp.pow_dvd_iff_le_factorization (by omega)).mpr rev)
  have od := Nat.odd_iff.mp (pp.odd_of_ne_two pn)
  exact no_even_singular_valuation pp (by omega) two lo (Nat.not_even_iff_odd.mp bad)
    (integer_gram (at_weaker_modulus (primary_dvd_modulus mp hp) (atOrder_of_integral H)))

/-- Combine local choices by CRT and identify a complementary-pair length
which supplies the independent factors one or two at all primary components. -/
theorem composite_frobenius_parameters {m r : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (eligible : TwiceLocallyAdmissible m r) :
    ∃ (v : ℕ) (x y : ZMod m), Odd v ∧ v.Coprime m ∧ Periodic.HasLength m v ∧
      IsUnit x ∧ (r:ZMod m) = 2*(v:ZMod m)*(x^2+1)*y^2 := by
  classical
  let I := m.primeFactors
  have localRep (p : I) : ∃ b : Bool,
      FrobeniusConic.Represents b (r:ZMod (p.val^m.factorization p.val)) := by
    have pp := Nat.prime_of_mem_primeFactors p.property
    have dv := Nat.dvd_of_mem_primeFactors p.property
    have pn : p.val≠2 := fun eq => Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2) (dvd_refl _) (eq ▸ dv) om
    exact FrobeniusConic.represents_primary pp (by have := pp.two_le; omega) _ (eligible p.val p.property)
  choose b xb yb ux equations using localRep
  let S := (Finset.univ.filter fun p : I => b p=true).image Subtype.val
  have mem (p : I) : p.val∈S ↔ b p=true := by
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q,hb,hq⟩
      exact (Subtype.ext hq : q=p) ▸ hb
    · exact fun hb => ⟨p,hb,rfl⟩
  obtain ⟨v, vo, vc, V, selections⟩ := Periodic.prescribed_switches mp om S
  have selected (p : I) :
      (v:ZMod (p.val^m.factorization p.val)) = (if b p then 2 else 1) := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (selections p.val p.property)
    by_cases flag : b p=true
    · simpa [flag,(mem p).mpr flag] using h
    · simpa [flag,mt (mem p).mp flag] using h
  let A := ZMod.equivPi m mp.ne'
  refine ⟨v, A.symm xb, A.symm yb, vo, vc, V, (Pi.isUnit_iff.mpr ux).map A.symm, ?_⟩
  apply A.injective
  simp only [map_natCast,map_mul,map_add,map_ofNat,map_pow,map_one,RingEquiv.apply_symm_apply]
  funext p
  change (r:ZMod (p.val^m.factorization p.val))=2*(v:ZMod (p.val^m.factorization p.val))*
    (xb p^2+1)*yb p^2
  rw [selected p]
  exact equations p

#print axioms twice_admissible_of_congr
#print axioms twice_necessary_at_odd_modulus
#print axioms composite_frobenius_parameters
end HadamardMod
