import Quantum.Hadamard.ArithmeticSingularCompositeCRT
import Quantum.Hadamard.ArithmeticCoprimeSelectors

/-! A large auxiliary matrix can absorb saturated valuations in an arbitrary
set of primary factors, while retaining the value four in the complement. -/
noncomputable section
namespace HadamardMod.FrobeniusConic
open Hadamard.Arithmetic Finset

theorem primary_congruences {m : ℕ} (_mp : 0 < m) (g : ℕ → ℕ) :
    ∃ n : ℕ, ∀ p ∈ m.primeFactors, n ≡ g p [MOD p^m.factorization p] := by
  let d (p:ℕ) := p^m.factorization p
  have cop : Set.Pairwise (↑m.primeFactors : Set ℕ) (fun p q => (d p).Coprime (d q)) := by
    intro p hp q hq ne
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr ne).pow_left _ |>.pow_right _
  obtain ⟨n,h⟩ := Nat.chineseRemainderOfFinset g d m.primeFactors
    (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero) cop
  exact ⟨n,h⟩

theorem congr_of_all_primary {m x y : ℕ} (mp : 0 < m)
    (h : ∀ p ∈ m.primeFactors, x ≡ y [MOD p^m.factorization p]) : x ≡ y [MOD m] := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  apply (ZMod.equivPi m mp.ne').injective
  rw [map_natCast,map_natCast]
  funext p
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h p.val p.property)

theorem primary_transport {p e r s : ℕ} (pp : p.Prime) (res : r ≡ s [MOD p^e])
    (eligible : p%4=1 ∨ p^e∣r ∨ Even (r.factorization p)) :
    p%4=1 ∨ p^e∣s ∨ Even (s.factorization p) := by
  by_cases en : e=0
  · simp [en]
  have mem : p∈(p^e).primeFactors := Nat.mem_primeFactors.mpr
    ⟨pp, dvd_pow_self p en, pow_ne_zero _ pp.ne_zero⟩
  have ok : TwiceLocallyAdmissible (p^e) r := by
    intro q hq
    have eq : q=p := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) pp).mp
      ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))
    subst q
    simpa [pp.factorization_pow] using eligible
  simpa [pp.factorization_pow] using (twice_admissible_of_congr (pow_pos pp.pos _) res ok p mem)

theorem saturated_multiplier {m r : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    ∃ N : ℕ, ∀ j ≥ N, (∀ p ∈ m.primeFactors,
      j ≡ (if p^m.factorization p∣r then 0 else 4) [MOD p^m.factorization p]) →
      AtOrder m j := by
  classical
  let d (p:ℕ) := p^m.factorization p
  let L := m.primeFactors.filter fun p => d p∣r
  let R := m.primeFactors.filter fun p => ¬d p∣r
  let A := ∏ p ∈ L, d p
  let B := ∏ p ∈ R, d p
  have prod : A*B=m := (Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => d p∣r) d).trans
    (Nat.prod_primeFactors_pow_factorization mp.ne').symm
  have mass : 0<A*B := prod ▸ mp
  have ap := Nat.pos_of_mul_pos_right mass
  have bp := Nat.pos_of_mul_pos_left mass
  have left : ∀ p∈L, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have right : ∀ p∈R, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have cop : A.Coprime B := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    have ne : p≠q := fun eq => (Finset.mem_filter.mp hq).2 (eq ▸ (Finset.mem_filter.mp hp).2)
    exact ((Nat.coprime_primes (left _ hp) (right _ hq)).mpr ne).pow_left _ |>.pow_right _
  have gather {F:Finset ℕ} (allPrime : ∀ p∈F,p.Prime) {y:ℕ} (h : ∀ p∈F,d p∣y) :
      (∏ p∈F,d p)∣y := by
    rw [←Finset.lcm_eq_prod (s:=F) (f:=d) (by
      intro p hp q hq ne
      exact ((Nat.coprime_primes (allPrime _ hp) (allPrime _ hq)).mpr ne).pow_left _ |>.pow_right _)]
    exact Finset.lcm_dvd h
  have base : ∃ N : ℕ, ∀ j≥N, A∣j → j ≡ 4 [MOD B] → AtOrder m j := by
    by_cases a1 : A=1
    · have eq : B=m := by simpa [a1] using prod
      exact ⟨0, fun j _ _ h => offdiag_four (by
        simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_natCast_iff j 4 m).mpr (eq ▸ h))⟩
    obtain ⟨N,H⟩ := all_large_coprime_zero_four (by omega : 1<A)
      (om.of_dvd_right (prod ▸ dvd_mul_right A B)) bp
      (om.of_dvd_right (prod ▸ dvd_mul_left B A)) cop
    exact ⟨N,fun j h a b => prod ▸ H j h a b⟩
  obtain ⟨N,H⟩ := base
  refine ⟨max 4 N,?_⟩
  intro j hj hjp
  apply H j (by omega)
  · apply gather left
    intro p hp
    obtain ⟨hm,div⟩ := Finset.mem_filter.mp hp
    exact Nat.modEq_zero_iff_dvd.mp (by simpa [d,div] using hjp p hm)
  · apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (by omega : 4≤j)).mpr
    apply gather right
    intro p hp
    obtain ⟨hm,nd⟩ := Finset.mem_filter.mp hp
    have localcon : j ≡ 4 [MOD d p] := by
      change ¬p^m.factorization p∣r at nd
      simpa [d,nd] using hjp p hm
    exact (Nat.modEq_iff_dvd' (by omega : 4≤j)).mp localcon.symm

#print axioms saturated_multiplier
end HadamardMod.FrobeniusConic
