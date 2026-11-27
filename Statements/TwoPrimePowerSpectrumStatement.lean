import Quantum.Hadamard.CompositeConductorSpectrum

private theorem explicit_conditions (m n : ℕ) (mp : 0 < m) :
    HadamardMod.CompositeAdmissible m n ↔
    4 ∣ n ∨ (n%4=2 ∧ ∀ p ∈ m.primeFactors, p%4=1 ∨ p^m.factorization p∣n ∨
        ∃ k u : ℕ, n=p^(2*k)*u ∧ ¬p∣u) ∨ (Odd n ∧ ∃ x : ℕ, x^2 ≡ n [MOD m]) := by
  have sqr : IsSquare (n:ZMod m) ↔ ∃ x:ℕ, x^2 ≡ n [MOD m] := by
    let : NeZero m := ⟨mp.ne'⟩
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨x.val,(ZMod.natCast_eq_natCast_iff _ _ _).mp (by simp [pow_two,hx])⟩
    · rintro ⟨x,hx⟩
      exact ⟨(x:ZMod m),by simpa [pow_two] using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hx).symm⟩
  unfold HadamardMod.CompositeAdmissible HadamardMod.TwiceLocallyAdmissible
  rw [sqr]
  by_cases nz : n=0
  · simp [nz]
  have val (p : ℕ) (hp : p∈m.primeFactors) :
      Even (n.factorization p) ↔ ∃ k u:ℕ, n=p^(2*k)*u ∧ ¬p∣u := by
    have pp := Nat.prime_of_mem_primeFactors hp
    constructor
    · rintro ⟨k,hk⟩
      let u := n/p^(n.factorization p)
      have eq : n=p^(n.factorization p)*u := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      exact ⟨k,u,by simpa [hk,two_mul] using eq,
        pp.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl pp nz)⟩
    · rintro ⟨k,u,eq,pu⟩
      have uz : u≠0 := fun h => pu (h ▸ dvd_zero p)
      have f := DFunLike.congr_fun (Nat.factorization_mul (pow_ne_zero (2*k) pp.ne_zero) uz) p
      rw [←eq] at f
      have zero := Nat.factorization_eq_zero_of_not_dvd pu
      have primePow : (p^(2*k)).factorization p=2*k := by simp [pp.factorization_pow]
      have v : n.factorization p=2*k := by simpa only [Finsupp.add_apply,primePow,zero,add_zero] using f
      exact ⟨k,by omega⟩
  exact or_congr Iff.rfl (or_congr (and_congr_right fun _ =>
      forall_congr' fun p => forall_congr' fun hp =>
        or_congr Iff.rfl (or_congr Iff.rfl (val p hp))) Iff.rfl)

/-- The eventual order of the integer sign matrix is the same n at which
the right-hand criterion is tested. Both prime bases and both exponents vary. -/
theorem audited_two_prime_power_orders (p q a b : ℕ) (pp : p.Prime) (qp : q.Prime)
    (po : 2<p) (qo : 2<q) :
    ∃ B : ℕ, ∀ n ≥ B,
      (∃ H : Matrix (Fin n) (Fin n) ℤ, (∀ i j, H i j=1 ∨ H i j= -1) ∧
       ∀ i j, ((p^a*q^b:ℕ):ℤ) ∣ (H*H.transpose) i j-(if i=j then (n:ℤ) else 0)) ↔
      4∣n ∨ (n%4=2 ∧ ∀ l ∈ (p^a*q^b).primeFactors,
        l%4=1 ∨ l^(p^a*q^b).factorization l∣n ∨ ∃ k u:ℕ, n=l^(2*k)*u ∧ ¬l∣u) ∨
      (Odd n ∧ ∃ x:ℕ, x^2 ≡ n [MOD p^a*q^b]) := by
  obtain ⟨B,h⟩ := HadamardMod.two_prime_power_spectrum pp qp po qo a b
  exact ⟨B,fun n hn => (h n hn).trans (explicit_conditions _ n (Nat.mul_pos (pow_pos pp.pos a) (pow_pos qp.pos b)))⟩

/-- At an arbitrary odd modulus, the independent statement asks separately
for an unbounded witness in every arithmetic progression. -/
theorem audited_odd_modulus_progressions (m n : ℕ) (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    (4∣n ∨ (n%4=2 ∧ ∀ p ∈ m.primeFactors,
      p%4=1 ∨ p^m.factorization p∣n ∨ ∃ k u:ℕ, n=p^(2*k)*u ∧ ¬p∣u) ∨
      (Odd n ∧ ∃ x:ℕ, x^2 ≡ n [MOD m])) ↔
    ∀ A : ℕ, 0 < A → ∀ N : ℕ, ∃ h > N,
      (∃ H : Matrix (Fin h) (Fin h) ℤ, (∀ i j, H i j=1 ∨ H i j= -1) ∧
       ∀ i j, (m:ℤ) ∣ (H*H.transpose) i j-(if i=j then (h:ℤ) else 0)) ∧ h ≡ n [MOD A] := by
  exact (explicit_conditions m n mp).symm.trans (HadamardMod.composite_progression_spectrum mp om)

set_option pp.funBinderTypes true in
#check audited_two_prime_power_orders
#print axioms audited_two_prime_power_orders
set_option pp.funBinderTypes true in
#check audited_odd_modulus_progressions
#print axioms audited_odd_modulus_progressions
#print axioms HadamardMod.odd_modulus_spectrum_at_three_centers
