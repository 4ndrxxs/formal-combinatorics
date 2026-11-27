import Quantum.Hadamard.CompositeSquareNorms

theorem audited_modular_norm_progressions (m n : ℕ) (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    (∃ x : Fin (n.gcd 4) → ℕ, (∑ i, x i^2) ≡ n [MOD m]) ↔
    ∀ A : ℕ, 0 < A → ∀ N : ℕ, ∃ h > N,
      (∃ H : Matrix (Fin h) (Fin h) ℤ, (∀ i j, H i j=1 ∨ H i j= -1) ∧
       ∀ i j, (m:ℤ) ∣ (H*H.transpose) i j-(if i=j then (h:ℤ) else 0)) ∧ h ≡ n [MOD A] :=
  HadamardMod.square_norm_progressions mp om

theorem audited_modular_norm_two_primes (p q a b : ℕ) (pp : p.Prime) (qp : q.Prime)
    (po : 2<p) (qo : 2<q) :
    ∃ B : ℕ, ∀ n≥B,
      (∃ H : Matrix (Fin n) (Fin n) ℤ, (∀ i j, H i j=1 ∨ H i j= -1) ∧
       ∀ i j, ((p^a*q^b:ℕ):ℤ) ∣ (H*H.transpose) i j-(if i=j then (n:ℤ) else 0)) ↔
      ∃ x : Fin (n.gcd 4) → ℕ, (∑ i, x i^2) ≡ n [MOD p^a*q^b] :=
  HadamardMod.two_prime_powers_square_norm pp qp po qo a b

set_option pp.funBinderTypes true in
#check audited_modular_norm_progressions
#print axioms audited_modular_norm_progressions
set_option pp.funBinderTypes true in
#check audited_modular_norm_two_primes
#print axioms audited_modular_norm_two_primes
