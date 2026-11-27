import Quantum.Hadamard.Kuperberg

/-- A separate statement with only integer entries, matrix multiplication, natural
parity, and an integer congruence witness for a square. -/
theorem audited_integer_spectrum (p : ℕ) (prime : p.Prime) (odd : 2<p) :
    ∃ N : ℕ, ∀ n ≥ N,
      (∃ H : Matrix (Fin n) (Fin n) ℤ,
        (∀ i j, H i j=1 ∨ H i j= -1) ∧
        ∀ i j, (p:ℤ) ∣ (H*H.transpose) i j - (if i=j then (n:ℤ) else 0)) ↔
      Even n ∨ ∃ a : ℕ, a*a ≡ n [MOD p] := by
  letI : Fact p.Prime := ⟨prime⟩
  obtain ⟨N,hN⟩ := HadamardMod.kuperberg_integer prime odd
  refine ⟨N,fun n hn => (hN n hn).trans (or_congr_right ?_)⟩
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a.val,(ZMod.natCast_eq_natCast_iff _ _ p).mp ?_⟩
    simpa using ha.symm
  · rintro ⟨a,ha⟩
    refine ⟨(a:ZMod p),?_⟩
    simpa using ((ZMod.natCast_eq_natCast_iff _ _ p).mpr ha).symm

set_option pp.funBinderTypes true in
#check audited_integer_spectrum
#check HadamardMod.kuperberg_integer
#print HadamardMod.IntegralSolution
#print HadamardMod.Sign
#print HadamardMod.AtOrder
#print Hadamard.Arithmetic.ProductStep
#print Hadamard.Arithmetic.SquareSeed
#print Hadamard.Arithmetic.squareIncrement
#print Hadamard.Arithmetic.PrimeOrderConstruction
#print HadamardMod.KuperbergAdmissible
#print HadamardMod.TwiceOddNonsquareSeed
#check HadamardMod.ones
#check HadamardMod.Extender.grow
#check Hadamard.Arithmetic.product_steps
#check Hadamard.Arithmetic.square_steps
#check Hadamard.Arithmetic.seed_class_large
#check Hadamard.Arithmetic.eventual_of_seeds
#check HadamardMod.kuperberg_given_twice_odd_seed
#print axioms audited_integer_spectrum
#print axioms HadamardMod.kuperberg_integer
#print axioms Hadamard.Arithmetic.linear_twist
#print axioms HadamardMod.conference_nonsquare_seed
