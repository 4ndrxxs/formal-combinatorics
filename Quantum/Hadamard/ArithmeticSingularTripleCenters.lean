import Quantum.Hadamard.ThreeCenterConductor

/-! Dividing the order by two or four produces a unit center whenever
the odd modulus has at most three distinct prime factors. -/
namespace HadamardMod.TripleRouting

private theorem hit {m n c : ℕ} (mp : 0 < m) (cn : c≤n)
    (nc : ¬IsUnit ((n:ZMod m)-(c:ZMod m))) :
    ∃ p∈m.primeFactors, n ≡ c [MOD p] := by
  have bad : ¬(n-c).Coprime m := by
    intro cu
    apply nc
    simpa only [Nat.cast_sub cn] using (ZMod.isUnit_iff_coprime _ _).mpr cu
  obtain ⟨p,pp,d,pm⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  exact ⟨p,Nat.mem_primeFactors.mpr ⟨pp,pm,mp.ne'⟩,((Nat.modEq_iff_dvd' cn).mpr d).symm⟩

private theorem failed {m n : ℕ} (mp : 0 < m) (lo : 2≤n) (bad : ¬ThreeUnitCenters m n) :
    (∃ p∈m.primeFactors, n ≡ 0 [MOD p]) ∧ (∃ p∈m.primeFactors, n ≡ 1 [MOD p]) ∧
    (∃ p∈m.primeFactors, n ≡ 2 [MOD p]) := by
  refine ⟨hit mp (Nat.zero_le _) ?_,hit mp (by omega) ?_,hit mp lo ?_⟩
  · exact fun unit => bad (Or.inl (by simpa using unit))
  · exact fun unit => bad (Or.inr (Or.inl (by simpa using unit)))
  · exact fun unit => bad (Or.inr (Or.inr (by simpa using unit)))

private theorem no_two_power {m p : ℕ} (om : (2:ℕ).Coprime m) (hp : p∈m.primeFactors) (k : ℕ) :
    ¬p∣2^k := by
  have pM := Nat.dvd_of_mem_primeFactors hp
  have good := (om.of_dvd_right pM).pow_left k
  exact fun d => Nat.not_coprime_of_dvd_of_dvd (Nat.prime_of_mem_primeFactors hp).one_lt d (dvd_refl p) good

private theorem different {p q n r s : ℕ} (rs : r ≤ s)
    (rp : n ≡ r [MOD p]) (sq : n ≡ s [MOD q]) (d : ¬p∣s-r) : p≠q := by
  rintro rfl
  exact d ((Nat.modEq_iff_dvd' rs).mp (rp.symm.trans sq))

private theorem all_three {m z x y : ℕ} (small : m.primeFactors.card≤3)
    (mz : z∈m.primeFactors) (mx : x∈m.primeFactors) (my : y∈m.primeFactors)
    (zx : z≠x) (zy : z≠y) (xy : x≠y) {q : ℕ} (hq : q∈m.primeFactors) :
    q=z ∨ q=x ∨ q=y := by
  by_contra! bad
  obtain ⟨qz,qx,qy⟩ := bad
  have sub : ({q,z,x,y}:Finset ℕ)⊆m.primeFactors := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> assumption
  have size := Finset.card_le_card sub
  have four : ({q,z,x,y}:Finset ℕ).card=4 := by simp [qz,qx,qy,zx,zy,xy]
  omega

/-- A modulus supported on at most three odd primes cannot meet all five
translated classes 0, 1, 2, 4, 8 in nonunits. When it has no factor three,
the first four translated classes already suffice. -/
private theorem obstruction {m n z x y w : ℕ} (om : (2:ℕ).Coprime m) (small : m.primeFactors.card≤3)
    (mz : z∈m.primeFactors) (mx : x∈m.primeFactors) (my : y∈m.primeFactors) (mw : w∈m.primeFactors)
    (rz : n ≡ 0 [MOD z]) (rx : n ≡ 1 [MOD x]) (ry : n ≡ 2 [MOD y]) (rw : n ≡ 4 [MOD w]) :
    x=3 ∧ ∀ q∈m.primeFactors, ¬n ≡ 8 [MOD q] := by
  have zx : z≠x := different (by decide) rz rx (no_two_power om mz 0)
  have zy : z≠y := different (by decide) rz ry (no_two_power om mz 1)
  have xy : x≠y := different (by decide) rx ry (no_two_power om mx 0)
  have zw : z≠w := different (by decide) rz rw (no_two_power om mz 2)
  have yw : y≠w := different (by decide) ry rw (no_two_power om my 1)
  have wx : w=x := by rcases all_three small mz mx my zx zy xy mw with h|h|h <;> omega
  subst w
  have dx : x∣3 := (Nat.modEq_iff_dvd' (by decide : 1≤4)).mp (rx.symm.trans rw)
  have x3 : x=3 := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors mx) (by decide)).mp dx
  refine ⟨x3,?_⟩
  intro q mq rq
  have zq : z≠q := different (by decide) rz rq (no_two_power om mz 3)
  have xq : x≠q := different (by decide) rw rq (no_two_power om mx 2)
  have qy : q=y := by rcases all_three small mz mx my zx zy xy mq with h|h|h <;> omega
  subst q
  have dy : y∣6 := (Nat.modEq_iff_dvd' (by decide : 2≤8)).mp (ry.symm.trans rq)
  have yp := Nat.prime_of_mem_primeFactors my
  rcases yp.dvd_mul.mp (show y∣2*3 from dy) with d|d
  · exact no_two_power om my 1 d
  · exact xy (x3.trans ((Nat.prime_dvd_prime_iff_eq yp (by decide)).mp d).symm)

theorem centers_after_two_halvings {m u : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (lo : 2≤u) :
    ThreeUnitCenters m (4*u) ∨ ThreeUnitCenters m (2*u) ∨ ThreeUnitCenters m u := by
  by_contra! bad
  obtain ⟨⟨z,mz,rz⟩,⟨x,mx,rx⟩,⟨y,my,ry⟩⟩ := failed mp (by omega) bad.1
  obtain ⟨w,mw,rw⟩ := (failed mp (by omega) bad.2.1).2.2
  obtain ⟨q,mq,rq⟩ := (failed mp lo bad.2.2).2.2
  have four : 4*u ≡ 4 [MOD w] := by
    simpa only [←mul_assoc,show (2:ℕ)*2=4 by decide] using rw.mul_left 2
  exact (obstruction om small mz mx my mw rz rx ry four).2 q mq (by simpa using rq.mul_left 4)

theorem centers_after_one_halving {m u : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (small : m.primeFactors.card≤3) (no3 : ¬3∣m) (lo : 2≤u) :
    ThreeUnitCenters m (2*u) ∨ ThreeUnitCenters m u := by
  by_contra! bad
  obtain ⟨⟨z,mz,rz⟩,⟨x,mx,rx⟩,⟨y,my,ry⟩⟩ := failed mp (by omega) bad.1
  obtain ⟨w,mw,rw⟩ := (failed mp lo bad.2).2.2
  have four : 2*u ≡ 4 [MOD w] := by simpa using rw.mul_left 2
  have x3 := (obstruction om small mz mx my mw rz rx ry four).1
  exact no3 (x3 ▸ Nat.dvd_of_mem_primeFactors mx)

#print axioms centers_after_two_halvings
#print axioms centers_after_one_halving
end HadamardMod.TripleRouting
