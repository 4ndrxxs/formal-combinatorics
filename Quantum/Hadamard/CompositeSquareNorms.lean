import Quantum.Hadamard.CompositeConductorSpectrum
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.SumFourSquares

/-! An elementary norm criterion equivalent to the local valuation
conditions. At a fixed order the required number of squares is gcd(n,4). -/
noncomputable section
namespace HadamardMod

private theorem norm_from_conic {R : Type*} [CommRing R] {r : R}
    {s : Bool} (rep : FrobeniusConic.Represents s r) : ∃ u v:R, u^2+v^2=r := by
  obtain ⟨x,y,_,eq⟩ := rep
  cases s with
  | false => exact ⟨(x+1)*y,(x-1)*y,by rw [eq]; simp only [Bool.false_eq_true,ite_false]; ring⟩
  | true => exact ⟨2*x*y,2*y,by rw [eq]; simp only [ite_true]; ring⟩

theorem twice_iff_sum_two_squares {m n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    TwiceLocallyAdmissible m n ↔ ∃ x y : ℕ, x^2+y^2 ≡ n [MOD m] := by
  constructor
  · intro localOk
    let I := m.primeFactors
    have loc (p : I) : ∃ x y : ZMod (p.val^m.factorization p.val),
        x^2+y^2=(n:ZMod (p.val^m.factorization p.val)) := by
      have pp := Nat.prime_of_mem_primeFactors p.property
      have dv := Nat.dvd_of_mem_primeFactors p.property
      have pn : p.val≠2 := fun e => Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2)
        (dvd_refl _) (e ▸ dv) om
      obtain ⟨s,hs⟩ := FrobeniusConic.represents_primary pp (by have := pp.two_le; omega) _ (localOk _ p.property)
      exact norm_from_conic hs
    choose u v eq using loc
    let E := ZMod.equivPi m mp.ne'
    let x := E.symm u
    let y := E.symm v
    have h : x^2+y^2=(n:ZMod m) := by
      apply E.injective
      simp only [x,y,map_add,map_pow,map_natCast,RingEquiv.apply_symm_apply]
      exact funext eq
    let : NeZero m := ⟨mp.ne'⟩
    refine ⟨x.val,y.val,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
    simpa only [Nat.cast_add,Nat.cast_pow,ZMod.natCast_zmod_val] using h
  · rintro ⟨x,y,h⟩
    let s := x^2+y^2
    refine twice_admissible_of_congr mp h ?_
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    have pn : p≠2 := fun e => Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2) (dvd_refl _)
      (e ▸ Nat.dvd_of_mem_primeFactors hp) om
    by_cases split : p%4=1
    · exact Or.inl split
    by_cases zero : s=0
    · right; left
      change p^m.factorization p ∣ s
      rw [zero]
      exact dvd_zero _
    right; right
    change Even (s.factorization p)
    by_cases dv : p∣s
    · have p4 : p%4=3 := by have := Nat.odd_iff.mp (pp.odd_of_ne_two pn); omega
      have ev := Nat.eq_sq_add_sq_iff.mp (show ∃ a b : ℕ, s=a^2+b^2 from ⟨x,y,rfl⟩)
        p (Nat.mem_primeFactors.mpr ⟨pp,dv,zero⟩) p4
      simpa [Nat.factorization_def _ pp,Nat.padicValNat_def] using ev
    · simp [Nat.factorization_eq_zero_of_not_dvd dv]

/-- A congruence involving only ordinary squares of natural numbers. -/
def SquareNorm (m n : ℕ) : Prop :=
  ∃ x : Fin (n.gcd 4) → ℕ, (∑ i, x i^2) ≡ n [MOD m]

theorem composite_iff_square_norm {m n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    CompositeAdmissible m n ↔ SquareNorm m n := by
  unfold SquareNorm CompositeAdmissible
  have gc : n.gcd 4 = (n%4).gcd 4 := by rw [Nat.gcd_comm n 4, Nat.gcd_rec 4 n]
  have b : n%4<4 := Nat.mod_lt _ (by decide)
  rcases (show n%4=0 ∨ n%4=2 ∨ n%4=1 ∨ n%4=3 by omega) with h|h|odd
  · have four := Nat.dvd_of_mod_eq_zero h
    have g : n.gcd 4=4 := by rw [gc,h]; decide
    rw [g]
    constructor
    · intro _
      obtain ⟨a,b,c,d,eq⟩ := Nat.sum_four_squares n
      refine ⟨![a,b,c,d],?_⟩
      simpa [Fin.sum_univ_succ,add_assoc] using (show a^2+b^2+c^2+d^2 ≡ n [MOD m] by rw [eq])
    · exact fun _ => Or.inl four
  · have g : n.gcd 4=2 := by rw [gc,h]; decide
    have nf : ¬4∣n := fun d => by have := Nat.mod_eq_zero_of_dvd d; omega
    have no : ¬Odd n := fun o => by have := Nat.odd_iff.mp o; omega
    rw [g]
    simp only [nf,no,h,true_and,false_and,or_false,false_or]
    rw [twice_iff_sum_two_squares mp om]
    constructor
    · rintro ⟨x,y,eq⟩
      exact ⟨![x,y],by simpa [Fin.sum_univ_two] using eq⟩
    · rintro ⟨x,eq⟩
      exact ⟨x 0,x 1,by simpa [Fin.sum_univ_two] using eq⟩
  · have o : Odd n := Nat.odd_iff.mpr (by omega)
    have g : n.gcd 4=1 := by rcases odd with h|h <;> rw [gc,h] <;> decide
    have nf : ¬4∣n := fun d => by have := Nat.mod_eq_zero_of_dvd d; omega
    have nt : ¬n%4=2 := by omega
    rw [g]
    simp only [nf,nt,o,true_and,false_and,false_or]
    let : NeZero m := ⟨mp.ne'⟩
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨fun _ => x.val,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
      simp [pow_two,hx]
    · rintro ⟨x,eq⟩
      have h : x 0 ^ 2 ≡ n [MOD m] := by simpa using eq
      exact ⟨(x 0:ZMod m),by simpa [pow_two] using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h).symm⟩

theorem square_norm_progressions {m n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m) :
    SquareNorm m n ↔ ∀ A : ℕ, 0 < A → ∀ N : ℕ, ∃ h>N, IntegralSolution m h ∧ h ≡ n [MOD A] :=
  (composite_iff_square_norm mp om).symm.trans (composite_progression_spectrum mp om)

theorem two_prime_powers_square_norm {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (po : 2<p) (qo : 2<q) (a b : ℕ) :
    ∃ B : ℕ, ∀ n≥B, IntegralSolution (p^a*q^b) n ↔ SquareNorm (p^a*q^b) n := by
  have pos := Nat.mul_pos (pow_pos pp.pos a) (pow_pos qp.pos b)
  have odd := ((Hadamard.Arithmetic.two_coprime_prime pp po).pow_right a).mul_right
    ((Hadamard.Arithmetic.two_coprime_prime qp qo).pow_right b)
  obtain ⟨B,h⟩ := two_prime_power_spectrum pp qp po qo a b
  exact ⟨B,fun n hn => (h n hn).trans (composite_iff_square_norm pos odd)⟩

#print axioms twice_iff_sum_two_squares
#print axioms composite_iff_square_norm
#print axioms square_norm_progressions
#print axioms two_prime_powers_square_norm
end HadamardMod
