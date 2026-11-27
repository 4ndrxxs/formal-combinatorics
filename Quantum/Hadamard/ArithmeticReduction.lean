import Quantum.Hadamard.ArithmeticNecessity
import Quantum.Hadamard.ArithmeticPowers
import Quantum.Hadamard.Asymptotic

/-! Reduction of Kuperberg's prime-modular conjecture to one seed outside
the square classes, given odd affine seeds for all nonzero squares. -/

namespace HadamardMod

open Hadamard.Arithmetic

def OddSquareSeeds (p : ℕ) : Prop :=
  ∀ a : ZMod p, a ≠ 0 →
    ∃ h > 0, AtOrder p h ∧ h ≡ 1 [MOD 4] ∧ (h : ZMod p) = a^2

def TwiceOddNonsquareSeed (p : ℕ) : Prop :=
  ∃ h > 0, AtOrder p h ∧ h ≡ 2 [MOD 4] ∧ ¬IsSquare (h : ZMod p)

theorem hasRoot_iff_isSquare {R : Type*} [Monoid R] (a : R) :
    (∃ x, x^2 = a) ↔ IsSquare a := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨x,by simpa [pow_two] using h.symm⟩
  · rintro ⟨x,h⟩
    exact ⟨x,by simpa [pow_two] using h.symm⟩

theorem nonsquare_ratio {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {a b : F} (na : ¬IsSquare a) (nb : ¬IsSquare b) :
    ∃ x : F, x ≠ 0 ∧ b*x^2 = a := by
  have a0 : a ≠ 0 := by rintro rfl; exact na ⟨0,by simp⟩
  have b0 : b ≠ 0 := by rintro rfl; exact nb ⟨0,by simp⟩
  have char : quadraticChar F (a*b) = 1 := by
    rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr na,
      quadraticChar_neg_one_iff_not_isSquare.mpr nb]
    norm_num
  obtain ⟨z,hz⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero a0 b0)).mp char
  have z0 : z ≠ 0 := by
    intro z0
    rw [z0,zero_mul] at hz
    exact (mul_ne_zero a0 b0) hz
  refine ⟨z/b, div_ne_zero z0 b0, ?_⟩
  field_simp
  linear_combination -hz

theorem square_seed_class {p n : ℕ} (hp : p.Prime) (odd : 2 < p)
    (affine : OddSquareSeeds p) (sq : IsSquare (n : ZMod p)) :
    ∃ k > 0, AtOrder p k ∧ k ≡ n [MOD 4] ∧ k ≡ n [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases zero : (n : ZMod p) = 0
  · apply zero_residue_seed hp odd
    exact (ZMod.natCast_eq_natCast_iff _ _ p).mp (by simpa using zero)
  have two : (2 : ZMod p) ≠ 0 := by
    intro e
    have d := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using e)
    exact (Nat.not_dvd_of_pos_of_lt (by decide) odd) d
  obtain ⟨a,ha⟩ := (hasRoot_iff_isSquare _).mpr sq
  have az : a ≠ 0 := by rintro rfl; simp at ha; exact zero ha.symm
  obtain ⟨h,hpos,H,h4,hm⟩ := affine (a/2) (div_ne_zero az two)
  obtain ⟨j,jpos,J,j4,jm⟩ := four_seed hp odd n
  refine ⟨j*h, Nat.mul_pos jpos hpos, at_mul J H, by simpa using j4.mul h4, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
  have jz : (j : ZMod p) = 4 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ p).mpr jm
  rw [Nat.cast_mul,jz,hm,← ha]
  field_simp
  ring

private theorem full_four_seed {p n : ℕ} (hp : p.Prime) (odd : 2 < p) (four : 4∣n) :
    ∃ k > 0, AtOrder p k ∧ k ≡ n [MOD 4] ∧ k ≡ n [MOD p] := by
  obtain ⟨B,hB⟩ := all_large_four_mod_prime hp odd
  let k := n+(4*p)*(B+1)
  have big : B < k := by dsimp [k]; nlinarith
  have d4 : 4∣k := dvd_add four (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have d : p ∣ (4*p)*(B+1) := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have zm : (4*p)*(B+1) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr d
  exact ⟨k,by omega,hB k big.le d4,(Nat.modEq_zero_iff_dvd.mpr d4).trans
    (Nat.modEq_zero_iff_dvd.mpr four).symm,by simpa [k] using zm.add_left n⟩

theorem kuperberg_of_one_nonsquare {p : ℕ} (hp : p.Prime) (odd : 2 < p)
    (affine : OddSquareSeeds p) (oneNonsquare : TwiceOddNonsquareSeed p) :
    ∃ B, ∀ n ≥ B, AtOrder p n ↔ KuperbergAdmissible p n := by
  let : Fact p.Prime := ⟨hp⟩
  have seeds (n : ℕ) (ha : KuperbergAdmissible p n) :
      ∃ k > 0, AtOrder p k ∧ k ≡ n [MOD 4] ∧ k ≡ n [MOD p] := by
    by_cases sq : IsSquare (n : ZMod p)
    · exact square_seed_class hp odd affine sq
    by_cases four : 4∣n
    · exact full_four_seed hp odd four
    have even : n%2=0 := ha.resolve_right (fun h => sq ((hasRoot_iff_isSquare _).mp h))
    have class2 : (2 : ℕ) ≡ n [MOD 4] := by change 2%4=n%4; omega
    obtain ⟨k,kpos,K,k4,kn⟩ := oneNonsquare
    obtain ⟨a,az,ratio⟩ := nonsquare_ratio sq kn
    obtain ⟨h,hpos,H,h4,hm⟩ := affine a az
    refine ⟨k*h, Nat.mul_pos kpos hpos, at_mul K H, ?_, ?_⟩
    · exact (by simpa using k4.mul h4 : k*h ≡ 2 [MOD 4]).trans class2
    · apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
      simpa [hm] using ratio
  obtain ⟨B,hB⟩ := eventual_of_seeds hp odd (primeConstruction p) seeds
  exact ⟨B,fun n hn => ⟨necessary_admissible hp, hB n hn⟩⟩

theorem two_nonsquare_seed {p : ℕ} (ns : ¬IsSquare (2 : ZMod p)) : TwiceOddNonsquareSeed p :=
  ⟨2,by decide,order_two p,Nat.ModEq.refl _,by simpa using ns⟩

end HadamardMod
