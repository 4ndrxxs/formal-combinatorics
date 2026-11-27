import Quantum.Hadamard.ArithmeticCompositeSteps
import Quantum.Hadamard.CompositeUnits

/-! Every sufficiently large multiple of four is a modular Hadamard
order at four times any product of two arbitrary odd prime powers. -/
namespace HadamardMod
open Hadamard.Arithmetic

theorem three_unit_class {b w : ℕ} (bp : 0 < b) (odd : (2:ℕ).Coprime b) (wp : 0 < w)
    (cond : w.Coprime b ∨ (4*w-1).Coprime b ∨ (2*w-1).Coprime b) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ 4*w [MOD 4*b] → AtOrder (4*b) n := by
  by_cases hb : b=1
  · subst b
    exact unit_four_large bp odd (by simp)
  rcases cond with H|H|H
  · exact unit_four_large bp odd H
  · exact lex_unit_class bp odd wp H
  · exact brouwer_unit_class (by omega) odd wp H

private theorem conflicting {p x y k:ℕ} (pp : p.Prime) (rel : y+1=k*x) (px:p∣x) (py:p∣y) :
    False := by
  have pk : p∣k*x := px.trans (dvd_mul_left x k)
  rw [←rel] at pk
  exact pp.not_dvd_one (by simpa using Nat.dvd_sub pk py)

theorem units_at_two_powers {p q:ℕ} (pp:p.Prime) (pq:q.Prime) (a d :ℕ) {w:ℕ} (wp:0<w) :
    w.Coprime (p^a*q^d) ∨ (4*w-1).Coprime (p^a*q^d) ∨ (2*w-1).Coprime (p^a*q^d) := by
  classical
  have bad (z:ℕ) (notC : ¬z.Coprime (p^a*q^d)) : p∣z ∨ q∣z := by
    by_contra! nh
    exact notC (((pp.coprime_iff_not_dvd.mpr nh.1).symm.pow_right a).mul_right
      ((pq.coprime_iff_not_dvd.mpr nh.2).symm.pow_right d))
  by_contra! H
  rcases bad _ H.1 with p0|q0 <;> rcases bad _ H.2.1 with p1|q1 <;> rcases bad _ H.2.2 with p2|q2
  all_goals first
    | exact conflicting pp (show (4*w-1)+1=4*w by omega) p0 p1
    | exact conflicting pq (show (4*w-1)+1=4*w by omega) q0 q1
    | exact conflicting pp (show (2*w-1)+1=2*w by omega) p0 p2
    | exact conflicting pq (show (2*w-1)+1=2*w by omega) q0 q2
    | exact conflicting pp (show 2*(2*w-1)+1=1*(4*w-1) by omega) p1 (p2.trans (dvd_mul_left _ _))
    | exact conflicting pq (show 2*(2*w-1)+1=1*(4*w-1) by omega) q1 (q2.trans (dvd_mul_left _ _))

theorem large_four_of_units {b : ℕ} (bp : 0 < b) (odd : (2:ℕ).Coprime b)
    (all : ∀ w, 0 < w → w.Coprime b ∨ (4*w-1).Coprime b ∨ (2*w-1).Coprime b) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → AtOrder (4*b) n := by
  classical
  have cls (i:Fin b) := three_unit_class bp odd (Nat.succ_pos i.val) (all (i.val+1) (by omega))
  choose bound spec using cls
  refine ⟨1+Finset.univ.sup bound,?_⟩
  rintro n hn ⟨k,hk⟩
  have kp : 0 < k := by omega
  let i : Fin b := ⟨(k-1)%b,Nat.mod_lt _ bp⟩
  have km : k ≡ i.val+1 [MOD b] := by
    have H := (Nat.mod_modEq (k-1) b).symm.add_right 1
    rwa [Nat.sub_add_cancel kp] at H
  have sufficient := Finset.le_sup (f := bound) (Finset.mem_univ i)
  apply spec i n (by omega) ⟨k,hk⟩
  rw [hk]
  exact km.mul_left' 4

/-- Includes both positive exponents independently, equal primes, and
zero exponents. There is a single threshold for the entire modulus. -/
theorem large_four_two_prime_powers {p q:ℕ} (pp:p.Prime) (pq:q.Prime)
    (po:2 < p) (qo:2 < q) (a d:ℕ) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → AtOrder (4*(p^a*q^d)) n :=
  large_four_of_units (Nat.mul_pos (pow_pos pp.pos _) (pow_pos pq.pos _))
    (((two_coprime_prime pp po).pow_right a).mul_right ((two_coprime_prime pq qo).pow_right d))
    (fun _ hw => units_at_two_powers pp pq a d hw)

theorem integral_large_four_two_prime_powers {p q:ℕ} (pp:p.Prime) (pq:q.Prime)
    (po:2 < p) (qo:2 < q) (a d:ℕ) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → IntegralSolution (4*(p^a*q^d)) n := by
  obtain ⟨B,hB⟩ := large_four_two_prime_powers pp pq po qo a d
  exact ⟨B,fun n h f => integer_gram (hB n h f)⟩

#print axioms large_four_two_prime_powers
#print axioms integral_large_four_two_prime_powers
end HadamardMod
