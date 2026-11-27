import Quantum.Hadamard.Basic

/-! Paley's prime-field character matrix and his bordered Hadamard construction
of order `q+1` for primes `q ≡ 3 (mod 4)`. The character sum calculation also
works over every finite field of odd characteristic. -/

noncomputable section

namespace Hadamard.Paley

open Finset

/-- The additive autocorrelation of the quadratic character of an odd finite field. -/
theorem character_corr {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (t : F) :
    (∑ x : F, quadraticChar F x * quadraticChar F (x+t)) =
      (if t = 0 then (Fintype.card F : ℤ) else 0) - 1 := by
  classical
  let L := quadraticChar F
  by_cases ht : t = 0
  · subst t
    have sq (a : F) : L a * L a = if a = 0 then 0 else 1 := by
      split_ifs with h
      · simp [L,h]
      · simpa [L,pow_two] using quadraticChar_sq_one h
    change (∑ a : F, L a * L (a+0)) = _
    simp [sq, sum_ite]
    rw [show (univ.filter (fun a : F => ¬a = 0)) = univ.erase 0 by ext; simp]
    rw [card_erase_of_mem (mem_univ 0), card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr inferInstance)]
    rfl
  · have hj : jacobiSum L L = -L (-1) := by
      have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
      rwa [(quadraticChar_isQuadratic F).inv] at h
    have hsq : L t ^ 2 = 1 := quadraticChar_sq_one ht
    have hm : L (-1) ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
    rw [ite_eq_right ht, zero_sub]
    calc
      _ = ∑ y : F, L ((-t)*y)*L (((-t)*y)+t) :=
        (Fintype.sum_equiv (Equiv.mulLeft₀ (-t) (neg_ne_zero.mpr ht)) _ _ (fun _ => rfl)).symm
      _ = L (-1)*jacobiSum L L := by
        rw [jacobiSum, mul_sum]
        apply sum_congr rfl
        intro y _
        rw [show (-t)*y+t = t*(1-y) by ring, show (-t)*y = ((-1)*t)*y by ring]
        simp only [map_mul]
        linear_combination (L (-1)*L y*L (1-y))*hsq
      _ = -1 := by rw [hj]; nlinarith

variable (q : ℕ) [Fact q.Prime]

/-- The Paley character matrix has entries `χ(j-i)`. -/
def Q (i j : ZMod q) : ℤ := quadraticChar (ZMod q) (j-i)

@[simp] theorem Q_diag (i : ZMod q) : Q q i i = 0 := by simp [Q]

theorem Q_sign_of_ne {i j : ZMod q} (h : i ≠ j) : HadamardMod.Sign (Q q i j) :=
  quadraticChar_dichotomy (sub_ne_zero.mpr h.symm)

private theorem char_ne_two (hq : q % 4 = 3) : ringChar (ZMod q) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

theorem Q_skew (hq : q % 4 = 3) (i j : ZMod q) : Q q i j = -Q q j i := by
  have hn : quadraticChar (ZMod q) (-1) = -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    rw [ZMod.exists_sq_eq_neg_one_iff]
    exact not_not.mpr hq
  unfold Q
  rw [show j-i = (-1)*(i-j) by ring, map_mul, hn, neg_one_mul]

theorem Q_row_sum (hq : q % 4 = 3) (i : ZMod q) : ∑ j, Q q i j = 0 := by
  calc
    _ = ∑ x : ZMod q, quadraticChar (ZMod q) x :=
      Fintype.sum_equiv (Equiv.addRight (-i)) _ _ (fun j => by simp [Q, sub_eq_add_neg])
    _ = 0 := quadraticChar_sum_zero (char_ne_two q hq)

theorem Q_col_sum (hq : q % 4 = 3) (j : ZMod q) : ∑ i, Q q i j = 0 := by
  simp_rw [Q_skew q hq _ j, Finset.sum_neg_distrib, Q_row_sum q hq, neg_zero]

theorem Q_gram (hq : q % 4 = 3) (i k : ZMod q) :
    ∑ j, Q q i j * Q q k j = (if i=k then (q:ℤ) else 0)-1 := by
  calc
    _ = ∑ x : ZMod q, quadraticChar (ZMod q) x * quadraticChar (ZMod q) (x+(i-k)) := by
      apply Fintype.sum_equiv (Equiv.addRight (-i))
      intro j
      change _ = quadraticChar (ZMod q) (j+ -i) * quadraticChar (ZMod q) (j+ -i+(i-k))
      rw [show j+ -i+(i-k)=j-k by abel]
      simp [Q, sub_eq_add_neg]
    _ = _ := by simpa only [sub_eq_zero, ZMod.card] using character_corr (char_ne_two q hq) (i-k)

/-- The `none` index borders the character block `Q−I` by ones. -/
def matrix : Option (ZMod q) → Option (ZMod q) → ℤ
  | none, _ => 1
  | some _, none => 1
  | some i, some j => Q q i j - if j=i then 1 else 0

theorem matrix_sign (i j : Option (ZMod q)) : HadamardMod.Sign (matrix q i j) := by
  cases i with
  | none => simp [matrix, HadamardMod.Sign]
  | some i =>
    cases j with
    | none => simp [matrix, HadamardMod.Sign]
    | some j =>
      by_cases e : j=i
      · subst j; simp [matrix, HadamardMod.Sign]
      · simpa [matrix,e] using Q_sign_of_ne q (Ne.symm e)

private theorem core_row_sum (hq : q % 4 = 3) (i : ZMod q) :
    ∑ j : ZMod q, matrix q (some i) (some j) = -1 := by
  simp [matrix, sum_sub_distrib, Q_row_sum q hq]

theorem matrix_ortho (hq : q % 4 = 3) (a b : Option (ZMod q)) (ne : a ≠ b) :
    ∑ j, matrix q a j * matrix q b j = 0 := by
  cases a with
  | none =>
    cases b with
    | none => contradiction
    | some k =>
      rw [Fintype.sum_option]
      change 1*1 + ∑ j : ZMod q, 1 * matrix q (some k) (some j) = 0
      simp [core_row_sum q hq]
  | some i =>
    cases b with
    | none =>
      rw [Fintype.sum_option]
      change 1*1 + ∑ j : ZMod q, matrix q (some i) (some j) * 1 = 0
      simp [core_row_sum q hq]
    | some k =>
      have e : i ≠ k := fun h => ne (congrArg some h)
      have term (j : ZMod q) : matrix q (some i) (some j)*matrix q (some k) (some j) =
          Q q i j * Q q k j - (if j=i then Q q k i else 0) -
            (if j=k then Q q i k else 0) := by
        by_cases a : j=i <;> by_cases b : j=k
        · exact (e (a.symm.trans b)).elim
        all_goals simp [matrix, a, b, e, Ne.symm e]
      rw [Fintype.sum_option]
      change 1*1 + ∑ j : ZMod q, matrix q (some i) (some j)*matrix q (some k) (some j) = 0
      simp only [term, sum_sub_distrib, Q_gram q hq, ite_eq_right e]
      simp [Q_skew q hq i k]

end Hadamard.Paley

namespace HadamardMod

/-- Paley type I yields an exact sign matrix, hence a solution at every modulus. -/
theorem paley_order (m q : ℕ) [Fact q.Prime] (hq : q % 4 = 3) : AtOrder m (q+1) := by
  let A : RowMatrix m (Option (ZMod q)) := fun i j => (Hadamard.Paley.matrix q i j : ZMod m)
  apply of_card (A := A) _ (by simp)
  constructor
  · intro i j
    rcases Hadamard.Paley.matrix_sign q i j with h|h <;> simp [A,h,Sign]
  · intro a b ne
    change (∑ j, (Hadamard.Paley.matrix q a j : ZMod m) * (Hadamard.Paley.matrix q b j : ZMod m)) = 0
    rw [← Int.cast_zero (R := ZMod m)]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod m)) (Hadamard.Paley.matrix_ortho q hq a b ne)

theorem paley_double (m q : ℕ) [Fact q.Prime] (hq : q % 4 = 3) : AtOrder m (2*(q+1)) :=
  at_mul (order_two m) (paley_order m q hq)

#print axioms paley_order
#print axioms paley_double

end HadamardMod

