import Quantum.Hadamard.ArithmeticProduct
import Quantum.Hadamard.ArithmeticSquare

/-! Converts the two matrix constructions into one uniform asymptotic
statement for all multiples of four at each odd prime modulus. -/

namespace Hadamard.Arithmetic

structure PrimeOrderConstruction (m : ℕ) (P : ℕ → Prop) : Prop where
  paley : ∀ {q : ℕ}, q.Prime → q ≡ 3 [MOD 4] → P (q+1)
  productGrow : ∀ {q p n : ℕ}, q.Prime → q ≡ 3 [MOD 4] → ProductStep m q p →
    0 < n → P n → n ≡ q+1 [MOD m] → ∀ t, P (n+t*(p*q-1))
  doublePaley : ∀ {q : ℕ}, SquareSeed m q → P (squareOrder q)
  squareGrow : ∀ {q n : ℕ}, SquareSeed m q → 0 < n → P n → n ≡ 1 [MOD m] →
    ∀ t, P (n+t*squareIncrement q)

theorem close_progression {m n₀ u v : ℕ} {P : ℕ → Prop} (hm : 0 < m)
    (c4 : (4 : ℕ).Coprime m) (huv : u.gcd v = m) (hv : 0 < v)
    (pos : 0 < n₀) (h₀ : 4 ∣ n₀) (seed : P n₀)
    (growU : ∀ {n}, 0 < n → P n → n ≡ n₀ [MOD m] → ∀ t, P (n+t*(4*u)))
    (growV : ∀ {n}, 0 < n → P n → n ≡ n₀ [MOD m] → ∀ t, P (n+t*(4*v))) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ n₀ [MOD m] → P n := by
  obtain ⟨B,hB⟩ := eventually_in_progression hm c4 huv hv h₀
  refine ⟨B, ?_⟩
  intro n hn h4 hr
  obtain ⟨x,y,xy⟩ := hB n hn h4 hr
  have du : m ∣ u := huv ▸ Nat.gcd_dvd_left u v
  have dz : 4*u ≡ 0 [MOD m] :=
    Nat.modEq_zero_iff_dvd.mpr (du.trans (dvd_mul_left u 4))
  have hrx : n₀+x*(4*u) ≡ n₀ [MOD m] := by
    simpa using (dz.mul_left x).add_left n₀
  have px := growU pos seed (Nat.ModEq.refl _) x
  have py := growV (by omega) px hrx y
  rw [xy]
  simpa only [Nat.mul_comm x (4*u), Nat.mul_comm y (4*v)] using py

private theorem product_normalization {m q p : ℕ}
    (q4 : q ≡ 3 [MOD 4]) (hp : ProductStep m q p) :
    4*((p*q-1)/4) = p*q-1 := by
  have h4 : p*q ≡ 1 [MOD 4] := (hp.modFour.mul q4).trans (by decide)
  have qp : 1 ≤ p*q := by
    have hq : 0<q := by change q%4 = 3%4 at q4; omega
    exact Nat.mul_pos hp.prime.pos hq
  exact Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' qp).mp h4.symm)

theorem class_large {m : ℕ} {P : ℕ → Prop} (hm : m.Prime) (hm2 : 2 < m)
    (C : PrimeOrderConstruction m P) (r : ℕ) :
    ∃ B, ∀ n ≥ B, 4 ∣ n → n ≡ r [MOD m] → P n := by
  have c4 := four_coprime_prime hm hm2
  by_cases hr : r%m = 1
  · obtain ⟨q₁,q₂,h₁,h₂,gcd⟩ := square_steps hm hm2
    have rone : r ≡ 1 [MOD m] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt (show 1<m by omega)] using hr
    have pos : 0 < squareOrder q₁ := by dsimp [squareOrder]; omega
    have pos₂ : 0 < squareIncrement q₂ := by
      have H : 1 < (2*(q₂+1))^2 := by
        have := h₂.prime.two_le
        nlinarith
      dsimp [squareIncrement, squareOrder]; omega
    have four : 4 ∣ squareOrder q₁ := by
      have H := h₁.modFour
      change q₁%4 = 3%4 at H
      dsimp [squareOrder]
      omega
    have grow {q n : ℕ} (hq : SquareSeed m q) (hn : 0<n) (pn : P n)
        (res : n ≡ squareOrder q₁ [MOD m]) (t : ℕ) :
        P (n+t*(4*squareIncrement q)) := by
      simpa only [Nat.mul_assoc] using
        C.squareGrow hq hn pn (res.trans h₁.orderOne) (t*4)
    obtain ⟨B,hB⟩ := close_progression hm.pos c4 gcd pos₂ pos four (C.doublePaley h₁)
      (grow h₁) (grow h₂)
    exact ⟨B, fun n hn h4 res => hB n hn h4 ((res.trans rone).trans h₁.orderOne.symm)⟩
  · obtain ⟨q,p₁,p₂,hq,q4,qr,h₁,h₂,gcd⟩ := product_steps hm hm2 hr
    have pos₂ : 0 < (p₂*q-1)/4 := by
      have hq2 := hq.two_le
      have pp := h₂.prime.two_le
      have p4 := h₂.modFour
      change p₂%4 = 3%4 at p4
      have hp : 3 ≤ p₂ := by omega
      have h : 6 ≤ p₂*q := by nlinarith
      omega
    have four : 4 ∣ q+1 := by change q%4 = 3%4 at q4; omega
    have grow {p n : ℕ} (hp : ProductStep m q p) (hn : 0<n) (pn : P n)
        (res : n ≡ q+1 [MOD m]) (t : ℕ) : P (n+t*(4*((p*q-1)/4))) := by
      rw [product_normalization q4 hp]
      exact C.productGrow hq q4 hp hn pn res t
    obtain ⟨B,hB⟩ := close_progression hm.pos c4 gcd pos₂ (by omega) four (C.paley hq q4)
      (grow h₁) (grow h₂)
    exact ⟨B, fun n hn h4 res => hB n hn h4 (res.trans qr.symm)⟩

theorem all_large {m : ℕ} {P : ℕ → Prop} (hm : m.Prime) (hm2 : 2 < m)
    (C : PrimeOrderConstruction m P) : ∃ B, ∀ n ≥ B, 4 ∣ n → P n := by
  classical
  have cls (r : Fin m) := class_large hm hm2 C r.val
  choose bound hbound using cls
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro n hn h4
  let r : Fin m := ⟨n%m, Nat.mod_lt _ hm.pos⟩
  exact hbound r n ((Finset.le_sup (Finset.mem_univ r)).trans hn) h4 (Nat.mod_modEq n m).symm

end Hadamard.Arithmetic
