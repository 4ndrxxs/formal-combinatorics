import SignedBasic

/-! The least positive variance numerator of an integral vector of length m is m−1. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [Fintype H]

def energy (a : H → ℤ) : ℤ := ∑ i, (a i)^2
def mass (a : H → ℤ) : ℤ := ∑ i, a i
def variance (a : H → ℤ) : ℤ := (Fintype.card H : ℤ)*energy a - (mass a)^2

theorem pairwise_variance (a : H → ℤ) :
    (∑ i : H, ∑ j : H, (a i-a j)^2) = 2*variance a := by
  calc
    _ = ∑ i : H, ∑ j : H, ((a i)^2+(a j)^2-2*a i*a j) := by
      apply sum_congr rfl; intro i _
      apply sum_congr rfl; intros
      ring
    _ = _ := by
      simp only [variance,energy,mass,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,
        nsmul_eq_mul, ← mul_sum, ← sum_mul]
      ring

theorem variance_constant (a : H → ℤ) (c : ℤ) (hc : ∀ i, a i=c) : variance a = 0 := by
  simp [variance,energy,mass,hc]
  ring

theorem variance_nonneg (a : H → ℤ) : 0 ≤ variance a := by
  have h : 0 ≤ ∑ i : H, ∑ j : H, (a i-a j)^2 :=
    sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  rw [pairwise_variance] at h
  omega

theorem variance_minimum (a : H → ℤ) {x y : H} (hxy : a x≠a y) :
    (Fintype.card H : ℤ)-1 ≤ variance a := by
  classical
  let s := univ.filter (fun i => a i = a x)
  let r := s.card
  let m := Fintype.card H
  have hx : x ∈ s := by simp [s]
  have hy : y ∉ s := by simp [s,hxy.symm]
  have hr : 0 < r := card_pos.mpr ⟨x,hx⟩
  have hrm : r < m := by
    change s.card < Fintype.card H
    exact card_lt_univ_of_notMem hy
  let cut := fun i j : H => if i∈s then (if j∈s then (0:ℤ) else 1)
                            else (if j∈s then 1 else 0)
  have le (i j : H) : cut i j ≤ (a i-a j)^2 := by
    have hi : i∈s ↔ a i=a x := by simp [s]
    have hj : j∈s ↔ a j=a x := by simp [s]
    dsimp only [cut]
    split_ifs with h1 h2 h2 <;> try exact sq_nonneg _
    · have hn : a i ≠ a j := fun e => h2 (hj.mpr (e.symm.trans (hi.mp h1)))
      have hne : a i-a j ≠ 0 := sub_ne_zero.mpr hn
      have hpos := sq_pos_of_ne_zero hne
      omega
    · have hn : a i ≠ a j := fun e => h1 (hi.mpr (e.trans (hj.mp h2)))
      have hne : a i-a j ≠ 0 := sub_ne_zero.mpr hn
      have hpos := sq_pos_of_ne_zero hne
      omega
  have rs : ∑ i : H, (if i∈s then (1:ℤ) else 0) = r := by simp [r]
  have cutnum : (∑ i : H, ∑ j : H, cut i j) = 2*(r:ℤ)*((m:ℤ)-r) := by
    have expr (i j : H) : cut i j =
        (if i∈s then 1 else 0) + (if j∈s then 1 else 0) -
          2*(if i∈s then 1 else 0)*(if j∈s then 1 else 0) := by
      by_cases hi : i∈s <;> by_cases hj : j∈s <;> simp [cut,hi,hj]
    simp only [expr,sum_sub_distrib,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,
      ← mul_sum, ← sum_mul, rs]
    change _ = 2*(r:ℤ)*((Fintype.card H:ℤ)-r)
    ring
  have hbound := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => le i j))
  rw [pairwise_variance,cutnum] at hbound
  have h1 : (0:ℤ) ≤ r-1 := by omega
  have h2 : (0:ℤ) ≤ (m:ℤ)-r-1 := by omega
  change (m:ℤ)-1 ≤ variance a
  nlinarith [mul_nonneg h1 h2]

theorem variance_ternary (a : H → ℤ) (h : ∀ i, a i = -1 ∨ a i=0 ∨ a i=1) :
    variance a ≤ (Fintype.card H : ℤ)^2 := by
  have hs : energy a ≤ (Fintype.card H : ℤ) := calc
    _ ≤ ∑ _ : H, (1:ℤ) := sum_le_sum (fun i _ => by rcases h i with he|he|he <;> norm_num [he])
    _ = _ := by simp
  unfold variance
  nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card H) : (0:ℤ) ≤ _)
    (sub_nonneg.mpr hs), sq_nonneg (mass a)]

theorem variance_scale (a : H → ℤ) (p : ℤ) : variance (fun x => p*a x) = p^2*variance a := by
  simp only [variance,energy,mass,mul_pow, ← mul_sum]
  ring

end Signed39.Contraction
