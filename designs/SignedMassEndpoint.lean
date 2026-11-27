import SignedArithmeticSieve

/-! The signed mass modulo the group order is within 2s steps of either endpoint in units of p. -/

namespace Signed39.Contraction

theorem mass_endpoint {p m s c : ℕ} {lam : ℤ} (hp : 0<p) (hs : 0 < s)
    (h : numericalParameter p m s c lam) : c<2*s ∨ m-c<2*s := by
  obtain ⟨_,_,_,cm,e,lo,_,_⟩ := h
  by_contra! none
  have ppos : (0:ℤ)<p := by exact_mod_cast hp
  have pos : (0:ℤ) < s := by exact_mod_cast hs
  have prod := mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg m : 0≤(m:ℤ))
  have bound : (p:ℤ)*((c:ℤ)*((m:ℤ)-c)) < (p:ℤ)*((m:ℤ)*s) := by
    nlinarith
  have forbidden := (mul_lt_mul_iff_right₀ ppos).mp bound
  have cmin : (2:ℤ)*s≤c := by exact_mod_cast none.1
  have cother : (2:ℤ)*s≤(m:ℤ)-c := by
    have hn : 2*s+c ≤ m := by omega
    have zi : (2:ℤ)*s+c≤(m:ℤ) := by exact_mod_cast hn
    omega
  by_cases small : 2*(c:ℤ) ≤ m
  · have v := mul_nonneg (sub_nonneg.mpr cmin) (show (0:ℤ)≤(m:ℤ)-c by omega)
    have w := mul_nonneg pos.le (show (0:ℤ)≤(m:ℤ)-2*c by omega)
    nlinarith
  · have v := mul_nonneg (sub_nonneg.mpr cother) (Nat.cast_nonneg c : (0:ℤ)≤c)
    have w := mul_nonneg pos.le (show (0:ℤ)≤2*(c:ℤ)-m by omega)
    nlinarith

end Signed39.Contraction

