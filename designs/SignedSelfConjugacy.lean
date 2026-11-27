import SignedConcentration

/-! Self-conjugacy modulo an auxiliary prime for an integral autocorrelation word. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {q : ℕ} [Fact q.Prime]

omit [DecidableEq H] in
theorem frobenius_forward (g : H → ZMod q) (r : ℕ) :
    (forward g)^(q^r) = ∑ x : H, AddMonoidAlgebra.single (q^r • x) (g x) := by
  have : ExpChar (AddMonoidAlgebra (ZMod q) H) q :=
    expChar_of_injective_ringHom (algebraMap (ZMod q) (AddMonoidAlgebra (ZMod q) H)).injective q
  rw [← iterateFrobenius_def]
  simp only [forward,map_sum,iterateFrobenius_def,AddMonoidAlgebra.single_pow,ZMod.pow_card_pow]

/-- When a positive q-power acts by negation on H, divisibility of every
autocorrelation by q forces every coefficient to be divisible by q. -/
theorem self_conjugate_coefficients (u : H → ℤ) (r : ℕ) (hr : 0 < r)
    (hinv : ∀ x : H, q^r • x = -x) (hc : ∀ t, (q:ℤ) ∣ corr u t) :
    ∀ x, (q:ℤ) ∣ u x := by
  let g := fun x : H => (u x : ZMod q)
  let N := q^r
  have hn : 2 ≤ N := (Fact.out : q.Prime).two_le.trans (Nat.le_pow hr)
  have fg : forward g*backward g=0 := by
    apply AddMonoidAlgebra.ext; ext t
    rw [cross_coeff]
    simpa [g,corr,add_comm,mul_comm] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hc t)
  have fb : (forward g)^N=backward g := by simp only [N,frobenius_forward,hinv,backward]
  have bf : (backward g)^N=forward g := by simp only [N,frobenius_backward,hinv,neg_neg,forward]
  have nil : (forward g)^(N+1)=0 := by rw [pow_succ,fb,mul_comm,fg]
  have stable : (forward g)^(N*N)=forward g := by rw [pow_mul,fb,bf]
  have big : N+1≤N*N := by nlinarith [Nat.mul_le_mul_left N hn]
  obtain ⟨w,hw⟩ := Nat.exists_eq_add_of_le big
  have zero : forward g=0 := by rw [← stable,hw,pow_add,nil,zero_mul]
  intro x
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  simpa [g] using congrArg (fun A : AddMonoidAlgebra (ZMod q) H => A.coeff x) zero

theorem self_conjugate_centered {p : ℕ} [Fact p.Prime] {s : ℤ} (u : ZMod p → ℤ)
    (hc : ∀ t : ZMod p, corr u t=(if t=0 then (p:ℤ)*s else 0)-s)
    (r : ℕ) (hr : 0<r) (hinv : (q^r:ℕ) ≡ p-1 [MOD p]) (hq : (q:ℤ) ∣ s) :
    ∀ x, (q:ℤ) ∣ u x := by
  apply self_conjugate_coefficients u r hr
  · intro x
    have hp := (Fact.out : p.Prime).pos
    have e := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hinv
    rw [nsmul_eq_mul,e,Nat.cast_sub (by omega : 1≤p)]
    simp
  · intro t
    rw [hc]
    split_ifs
    · exact dvd_sub (dvd_mul_of_dvd_right hq _) hq
    · simpa using hq

theorem auxiliary_prime_exclusion {p : ℕ} [Fact p.Prime]
    {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (r : ℕ) (hr : 0<r) (hinv : (q^r:ℕ) ≡ p-1 [MOD p])
    (hq : (q:ℤ) ∣ s) (hq2 : ¬ (q:ℤ)^2 ∣ s) : False := by
  obtain ⟨c,_,_,_,hc⟩ := centered_row_corr hf hn
  let u := fun i => rowMass f i-c
  have each := self_conjugate_centered u hc r hr hinv hq
  have div : (q:ℤ)^2 ∣ corr u 1 := by
    apply dvd_sum
    intro i _
    simpa only [pow_two] using mul_dvd_mul (each i) (each (i+1))
  have h : corr u 1 = -s := by
    have one : (1:ZMod p)≠0 := one_ne_zero
    simpa only [ite_eq_right one,zero_sub] using hc 1
  rw [h] at div
  exact hq2 (dvd_neg.mp div)

#print axioms self_conjugate_coefficients

end Signed39.Contraction

