import Quantum.Hadamard.ArithmeticOddUnits

/-! If every prime factor is three modulo four, all units have
multiplicative order twice an odd divisor. This includes arbitrary
products and arbitrary positive prime exponents. -/
namespace Hadamard.Arithmetic
open Hadamard.PG

private theorem combine_period {q e m p : ℕ} (hm : q^e ≡ 1 [MOD m]) (hp : q^e ≡ 1 [MOD p]) :
    q^(e*p) ≡ 1 [MOD m*p] := by
  have hq : ((q^e:ℕ):ZMod p)=1 := by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hp
  have geo := geom_at_one (q^e) p p hq
  simp only [ZMod.natCast_self] at geo
  have gd : p ∣ geom (q^e) p := (ZMod.natCast_eq_zero_iff _ _).mp geo
  have hsub : (m:ℤ) ∣ ((q^e:ℕ):ℤ)-1 := by simpa using (Nat.modEq_iff_dvd.mp hm.symm)
  have gsub : (p:ℤ) ∣ (geom (q^e) p:ℤ) := by exact_mod_cast gd
  have prod := mul_dvd_mul hsub gsub
  have id := geom_int (q^e) p
  have strong : ((m*p:ℕ):ℤ) ∣ ((q^(e*p):ℕ):ℤ)-1 := by
    rw [pow_mul,Nat.cast_pow,←id,mul_comm (geom (q^e) p:ℤ)]
    simpa using prod
  exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr (by simpa using strong))

theorem odd_unit_exponent {m q : ℕ} (mp : 0 < m) (c : q.Coprime m)
    (primes : ∀ p, p.Prime → p ∣ m → p%4=3) :
    ∃ t : ℕ, Odd t ∧ q^(2*t) ≡ 1 [MOD m] := by
  induction m using Nat.strong_induction_on with
  | ind m IH =>
    by_cases m1 : m=1
    · exact ⟨1,by decide,by subst m; exact Nat.modEq_one⟩
    obtain ⟨p,pp,pm⟩ := Nat.exists_prime_and_dvd m1
    obtain ⟨k,mk⟩ := pm
    have pdiv : p∣m := ⟨k,mk⟩
    have kdiv : k∣m := by rw [mk]; exact dvd_mul_left _ _
    have h4 := primes p pp pdiv
    have kp : 0 < k := by by_contra! h; have k0 := Nat.le_zero.mp h; simp_all
    have kl : k < m := by rw [mk]; have := pp.two_le; nlinarith
    obtain ⟨t,todd,tper⟩ := IH k kl kp (c.of_dvd_right kdiv) (fun l lpr lk => primes l lpr (lk.trans kdiv))
    let s := (p-1)/2
    have sp : 2*s=p-1 := by dsimp [s]; omega
    have so : Odd s := by apply Nat.odd_iff.mpr; dsimp [s]; omega
    have po := pp.odd_of_ne_two (by omega : p≠2)
    have pf : q^(2*s) ≡ 1 [MOD p] := by
      rw [sp,← Nat.totient_prime pp]
      exact Nat.ModEq.pow_totient (c.of_dvd_right pdiv)
    let e := 2*t*s
    have ek : q^e ≡ 1 [MOD k] := by simpa [e,pow_mul] using tper.pow s
    have ep : q^e ≡ 1 [MOD p] := by
      rw [show e=(2*s)*t by dsimp [e]; ring,pow_mul]
      simpa using pf.pow t
    have comb := combine_period ek ep
    refine ⟨t*s*p,(todd.mul so).mul po,?_⟩
    rw [mk,Nat.mul_comm p k,show 2*(t*s*p)=e*p by dsimp [e]; ring]
    exact comb

end Hadamard.Arithmetic
