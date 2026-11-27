import SignedSelfConjugacy

/-! The classical odd-valuation self-conjugacy test on any prime-order quotient. -/

namespace Signed39.Contraction

open Finset

variable {r q : ℕ} [Fact r.Prime] [Fact q.Prime]

private theorem scale_corr {I : Type} [AddCommGroup I] [Fintype I] (u : I → ℤ) (a : ℤ) (t : I) :
    corr (fun i => a*u i) t=a^2*corr u t := by
  simp only [corr,mul_sum]
  apply sum_congr rfl; intros; ring

theorem odd_ramification_exclusion (j : ℕ) (a : ℤ) (ha : ¬ (q:ℤ) ∣ a)
    (e : ℕ) (he : 0<e) (hinv : (q^e:ℕ) ≡ r-1 [MOD r]) (u : ZMod r → ℤ)
    (hu : ∀ t : ZMod r, corr u t=(if t=0 then (r:ℤ)*((q:ℤ)^(2*j+1)*a) else 0)-((q:ℤ)^(2*j+1)*a)) :
    False := by
  have nonzero : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  induction j generalizing u with
  | zero =>
    have hc : ∀ t : ZMod r, corr u t=(if t=0 then (r:ℤ)*((q:ℤ)*a) else 0)-(q:ℤ)*a := by simpa using hu
    have every := self_conjugate_centered u hc e he hinv (dvd_mul_right _ _)
    choose w hw using every
    have one := hc 1
    simp only [ite_eq_right one_ne_zero,zero_sub] at one
    have eq : u=fun i => (q:ℤ)*w i := funext hw
    rw [eq,scale_corr] at one
    apply ha
    refine ⟨-corr w 1,?_⟩
    apply mul_left_cancel₀ nonzero
    linear_combination one
  | succ j ih =>
    let b := (q:ℤ)^(2*j+1)*a
    have power : (q:ℤ)^(2*(j+1)+1)*a=(q:ℤ)^2*b := by
      rw [show 2*(j+1)+1=2+(2*j+1) by omega,pow_add]; dsimp [b]; ring
    have hc : ∀ t : ZMod r, corr u t=(if t=0 then (r:ℤ)*((q:ℤ)^2*b) else 0)-(q:ℤ)^2*b := by
      intro t; simpa only [power] using hu t
    have every := self_conjugate_centered u hc e he hinv ⟨(q:ℤ)*b,by ring⟩
    choose w hw using every
    have eq : u=fun i => (q:ℤ)*w i := funext hw
    apply ih w
    intro t
    apply mul_left_cancel₀ (pow_ne_zero 2 nonzero)
    have h := hc t
    rw [eq,scale_corr] at h
    change _=(q:ℤ)^2*((if t=0 then (r:ℤ)*b else 0)-b)
    by_cases ht : t=0 <;> simp only [ht,ite_true,ite_false] at h ⊢ <;> linear_combination h

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- On a prime-order quotient, a prime self-conjugate modulo its order
cannot occur to odd valuation in the norm. -/
theorem quotient_self_conjugate_exclusion {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hr : r ∣ Fintype.card G) (hne : q≠r) (e : ℕ) (he : 0<e) (hinv : (q^e:ℕ) ≡ r-1 [MOD r])
    (j : ℕ) (a : ℤ) (ha : ¬ (q:ℤ) ∣ a) (hn : k-lam=(q:ℤ)^(2*j+1)*a) : False := by
  obtain ⟨φ,hφ⟩ := exists_prime_quotient r (Fact.out : r.Prime) hr
  let w := projected φ f
  let n := k-lam
  let L := (Nat.card φ.ker:ℤ)*lam
  have hw : ∀ t, corr w t=(if t=0 then n else 0)+L := projected_flat φ hφ hf
  have hm : (mass w)^2=n+(r:ℤ)*L := by simpa [ZMod.card] using mass_from_flat w n L hw
  let u := fun i : ZMod r => (r:ℤ)*w i-mass w
  have each (t : ZMod r) : corr u t=(if t=0 then (r:ℤ)*((r:ℤ)*n) else 0)-(r:ℤ)*n := by
    have ht : (∑ i, w (i+t))=mass w := sum_translate w t
    calc
      _ = ∑ i, ((r:ℤ)^2*(w i*w (i+t))-(r:ℤ)*mass w*w i-(r:ℤ)*mass w*w (i+t)+(mass w)^2) := by
        apply sum_congr rfl; intro i _; dsimp [u]; ring
      _ = (r:ℤ)^2*corr w t-(r:ℤ)*mass w*mass w-(r:ℤ)*mass w*mass w+(r:ℤ)*(mass w)^2 := by
        simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,ht,sum_const,card_univ,nsmul_eq_mul,ZMod.card,corr,mass]
      _ = _ := by rw [hw]; by_cases h : t=0 <;> simp only [h,ite_true,ite_false,zero_add] <;> linear_combination -(r:ℤ)*hm
  have dq : ¬ (q:ℤ) ∣ (r:ℤ) := by
    intro d
    have d' : q∣r := by exact_mod_cast d
    exact hne (((Nat.dvd_prime (Fact.out : r.Prime)).mp d').resolve_left (Fact.out : q.Prime).ne_one)
  have dqa : ¬ (q:ℤ) ∣ (r:ℤ)*a := fun d =>
    ((Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd d).elim dq ha
  have sub : (r:ℤ)*n=(q:ℤ)^(2*j+1)*((r:ℤ)*a) := by dsimp [n]; rw [hn]; ring
  exact odd_ramification_exclusion j ((r:ℤ)*a) dqa e he hinv u (fun t => by simpa only [← sub] using each t)

#print axioms quotient_self_conjugate_exclusion

end Signed39.Contraction

