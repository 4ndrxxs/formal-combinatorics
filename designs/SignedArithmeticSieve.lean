import SignedLinearPrimeBound
import SignedQuotientSelfConjugacy
import SignedAbsoluteBound

/-! Finite arithmetic parameter screening and modular certificates for bounded norm cofactors. -/

namespace Signed39.Contraction

open Finset

/-- All data in this certificate are rational integers. -/
def quotientCertificate (v n r q e j b : ℕ) : Prop :=
  r.Prime ∧ q.Prime ∧ r∣v ∧ q≠r ∧ 0<e ∧ q^e≡r-1 [MOD r] ∧ ¬q∣b ∧ n=q^(2*j+1)*b

instance (v n r q e j b : ℕ) : Decidable (quotientCertificate v n r q e j b) := by
  unfold quotientCertificate; infer_instance

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem quotient_certificate_false {v n r q e j b : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hg : Fintype.card G=v) (hn : k-lam=n) (h : quotientCertificate v n r q e j b) : False := by
  obtain ⟨hr,hq,hv,hne,he,hi,hb,hpow⟩ := h
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  apply quotient_self_conjugate_exclusion (r:=r) (q:=q) hf (hg ▸ hv) hne e he hi j (b:ℤ)
  · exact_mod_cast hb
  · rw [hn]; exact_mod_cast hpow

/-- A self-conjugacy witness on the p-quotient eliminates a given cofactor s
whenever q has odd valuation in s and q differs from p. -/
theorem prime_factor_sieve {p s q e j b : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hd : p∣Fintype.card G) (hn : k-lam=(p:ℤ)*s)
    (cert : quotientCertificate p s p q e j b) : False := by
  obtain ⟨hp,hq,_,hne,he,hi,hb,hpow⟩ := cert
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have dn : ¬q∣p := fun d => hne (((Nat.dvd_prime hp).mp d).resolve_left hq.ne_one)
  have db : ¬q∣p*b := fun h => (hq.dvd_or_dvd h).elim dn hb
  apply quotient_self_conjugate_exclusion (r:=p) (q:=q) hf hd hne e he hi j ((p*b:ℕ):ℤ)
  · exact_mod_cast db
  · rw [hn,hpow]
    push_cast
    ring

/-- If an abelian design with n=ps exists, the global nonnegative mass can be
written pc where c ranges from zero to m and the two integer tests below hold. -/
theorem normalized_parameter {p m : ℕ} [Fact p.Prime] {s k lam : ℤ} {f : G → ℤ}
    (hf : IsSDS k lam f) (hg : Fintype.card G=p*m) (hn : k-lam=(p:ℤ)*s) :
    ∃ c : ℕ, c ≤ m ∧ (p:ℤ)*((c:ℤ)^2)=s+(m:ℤ)*lam ∧
      (p:ℤ)*c≤k ∧ k≤(p:ℤ)*m ∧ 2∣k-(p:ℤ)*c := by
  have prime := (Fact.out : p.Prime)
  have hp : (0:ℤ)<p := by exact_mod_cast prime.pos
  have support := support_card hf
  have kbound : k≤(p:ℤ)*m := by
    rw [← Nat.cast_mul,← hg,← support]
    exact_mod_cast card_le_univ _
  obtain ⟨g,hg',pos⟩ : ∃ g : G → ℤ, IsSDS k lam g ∧ 0 ≤ mass g := by
    by_cases h : 0 ≤ mass f
    · exact ⟨f,hf,h⟩
    · exact ⟨fun i => -f i,hf.neg,by simp only [mass,sum_neg_distrib] at h ⊢; omega⟩
  have he := sds_mass hg'
  rw [hg,Nat.cast_mul,hn] at he
  have hd : (p:ℤ) ∣ (mass g)^2 := ⟨s+(m:ℤ)*lam,by linear_combination he⟩
  obtain ⟨b,hb⟩ := (Nat.prime_iff_prime_int.mp prime).dvd_of_dvd_pow hd
  have bp : 0≤b := nonneg_of_mul_nonneg_right (hb ▸ pos) hp
  have neg := negative_count hg'
  change 2*_=k-mass g at neg
  have kb : mass g≤k := by
    have hc : (0:ℤ)≤((univ.filter (fun x => g x= -1)).card:ℤ) := Nat.cast_nonneg _
    omega
  rw [hb] at kb he neg
  have eq : (p:ℤ)*b^2=s+(m:ℤ)*lam := by apply mul_left_cancel₀ hp.ne'; linear_combination he
  have bm : b≤(m:ℤ) := le_of_mul_le_mul_left (kb.trans kbound) hp
  exact ⟨b.toNat,by omega,by simpa [Int.toNat_of_nonneg bp] using eq,
    by simpa [Int.toNat_of_nonneg bp] using kb,kbound,⟨_,by simpa [Int.toNat_of_nonneg bp] using neg.symm⟩⟩

def numericalParameter (p m s c : ℕ) (lam : ℤ) : Prop :=
  p < m ∧ ¬ 2 ∣ m ∧ ¬ p ∣ m ∧ c ≤ m ∧ (p:ℤ)*c^2=(s:ℤ)+(m:ℤ)*lam ∧
  (p:ℤ)*c≤(p:ℤ)*s+lam ∧ (p:ℤ)*s+lam≤(p:ℤ)*m ∧ 2∣(p:ℤ)*s+lam-(p:ℤ)*c

instance (p m s c : ℕ) (lam : ℤ) : Decidable (numericalParameter p m s c lam) := by
  unfold numericalParameter; infer_instance

theorem bounded_parameters {p m s : ℕ} [Fact p.Prime] {k lam : ℤ} {f : G → ℤ}
    (hf : IsSDS k lam f) (hg : Fintype.card G=p*m) (hn : k-lam=(p:ℤ)*s)
    (hs : ¬p∣s) (hm : p < m) :
    ∃ c : ℕ, numericalParameter p m s c lam ∧
      lam=((p:ℤ)*c^2-s)/(m:ℤ) ∧ p*m≤(p*s)^2+p*s+1 := by
  have hp := (Fact.out : p.Prime)
  have hsn : ¬(p:ℤ)∣(s:ℤ) := by exact_mod_cast hs
  have nsp : ¬ IsSquare (k-lam) := hn ▸ nonsquare_of_valuation_one hp hsn
  have s0 : 0 < s := Nat.pos_of_ne_zero (fun e => hs (e ▸ dvd_zero _))
  have upper := absolute_order_bound hf (by rw [hn]; exact_mod_cast Nat.mul_pos hp.pos s0) nsp
  rw [hn,hg] at upper
  have ud : p*m≤(p*s)^2+p*s+1 := by exact_mod_cast upper
  have odd : ¬2∣m := by
    intro d
    exact nsp (even_norm_square hf (hg ▸ dvd_mul_of_dvd_right d p))
  have cop := valuation_one_coprime hf hg hn hsn
  obtain ⟨c,hcm,e,klo,khi,pa⟩ := normalized_parameter hf hg hn
  have mpos : (0:ℤ) < m := by exact_mod_cast (hp.pos.trans hm)
  have hparam : numericalParameter p m s c lam := ⟨hm,odd,hp.coprime_iff_not_dvd.mp cop,hcm,e,
    by omega,by omega,by rwa [show (p:ℤ)*s+lam=k by omega]⟩
  refine ⟨c,hparam,?_,ud⟩
  rw [show (p:ℤ)*c^2-(s:ℤ)=lam*(m:ℤ) by linear_combination e]
  exact (Int.mul_ediv_cancel _ mpos.ne').symm

end Signed39.Contraction

