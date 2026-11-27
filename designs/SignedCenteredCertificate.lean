import SignedCapacityCertificate
import SignedSelfConjugacy

/-! Finite separating certificates with the energy and characteristic-residue constraints
of the integer centered quotient at C_p. -/

namespace Signed39.Contraction

open Finset

def deviationModulus (p : ℕ) (s : ℤ) (q e : ℕ) : Prop :=
  q=1 ∨ q.Prime ∧ 0<e ∧ q^e≡p-1 [MOD p] ∧ (q:ℤ)∣s
instance (p : ℕ) (s : ℤ) (q e : ℕ) : Decidable (deviationModulus p s q e) := by
  unfold deviationModulus; infer_instance

def centeredCertificate (p m : ℕ) [NeZero p] (k lam s c : ℤ) (D q e : ℕ) (h : Separator) (z : ℕ → ℤ) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-lam=(p:ℤ)*s ∧ ¬ (p:ℤ) ∣ s ∧
  ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam ∧ deviationModulus p s q e ∧
  ((p:ℤ)-1)*s<((D:ℤ)+1)^2 ∧ (∀ r : ZMod p, 0≤z r.val) ∧
  h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam)+((p/2:ℕ):ℤ)*(∑ r : ZMod p, z r.val)<0 ∧
  ∀ i : Fin (2*D+1), ∀ w : Fin (m+1),
    let d := (i.val:ℤ)-(D:ℤ)
    let a := c+d
    let b := (w.val:ℤ)
    (q:ℤ)∣d → d^2≤((p:ℤ)-1)*s → admissibleRow p m s lam c a b → admissibleShift p m a b →
    0≤h.value 1 a b (a^2)+z (a:ZMod p).val

instance (p m : ℕ) [NeZero p] (k lam s c : ℤ) (D q e : ℕ) (h : Separator) (z : ℕ → ℤ) :
    Decidable (centeredCertificate p m k lam s c D q e h z) := by unfold centeredCertificate; infer_instance

variable {p : ℕ} [Fact p.Prime] {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem centered_row_bounds {k lam s c : ℤ} {q e : ℕ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hmass : mass f=(p:ℤ)*c) (hmod : deviationModulus p s q e) (i : ZMod p) :
    (q:ℤ)∣rowMass f i-c ∧ (rowMass f i-c)^2≤((p:ℤ)-1)*s := by
  obtain ⟨c',h',_,_,hcor⟩ := centered_row_corr hf hn
  have eq : c'=c := mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p:ℤ)≠0) (h'.symm.trans hmass)
  subst c'
  have he : energy (fun i => rowMass f i-c)=((p:ℤ)-1)*s := by rw [energy_zero,hcor]; simp; ring
  refine ⟨?_,he ▸ single_le_sum (fun j _ => sq_nonneg (rowMass f j-c)) (mem_univ i)⟩
  rcases hmod with one|⟨prime,exp,inv,div⟩
  · simp [one]
  · have : Fact q.Prime := ⟨prime⟩
    exact self_conjugate_centered _ hcor e exp inv div i

theorem centered_false {k lam s c : ℤ} {m D q e : ℕ} {h : Separator} {z : ℕ → ℤ}
    (hm : Fintype.card H=m) (cert : centeredCertificate p m k lam s c D q e h z) :
    ¬ ∃ f : ZMod p × H → ℤ, IsSDS k lam f := by
  obtain ⟨_,cop,hn,hs,hc2,hmod,hD,zpos,hbad,hall⟩ := cert
  apply capacity_family_false hm hn hs hc2 zpos hbad
  intro f hf hmain i
  let a := rowMass f i
  let b := energy (row f i)
  let d := a-c
  obtain ⟨div,sq⟩ := centered_row_bounds hf hn hmain hmod i
  change (q:ℤ)∣d at div
  change d^2≤((p:ℤ)-1)*s at sq
  have low : -(D:ℤ)≤d := by
    by_contra! bad
    have smaller : d≤-(D:ℤ)-1 := by omega
    nlinarith [mul_nonneg (show 0≤ -(D:ℤ)-1-d by omega) (show 0≤ -d+(D:ℤ)+1 by omega)]
  have high : d≤(D:ℤ) := by
    by_contra! bad
    have smaller : (D:ℤ)+1≤d := by omega
    nlinarith [mul_nonneg (show 0≤d-(D:ℤ)-1 by omega) (show 0≤d+(D:ℤ)+1 by omega)]
  have raw := row_admissible hf hn hmain (hm ▸ cop) i
  have shift := row_shift_admissible hf hn hs (hm ▸ cop) i
  rw [hm] at raw shift
  change admissibleRow p m s lam c a b at raw
  change admissibleShift p m a b at shift
  have b₀ := raw.2.2.1
  have b₁ := raw.2.2.2.1
  let u : Fin (2*D+1) := ⟨(d+D).toNat,by omega⟩
  let w : Fin (m+1) := ⟨b.toNat,by omega⟩
  have hu : (u.val:ℤ)-(D:ℤ)=d := by dsimp [u]; omega
  have hw : (w.val:ℤ)=b := Int.toNat_of_nonneg b₀
  have ca : c+d=a := by dsimp [d]; ring
  have use := hall u w
  simp only [hu,hw,ca] at use
  exact use div sq raw shift

theorem abelian_centered_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) [NeZero p] (k lam s c : ℤ) (D q e : ℕ) (h : Separator) (z : ℕ → ℤ)
    (hg : Fintype.card G=p*m) (hc : centeredCertificate p m k lam s c D q e h z) :
    ¬ ∃ f : G → ℤ, IsSDS k lam f := by
  classical
  have : Fact p.Prime := ⟨hc.1⟩
  obtain ⟨K,hK,⟨eq⟩⟩ := split_prime_factor hg hc.2.1
  rintro ⟨f,hf⟩
  have size : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  exact centered_false size hc ⟨_,pullback hf eq⟩

#print axioms abelian_centered_exclusion

end Signed39.Contraction

