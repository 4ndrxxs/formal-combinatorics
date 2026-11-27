import SignedSelfConjugacy

/-! Small values of the norm divided by a common prime. -/

namespace Signed39.Contraction

open Finset

private theorem small_squares (d : ℤ) (hd : d^2<9) : d^2=0 ∨ d^2=1 ∨ d^2=4 := by
  have lo : -2≤d := by
    by_contra! h
    have ht : d≤ -3 := by omega
    nlinarith [sq_nonneg (d+3)]
  have hi : d≤2 := by
    by_contra! h
    have ht : 3≤d := by omega
    nlinarith [sq_nonneg (d-3)]
  interval_cases d <;> decide

private theorem obstruction_zero_or_one {p m s d : ℤ} (hpm : p < m) (hs₀ : 0 < s) (hsp : s < p)
    (hd : m ∣ p*d^2-s) (small : d^2=0 ∨ d^2=1) : False := by
  rcases small with zero|one
  · have dd : m ∣ s := by simpa [zero] using hd
    have := Int.le_of_dvd hs₀ dd
    omega
  · have dd : m ∣ p-s := by simpa [one] using hd
    have := Int.le_of_dvd (by omega : 0<p-s) dd
    omega

private theorem obstruction_four {p : ℤ} {m : ℕ} {d : ℤ} (hpm : p<(m:ℤ)) (hp : 4<p)
    (hm : Odd m) (hd : (m:ℤ) ∣ p*d^2-4) (small : d^2<9) : False := by
  rcases small_squares d small with zero|one|four
  · exact obstruction_zero_or_one hpm (by decide) hp hd (Or.inl zero)
  · exact obstruction_zero_or_one hpm (by decide) hp hd (Or.inr one)
  · rw [four,show p*4-4=4*(p-1) by ring] at hd
    have cop : Nat.Coprime m 4 := (Nat.coprime_two_right.mpr hm).pow_right 2
    have dd := (show IsCoprime (m:ℤ) (4:ℤ) from cop.isCoprime).dvd_of_dvd_mul_left hd
    have := Int.le_of_dvd (by omega : 0<p-1) dd
    omega

/-- A nonzero centered vector has energy strictly greater than the square of any single entry. -/
private theorem peak_lt_energy {I : Type} [Fintype I] [DecidableEq I] (u : I → ℤ) (hM : mass u=0)
    (hE : 0<energy u) (i : I) : (u i)^2<energy u := by
  have lower : (u i)^2≤energy u := single_le_sum (fun z _ => sq_nonneg (u z)) (mem_univ i)
  apply lower.lt_of_ne
  intro h
  have e := sum_erase_add univ (fun z => (u z)^2) (mem_univ i)
  change _+_=energy u at e
  have zero : (∑ z ∈ univ.erase i, (u z)^2)=0 := by omega
  have each (j : I) (hj : j∈univ.erase i) : u j=0 := by
    have z := (sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg (u z))).mp zero j hj
    simpa using z
  have sz : (∑ z ∈ univ.erase i, u z)=0 := sum_eq_zero each
  have m := sum_erase_add univ u (mem_univ i)
  change _+_=mass u at m
  rw [sz,hM,zero_add] at m
  rw [m] at h
  norm_num at h
  omega

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

private theorem small_witness {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (hc : p.Coprime (Fintype.card H))
    (hm : 1<Fintype.card H) (hsp : s<(p:ℤ)) :
    ∃ c : ℤ, ∃ i : ZMod p, let u := fun z => rowMass f z-c
      mass u = 0 ∧ (∀ t, corr u t=(if t=0 then (p:ℤ)*s else 0)-s) ∧
      ((p:ℤ)-s)*(u i)^2 ≤ ((p:ℤ)-1)*s ∧
      (Fintype.card H:ℤ) ∣ (p:ℤ)*(u i)^2-s := by
  obtain ⟨c,_,he,hmass,hcor⟩ := centered_row_corr hf hn
  have henergy : energy (fun z => rowMass f z-c)=((p:ℤ)-1)*s := by
    rw [energy_zero,hcor]; simp; ring
  obtain ⟨i,h⟩ := concentration hf hn hs hc hm hsp he henergy
  exact ⟨c,i,hmass,hcor,h⟩

theorem no_norm_twice {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*2) (hc : p.Coprime (Fintype.card H)) (hp : 3≤p) (hm : p<Fintype.card H) : False := by
  by_cases small : p=3
  · subst p
    exact auxiliary_prime_exclusion (q:=2) hf hn 1 (by decide) (by decide) (by decide) (by decide)
  have hp' : 5≤p := by
    have pp : p.Prime := Fact.out
    by_contra! h
    have := (show p=4 by omega) ▸ pp
    exact (by decide : ¬ Nat.Prime 4) this
  have hsp : (2:ℤ)<p := by omega
  have hnd : ¬ (p:ℤ) ∣ 2 := fun h => (not_le.mpr hsp) (Int.le_of_dvd (by decide) h)
  obtain ⟨c,i,_,_,h,hd⟩ := small_witness hf hn hnd hc (by omega) hsp
  let d := rowMass f i-c
  change ((p:ℤ)-2)*d^2≤((p:ℤ)-1)*2 at h
  have sm : d^2<4 := by
    by_contra! he
    have sub := mul_le_mul_of_nonneg_left he (by omega : (0:ℤ)≤(p:ℤ)-2)
    omega
  exact obstruction_zero_or_one (d:=d) (by exact_mod_cast hm) (by decide) hsp hd
    (by rcases small_squares d (by omega) with l|l|l <;> omega)

theorem no_norm_thrice {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*3) (hc : p.Coprime (Fintype.card H)) (hp : 5≤p) (hm : p<Fintype.card H) : False := by
  by_cases h5 : p=5
  · subst p
    exact auxiliary_prime_exclusion (q:=3) hf hn 2 (by decide) (by decide) (by decide) (by decide)
  by_cases h7 : p=7
  · subst p
    exact auxiliary_prime_exclusion (q:=3) hf hn 3 (by decide) (by decide) (by decide) (by decide)
  have hp' : 11≤p := by
    by_contra! h
    have pp : p.Prime := Fact.out
    interval_cases p <;> norm_num at *
  have hsp : (3:ℤ)<p := by omega
  have hnd : ¬ (p:ℤ) ∣ 3 := fun h => (not_le.mpr hsp) (Int.le_of_dvd (by decide) h)
  obtain ⟨c,i,_,_,h,hd⟩ := small_witness hf hn hnd hc (by omega) hsp
  let d := rowMass f i-c
  change ((p:ℤ)-3)*d^2≤((p:ℤ)-1)*3 at h
  have sm : d^2<4 := by
    by_contra! he
    have sub := mul_le_mul_of_nonneg_left he (by omega : (0:ℤ)≤(p:ℤ)-3)
    omega
  exact obstruction_zero_or_one (d:=d) (by exact_mod_cast hm) (by decide) hsp hd
    (by rcases small_squares d (by omega) with l|l|l <;> omega)

theorem no_norm_four_times_large {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*4) (hc : p.Coprime (Fintype.card H)) (hp : 5≤p) (hm : p<Fintype.card H)
    (hodd : Odd (Fintype.card H)) : False := by
  have hsp : (4:ℤ)<p := by omega
  have hnd : ¬ (p:ℤ) ∣ 4 := fun h => (not_le.mpr hsp) (Int.le_of_dvd (by decide) h)
  obtain ⟨c,i,hzero,hcor,h,hd⟩ := small_witness hf hn hnd hc (by omega) hsp
  let u := fun z => rowMass f z-c
  change ((p:ℤ)-4)*(u i)^2≤((p:ℤ)-1)*4 at h
  apply obstruction_four (by exact_mod_cast hm) hsp hodd hd
  change (u i)^2<9
  by_cases h5 : p=5
  · subst p
    have ev := self_conjugate_centered (q:=2) u hcor 2 (by decide) (by decide) (by decide) i
    have en : energy u=16 := by rw [energy_zero]; norm_num [u,hcor]
    have pk := peak_lt_energy u hzero (by omega) i
    rw [en] at pk
    obtain ⟨z,hz⟩ := ev
    have corr : (u i)^2=4*z^2 := by rw [hz]; ring
    have small : z^2<4 := by omega
    rcases small_squares z (by omega) with e|e|e <;> omega
  · have h7 : 7≤p := by
      by_contra! h'
      have pp : p.Prime := Fact.out
      have := (show p=6 by omega) ▸ pp
      exact (by decide : ¬ Nat.Prime 6) this
    by_contra! he
    have sub := mul_le_mul_of_nonneg_left he (by omega : (0:ℤ)≤(p:ℤ)-4)
    omega

#print axioms no_norm_four_times_large

end Signed39.Contraction

