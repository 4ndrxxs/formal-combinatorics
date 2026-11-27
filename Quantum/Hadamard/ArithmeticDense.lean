import Quantum.Hadamard.ArithmeticDensePrimes
import Quantum.Hadamard.ArithmeticSelector
import Quantum.Hadamard.PaleySecond

/-! A modular Hadamard order in every arithmetic progression of multiples
of four. The first tensor factor supplies an extra factor of four in the
Gram divisibility of the second tensor factor. -/
noncomputable section
namespace HadamardMod
open Finset Hadamard.Arithmetic

theorem at_mul_raise {a b m t : ℕ} (X : AtOrder (t*m) a)
    (Y : AtOrder m b) (div : t ∣ a) : AtOrder (t*m) (a*b) := by
  classical
  obtain ⟨A,g⟩ := X
  obtain ⟨B,sign,gram⟩ := integer_gram Y
  let C : RowMatrix (t*m) (Fin b) := fun i j => (B i j : ZMod (t*m))
  have sc (i j) : Sign (C i j) := by
    rcases sign i j with h|h <;> simp [Sign,C,h]
  have off (i k : Fin b) (ne : i≠k) :
      (a : ZMod (t*m))*(∑ j, C i j*C k j)=0 := by
    have db : (m : ℤ) ∣ ∑ j, B i j*B k j := by
      simpa [Matrix.mul_apply,Matrix.transpose_apply,ne] using gram i k
    have da : (t : ℤ) ∣ (a : ℤ) := by exact_mod_cast div
    have dd : ((t*m : ℕ) : ℤ) ∣ (a : ℤ)*(∑ j, B i j*B k j) := by
      simpa using mul_dvd_mul da db
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (t*m)).mpr dd
    push_cast at z
    exact z
  have ds : Good (fun i j : Fin a × Fin b => A i.1 j.1*C i.2 j.2) := by
    refine ⟨fun i j => sign_mul (g.sign _ _) (sc _ _),?_⟩
    rintro ⟨i,u⟩ ⟨k,v⟩ ne
    rw [Fintype.sum_prod_type]
    dsimp only
    have fac (j l) : A i j*C u l*(A k j*C v l)=(A i j*A k j)*(C u l*C v l) := by ring
    simp only [fac,← mul_sum,← sum_mul]
    by_cases same : i=k
    · subst k
      rw [g.norm_rows,Fintype.card_fin]
      exact off u v (fun eq => ne (Prod.ext rfl eq))
    · rw [g.ortho _ _ same,zero_mul]
  exact of_card ds (by simp)

private theorem dense_aux {b T w factor N : ℕ} (bp : 0 < b) (odd : (2 : ℕ).Coprime b)
    (tp : 0 < T) (hl : factor=2 ∨ factor=4) (h3 : (factor*w)%3≠1) :
    ∃ h > N, AtOrder (4*b) h ∧ h ≡ 4*w [MOD 4*T] := by
  have h2 : (factor*w)%2=0 := by rcases hl with hh|hh <;> simp [hh,Nat.mul_mod]
  obtain ⟨q,hb,s,hs,pq,ps,cq,con⟩ := square_times_successor (L := 4*T)
    (by omega) h2 h3 b (max N 2)
  haveI : Fact q.Prime := ⟨pq⟩
  haveI : Fact s.Prime := ⟨ps⟩
  have sq : AtOrder b (q^2) := by
    by_cases b1 : b=1
    · subst b
      exact ones (Subsingleton.elim _ _)
    · simpa using prime_power_affine (p := q) (e := 1) (by omega) odd (by decide) (by simpa using hb.le)
  have s2 : 2 < s := by omega
  have os := ps.odd_of_ne_two (by omega : s≠2)
  have op : s%4=1 ∨ s%4=3 := by obtain ⟨k,hk⟩ := os; omega
  have finish {d : ℕ} (mat : AtOrder (4*b) d) (div : 4 ∣ d)
      (low : N < d) (cong : d*q^2 ≡ 4*w [MOD 4*T]) :
      ∃ h > N, AtOrder (4*b) h ∧ h ≡ 4*w [MOD 4*T] := by
    have qpos := pq.pos
    have qs : 0 < q^2 := pow_pos qpos _
    exact ⟨d*q^2,low.trans_le (Nat.le_mul_of_pos_right d qs),
      at_mul_raise mat sq div,cong⟩
  rcases hl with l2|l4
  · subst factor
    have mat : AtOrder (4*b) (2*(s+1)) := op.elim (paley_second _ _) (paley_double _ _)
    obtain ⟨k,hk⟩ := os
    refine finish mat ⟨k+1,by omega⟩ (by omega) ?_
    convert con.mul_left 2 using 1 <;> ring
  · subst factor
    have c2 : q.Coprime 2 := cq.of_dvd_right (by exact ⟨2*T,by ring⟩)
    have qo := Nat.coprime_two_right.mp c2
    have qfour : q^2 ≡ 1 [MOD 4] := by
      obtain ⟨k,hk⟩ := qo
      rw [hk, show (2*k+1)^2=1+4*(k^2+k) by ring]
      simp [Nat.ModEq]
    have s4 : s%4=3 := by
      have eq := (qfour.mul_right (s+1)).symm.trans (con.of_dvd (dvd_mul_right 4 T))
      simp [Nat.ModEq] at eq
      omega
    have div : 4 ∣ s+1 := Nat.dvd_of_mod_eq_zero (by omega)
    exact finish (paley_order _ _ s4) div (by omega) (by simpa [mul_comm] using con)

/-- Fixed positive odd b, arbitrary period and arbitrary class of multiples
of four, with an arbitrarily large order in that class. -/
theorem dense_four_seeds {b T : ℕ} (bp : 0 < b) (odd : (2 : ℕ).Coprime b)
    (tp : 0 < T) (w N : ℕ) : ∃ h > N, AtOrder (4*b) h ∧ h ≡ 4*w [MOD 4*T] := by
  by_cases e : w%3=1
  · exact dense_aux (factor := 2) bp odd tp (Or.inl rfl) (by omega)
  · exact dense_aux (factor := 4) bp odd tp (Or.inr rfl) (by omega)

#print axioms dense_four_seeds
end HadamardMod
