import Quantum.Hadamard.ArithmeticBase
import Mathlib

/-! Prime progressions for dense modular Hadamard orders. -/
namespace Hadamard.Arithmetic

private theorem prime_avoiding_square {L R : ℕ} (hL : 1 < L)
    (h2 : R%2=0) (h3 : R%3≠1) (B : ℕ) :
    ∃ q > B, q.Prime ∧ q.Coprime L ∧
      ∀ s, s.Prime → s ∣ L → ¬q^2 ≡ R [MOD s] := by
  classical
  let a (s : ℕ) := if R%s=1 then 2 else 1
  have ppos (s : ℕ) (hs : s ∈ L.primeFactors) := (Nat.mem_primeFactors.mp hs).1
  have pp : Set.Pairwise (↑L.primeFactors : Set ℕ) (fun s t => s.Coprime t) := by
    intro s hs t ht ne
    exact (Nat.coprime_primes (ppos _ hs) (ppos _ ht)).mpr ne
  obtain ⟨z,hz⟩ := Nat.chineseRemainderOfFinset a id L.primeFactors
    (fun s hs => (ppos s hs).ne_zero) pp
  have large (s : ℕ) (hs : s.Prime) (eq : R%s=1) : 3 < s := by
    have l := hs.two_le
    by_contra! hl
    have : s=2 ∨ s=3 := by omega
    rcases this with h|h <;> subst s <;> omega
  have cz : z.Coprime L := by
    by_contra bad
    obtain ⟨s,hs,sz,sl⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have H := hz s (Nat.mem_primeFactors.mpr ⟨hs,sl,by omega⟩)
    change z%s=a s%s at H
    have zz := Nat.mod_eq_zero_of_dvd sz
    by_cases eq : R%s=1
    · have ls := large s hs eq
      simp [a,eq,Nat.mod_eq_of_lt (show 2 < s by omega),zz] at H
    · simp [a,eq,Nat.mod_eq_of_lt hs.one_lt,zz] at H
  obtain ⟨q,hB,hq,qz⟩ := Nat.forall_exists_prime_gt_and_modEq B (by omega : L≠0) cz
  refine ⟨q,hB,hq,coprime_of_modEq qz cz,?_⟩
  intro s hs sl bad
  have H := hz s (Nat.mem_primeFactors.mpr ⟨hs,sl,by omega⟩)
  change z ≡ a s [MOD s] at H
  have eqsq := (((qz.of_dvd sl).trans H).pow 2).symm.trans bad
  by_cases eq : R%s=1
  · have ls := large s hs eq
    have hfour : 4 ≡ 1 [MOD s] := by
      change 4%s=1%s
      simpa [Nat.ModEq,a,eq,Nat.mod_eq_of_lt hs.one_lt] using eqsq
    have dv : s ∣ 3 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 4)).mp hfour.symm
    exact Nat.not_dvd_of_pos_of_lt (by decide) ls dv
  · apply eq
    simpa [Nat.ModEq,a,eq,Nat.mod_eq_of_lt hs.one_lt] using eqsq.symm

/-- Choose two arbitrarily large primes with their square and successor
realizing a possibly nonunit even target. -/
theorem square_times_successor {L R : ℕ} (hL : 1 < L)
    (h2 : R%2=0) (h3 : R%3≠1) (B N : ℕ) :
    ∃ q > B, ∃ s > N, q.Prime ∧ s.Prime ∧ q.Coprime L ∧
      q^2*(s+1) ≡ R [MOD L] := by
  obtain ⟨q,hq,pq,cq,avoid⟩ := prime_avoiding_square hL h2 h3 B
  let A := R+q^2*(L-1)
  have ident : A+q^2=R+q^2*L := by
    dsimp [A]
    rw [add_assoc,← Nat.mul_add_one]
    congr 2
    omega
  have residue : A+q^2 ≡ R [MOD L] := by simp [ident,Nat.ModEq]
  have cA : A.Coprime L := by
    by_contra bad
    obtain ⟨p,hp,pa,pl⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    apply avoid p hp pl
    have az := (Nat.modEq_zero_iff_dvd.mpr pa).add_right (q^2)
    simpa using az.symm.trans (residue.of_dvd pl)
  obtain ⟨i,_,hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime (cq.pow_left 2) hL
  have inv : q^2*i ≡ 1 [MOD L] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hL] using hi
  have ci : i.Coprime L := Nat.coprime_of_mul_modEq_one (q^2) (by simpa [mul_comm] using inv)
  obtain ⟨s,hs,ps,con⟩ := Nat.forall_exists_prime_gt_and_modEq N (by omega : L≠0) (cA.mul_left ci)
  refine ⟨q,hq,s,hs,pq,ps,cq,?_⟩
  calc
    q^2*(s+1) ≡ q^2*(A*i+1) [MOD L] := (con.add_right 1).mul_left _
    _ = (q^2*i)*A+q^2 := by ring
    _ ≡ 1*A+q^2 [MOD L] := (inv.mul_right A).add_right _
    _ ≡ R [MOD L] := by simpa using residue

end Hadamard.Arithmetic
