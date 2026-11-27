import Quantum.Hadamard.ArithmeticSingularCompositeAux

/-! Density of all locally admissible twice-odd orders in arbitrary arithmetic
progressions, for every fixed odd modulus. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic FrobeniusConic

theorem dense_composite_twice {m a n : ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    (ap : 0 < a) (n4 : n%4=2) (eligible : TwiceLocallyAdmissible m n) (N : ℕ) :
    ∃ h>N, AtOrder m h ∧ h%4=2 ∧ h ≡ n [MOD a] := by
  classical
  obtain ⟨e,L,lo,period⟩ := Nat.exists_eq_two_pow_mul_odd (by positivity : 4*a≠0)
  let P := 2^e
  let M := m*(3*L)
  have lp : 0<L := by have h := lo.pos; omega
  have big : 1<M := by dsimp [M]; nlinarith
  have mM : m∣M := dvd_mul_right _ _
  have odd : (2:ℕ).Coprime M := om.mul_right ((by decide : (2:ℕ).Coprime 3).mul_right lo.coprime_two_left)
  have PM : P.Coprime M := odd.pow_left e
  have PP : 0<P := pow_pos (by decide) _
  obtain ⟨s,sp,S,s4,sc⟩ := twice_seed_primary_precision mp big odd mM n4 eligible
  obtain ⟨u,uo,su⟩ : ∃ u:ℕ, Odd u ∧ s=2*u := ⟨s/2,Nat.odd_iff.mpr (by omega),by omega⟩
  let w := n/2
  have nw : n=2*w := by dsimp [w]; omega
  let U := ZMod.unitOfCoprime u (uo.coprime_two_right.pow_right e)
  let j₂ := ((↑U⁻¹:ZMod P)*(w:ZMod P)).val
  have h2 : u*j₂ ≡ w [MOD P] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ P).mp
    have uv : (U:ZMod P)=(u:ZMod P) := ZMod.coe_unitOfCoprime _ _
    rw [Nat.cast_mul,show (j₂:ZMod P)=(↑U⁻¹:ZMod P)*(w:ZMod P) from ZMod.natCast_zmod_val _,
      ←uv]
    simp
  let g (p:ℕ) := if p^m.factorization p∣n then n else 4
  obtain ⟨j₁,jc⟩ := primary_congruences (by omega : 0 < M) g
  obtain ⟨cut,selector⟩ := saturated_multiplier (r:=n) mp om
  obtain ⟨z,z₂,z₁⟩ := Nat.chineseRemainder PM j₂ j₁
  let j := z+(P*M)*(N+cut+1)
  have jbig : N<j ∧ cut≤j := by
    have bound := Nat.le_mul_of_pos_left (N+cut+1) (Nat.mul_pos PP (by omega : 0 < M))
    dsimp only [j]
    omega
  have jP : j ≡ j₂ [MOD P] := by
    apply Nat.ModEq.trans _ z₂
    change (z+(P*M)*(N+cut+1))%P=z%P
    rw [show P*M*(N+cut+1)=(M*(N+cut+1))*P by ring,Nat.add_mul_mod_self_right]
  have jM : j ≡ j₁ [MOD M] := by
    apply Nat.ModEq.trans _ z₁
    change (z+(P*M)*(N+cut+1))%M=z%M
    rw [show P*M*(N+cut+1)=(P*(N+cut+1))*M by ring,Nat.add_mul_mod_self_right]
  have pjc (p:ℕ) (hp:p∈M.primeFactors) : j ≡ g p [MOD p^M.factorization p] := by
    have d := Finset.dvd_prod_of_mem (fun q=>q^M.factorization q) hp |>.trans
      (dvd_of_eq (Nat.prod_primeFactors_pow_factorization (by omega : M≠0)).symm)
    exact (jM.of_dvd d).trans (jc p hp)
  have J : AtOrder m j := by
    apply selector j jbig.2
    intro p hp
    obtain ⟨pp,pm,_⟩ := Nat.mem_primeFactors.mp hp
    have pM := Nat.mem_primeFactors.mpr ⟨pp,pm.trans mM,(by omega : M≠0)⟩
    have e0 := Finset.dvd_prod_of_mem (fun q=>q^m.factorization q) hp |>.trans
      (dvd_of_eq (Nat.prod_primeFactors_pow_factorization mp.ne').symm)
    have ef := (pp.pow_dvd_iff_le_factorization (by omega : M≠0)).mp (e0.trans mM)
    have h := (pjc p pM).of_dvd (pow_dvd_pow p ef)
    by_cases sat : p^m.factorization p∣n
    · simp only [g,sat,ite_true] at h ⊢
      exact h.trans (Nat.modEq_zero_iff_dvd.mpr sat)
    · simpa only [g,sat,ite_false] using h
  have oddCon : s*j ≡ n [MOD M] := by
    apply congr_of_all_primary (by omega)
    intro p hp
    have c := sc p hp
    have c' := pjc p hp
    by_cases sat : p^m.factorization p∣n
    · simp only [g,sat,ite_true] at c c'
      simpa using c.mul c'
    · simp only [g,sat,ite_false] at c c'
      exact ((c'.mul_left s).trans c)
  have twoCon : s*j ≡ n [MOD P] := by
    exact su ▸ nw ▸ (by simpa only [mul_assoc] using ((jP.mul_left u).trans h2).mul_left 2)
  have lM : L∣M := by exact (dvd_mul_left L 3).trans (dvd_mul_left _ m)
  have both : s*j ≡ n [MOD 4*a] := by
    rw [period]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (PM.of_dvd_right lM)).mp ⟨twoCon,oddCon.of_dvd lM⟩
  have huge := Nat.le_mul_of_pos_left j sp
  refine ⟨s*j,by omega,at_mul S J,?_,both.of_dvd (dvd_mul_left a 4)⟩
  have h := both.of_dvd (dvd_mul_right 4 a)
  change (s*j)%4=n%4 at h
  omega

#print axioms dense_composite_twice
end HadamardMod
