module
public import Mathlib

/-! An elementary integer-polynomial bound for an exponent in a rational
Krylov orbit. A long gap above a polynomial's low part forces divisibility
of its leading coefficient by successive powers of a prime. -/
@[expose] public section
noncomputable section
namespace RationalOrbit
open Polynomial

variable {p : ℕ} [Fact (Nat.Prime p)]

abbrev red (p : ℕ) := Int.castRingHom (ZMod p)

private theorem coefficient_divisor (D S : ℤ[X]) (A : ℤ) (k : ℕ) (hA : A≠0)
    (hk : S.natDegree<k) (hd : D ∣ C A*X^k+S) (hp : (p:ℤ)∣D.leadingCoeff) :
    (p:ℤ)∣A := by
  obtain ⟨Q,hQ⟩ := hd
  have e : (C A*X^k+S).leadingCoeff=A := by
    rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree (by rwa [natDegree_C_mul_X_pow k A hA]))]
    rw [leadingCoeff_mul,leadingCoeff_X_pow,leadingCoeff_C,mul_one]
  rw [hQ,leadingCoeff_mul] at e
  rw [← e]
  exact dvd_mul_of_dvd_left hp _

private theorem split_mod (D Q F : ℤ[X]) (hD : D.map (red p)≠0)
    (h : F.map (red p)=D.map (red p)*Q.map (red p)) :
    ∃ L Z : ℤ[X], Q=L+C (p:ℤ)*Z ∧
      (L=0 ∨ L.natDegree+(D.map (red p)).natDegree≤F.natDegree) := by
  by_cases hQ : Q.map (red p)=0
  · have dv : C (p:ℤ) ∣ Q := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      change red p (Q.coeff i)=0
      rw [← coeff_map,hQ,coeff_zero]
    obtain ⟨Z,hZ⟩ := dv
    exact ⟨0,Z,by simpa using hZ,Or.inl rfl⟩
  have lifts : Q.map (red p) ∈ Polynomial.lifts (red p) := (mem_lifts _).mpr ⟨Q,rfl⟩
  obtain ⟨L,hL,deg⟩ := exists_natDegree_eq_of_mem_lifts lifts
  have div : C (p:ℤ) ∣ Q-L := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    change red p ((Q-L).coeff i)=0
    rw [← coeff_map,Polynomial.map_sub,hL,sub_self,coeff_zero]
  obtain ⟨Z,hZ⟩ := div
  refine ⟨L,Z,by linear_combination hZ,?_⟩
  right
  rw [deg]
  have de := congrArg natDegree h
  rw [natDegree_mul hD hQ] at de
  have upper : (F.map (red p)).natDegree≤F.natDegree := natDegree_map_le
  omega

/-- If a primitive divisor loses its leading coefficient modulo p, a possible
orbit exponent is bounded by the low degree plus the degree lost modulo p
times the p-adic valuation of the scalar clearing the target coordinates. -/
theorem gap_bound_sharp (D : ℤ[X]) (hD : D.map (red p)≠0) (lead : (p:ℤ)∣D.leadingCoeff)
    (k t : ℕ) (A : ℤ) (S : ℤ[X]) (hA : ¬(p:ℤ)^(t+1)∣A)
    (dvd : D ∣ C A*X^k+S) :
    k≤S.natDegree+t*(D.natDegree-(D.map (red p)).natDegree) := by
  induction t generalizing A S with
  | zero =>
    simp only [zero_mul,add_zero]
    by_contra! hk
    have hn : A≠0 := fun hz => hA (hz ▸ dvd_zero _)
    apply hA
    simpa using coefficient_divisor D S A k hn hk dvd lead
  | succ t ih =>
    by_cases hk : k≤S.natDegree
    · omega
    have hn : A≠0 := fun hz => hA (hz ▸ dvd_zero _)
    obtain ⟨B,hB⟩ := coefficient_divisor D S A k hn (by omega) dvd lead
    obtain ⟨Q,hQ⟩ := dvd
    have hmod : S.map (red p)=D.map (red p)*Q.map (red p) := by
      have v := congrArg (Polynomial.map (red p)) hQ
      simpa [hB,red] using v
    obtain ⟨L,Z,eq,deg⟩ := split_mod D Q S hD hmod
    let F := D*Z-C B*X^k
    have scaled : C (p:ℤ)*F=S-D*L := by
      rw [hB,eq,map_mul] at hQ
      dsimp only [F]
      linear_combination -hQ
    have hnp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have fdeg : F.natDegree≤S.natDegree+(D.natDegree-(D.map (red p)).natDegree) := by
      rw [← natDegree_C_mul (p := F) hnp,scaled]
      rcases deg with zero | small
      · simp [zero]
      · have muldeg := natDegree_mul_le (p := D) (q := L)
        exact (natDegree_sub_le _ _).trans (by omega)
    have bh : ¬(p:ℤ)^(t+1) ∣ B := by
      rintro ⟨a,ha⟩
      apply hA
      exact ⟨a,by rw [hB,ha,pow_succ']; ring⟩
    have newdiv : D∣C B*X^k+F := ⟨Z,by dsimp only [F]; ring⟩
    have bound := ih B F bh newdiv
    rw [Nat.succ_mul]
    omega

theorem gap_bound (D : ℤ[X]) (hD : D.map (red p)≠0) (lead : (p:ℤ)∣D.leadingCoeff)
    (k t : ℕ) (A : ℤ) (S : ℤ[X]) (hA : ¬(p:ℤ)^(t+1)∣A)
    (dvd : D ∣ C A*X^k+S) : k≤S.natDegree+t*D.natDegree :=
  (gap_bound_sharp D hD lead k t A S hA dvd).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left t (Nat.sub_le _ _)) _)

#print axioms gap_bound_sharp
#print axioms gap_bound
end RationalOrbit
