import Quantum.Hadamard.TorusOddCompositeLocal
import Quantum.Hadamard.ArithmeticSingularCompositeSelectors
import Quantum.Hadamard.ArithmeticSingularSeeds
import Quantum.Hadamard.Weaken

/-! Every square residue of an odd modulus has modular Hadamard orders in
every compatible arithmetic progression. The progression may have even period. -/
noncomputable section
namespace HadamardMod.TorusOddComposite
open Hadamard.Arithmetic FrobeniusConic

private theorem local_data {m L n p:ℕ} (om:(2:ℕ).Coprime L) (hp:p∈L.primeFactors)
    (square:IsSquare (n:ZMod m)) :
    ∃ x:ℕ, x^2*(if p^m.factorization p∣n then n else 4) ≡ n [MOD p^L.factorization p] := by
  classical
  by_cases saturated : p^m.factorization p ∣ n
  · exact ⟨1,by simpa only [if_pos saturated,one_pow,one_mul] using (Nat.ModEq.refl n)⟩
  rw [if_neg saturated]
  have pp := Nat.prime_of_mem_primeFactors hp
  have pn : p≠2 := fun e => Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2) (dvd_refl _)
    (e ▸ Nat.dvd_of_mem_primeFactors hp) om
  let M:=p^L.factorization p
  letI : NeZero M := ⟨pow_ne_zero _ pp.ne_zero⟩
  have sm : IsSquare (n:ZMod (p^m.factorization p)) := by
    simpa only [map_natCast] using square.map (ZMod.castHom (Nat.ordProj_dvd m p) (ZMod (p^m.factorization p)))
  obtain ⟨r,rr⟩ := lift_nonzero_square (f:=L.factorization p) pp (by have := pp.two_le;omega) saturated sm
  let u := ZMod.unitOfCoprime 2 (om.of_dvd_right (Nat.ordProj_dvd L p))
  let y : ZMod M := (↑u⁻¹:ZMod M)*r
  have hu : (↑u:ZMod M)=2 := ZMod.coe_unitOfCoprime _ _
  have hy : (2:ZMod M)*y=r := by rw [←hu];change (u:ZMod M)*((↑u⁻¹:ZMod M)*r)=r;rw [←mul_assoc,Units.mul_inv,one_mul]
  refine ⟨y.val,(ZMod.natCast_eq_natCast_iff _ _ M).mp ?_⟩
  change (((y.val^2*4:ℕ):ZMod M))=(n:ZMod M)
  push_cast
  rw [ZMod.natCast_zmod_val,show y^2*4=(2*y)^2 by ring,hy,pow_two]
  exact rr.symm

/-- A positive matrix order in every progression above a square class. -/
theorem odd_square_dense {m A n:ℕ} (mp : 0 < m) (om:(2:ℕ).Coprime m) (ap : 0 < A)
    (ma:m∣A) (sq:IsSquare (n:ZMod m)) :
    ∃ h>0, AtOrder m h ∧ h ≡ n [MOD A] := by
  classical
  by_cases one:m=1
  · subst m
    exact ⟨n+A,by omega,ones (Subsingleton.elim _ _),by simp [Nat.ModEq]⟩
  have mh : 1 < m := by omega
  obtain ⟨e,L,lo,aEq⟩ := Nat.exists_eq_two_pow_mul_odd ap.ne'
  have Lp : 0<L := by by_contra! h; rw [Nat.le_zero.mp h,mul_zero] at aEq;omega
  have mL : m∣L := (om.symm.pow_right e).dvd_of_dvd_mul_left (aEq ▸ ma)
  have Le : 1<L := mh.trans_le (Nat.le_of_dvd Lp mL)
  let d := 2^e
  have dp : 0<d := pow_pos (by decide) _
  let value (p:ℕ) := if p^m.factorization p∣n then n else 4
  choose root spec using (fun p : L.primeFactors => local_data lo.coprime_two_left p.property sq)
  let g (p:ℕ) := if h:p∈L.primeFactors then root ⟨p,h⟩ else 0
  obtain ⟨x,hx⟩ := primary_congruences Lp g
  obtain ⟨z,hz⟩ := primary_congruences Lp value
  have product : x^2*z ≡ n [MOD L] := by
    apply congr_of_all_primary Lp
    intro p hp
    have a := ((hx p hp).pow 2).mul (hz p hp)
    exact a.trans (by simpa only [g,dif_pos hp,value] using spec ⟨p,hp⟩)
  have sx : IsSquare ((x^2:ℕ):ZMod L) := ⟨(x:ZMod L),by push_cast;ring⟩
  obtain ⟨h,hp,H,h4,hl⟩ := square_seed_each_mod_four Le lo.coprime_two_left sx (1:Fin 4)
  have oh : Odd h := Nat.odd_iff.mpr (by
    change h%4=1%4 at h4
    omega)
  have dh : h.Coprime d := oh.coprime_two_left.symm.pow_right e
  let hu := ZMod.unitOfCoprime h dh
  let y : ZMod d := (↑hu⁻¹:ZMod d)*(n:ZMod d)
  have hy : h*y.val ≡ n [MOD d] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hhu : (hu:ZMod d)=(h:ZMod d) := ZMod.coe_unitOfCoprime _ _
    rw [Nat.cast_mul,ZMod.natCast_zmod_val,←hhu]
    simp [y,mul_assoc]
  have cop : d.Coprime L := lo.coprime_two_left.pow_left e
  obtain ⟨j0,jd,jL⟩ := Nat.chineseRemainder cop y.val z
  obtain ⟨N,base⟩ := saturated_multiplier (r:=n) mp om
  let j:=j0+A*(N+1)
  have big : N<j := by dsimp [j];nlinarith
  have ja : j ≡ j0 [MOD A] := by simp [j,Nat.ModEq]
  have dA : d∣A := aEq ▸ dvd_mul_right d L
  have LA : L∣A := aEq ▸ dvd_mul_left L d
  have js : j ≡ z [MOD L] := (ja.of_dvd LA).trans jL
  have J : AtOrder m j := base j big.le (by
    intro p pm
    have pp:=Nat.prime_of_mem_primeFactors pm
    have pL:=Nat.mem_primeFactors.mpr ⟨pp,(Nat.dvd_of_mem_primeFactors pm).trans mL,Lp.ne'⟩
    have le := (Nat.factorization_le_iff_dvd mp.ne' Lp.ne').mpr mL p
    have c : j ≡ value p [MOD p^m.factorization p] :=
      ((js.of_dvd (Nat.ordProj_dvd L p)).trans (hz p pL)).of_dvd (pow_dvd_pow p le)
    by_cases full:p^m.factorization p∣n
    · rw [if_pos full]
      have cn : j ≡ n [MOD p^m.factorization p] := by simpa only [value,if_pos full] using c
      exact cn.trans (Nat.modEq_zero_iff_dvd.mpr full)
    · simpa [value,full] using c)
  refine ⟨h*j,Nat.mul_pos hp (by omega),at_mul (at_weaker_modulus mL H) J,?_⟩
  rw [aEq]
  exact (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
    ⟨(((ja.of_dvd dA).trans jd).mul_left h).trans hy,(hl.mul js).trans product⟩

#print axioms odd_square_dense
end HadamardMod.TorusOddComposite


