import PermanentAttainedRank
import PermanentFourEuler
import PermanentBinaryFixedOrder

/-! The exact maximum ordinary Hessian rank on smooth permanent zeros of
every order over an infinite field, with the Euler drop in positive characteristic. -/
noncomputable section
open Matrix Finset MvPolynomial PermanentFive PermanentBorder QuinticPencil PermanentOrderThree
namespace PermanentMaximum
variable {K : Type*} [Field K]

def target (K : Type*) [Field K] (m : ℕ) : ℕ := by
  classical
  exact if (2:K)=0 then 2*m else if ((m-1:ℕ):K)=0 then m^2-1 else m^2

private theorem width (m : ℕ) (z : CellOf (Fin m)→K) : (hessian (per K (Fin m)) z).rank≤m^2 := by
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using Matrix.rank_le_card_width (hessian (per K (Fin m)) z)

theorem euler_cap (m : ℕ) (size : 2≤m) (bad : ((m-1:ℕ):K)=0) (z : CellOf (Fin m)→K)
    (smooth : cofactor z≠0) : (hessian (per K (Fin m)) z).rank≤m^2-1 := by
  let A := hessian (per K (Fin m)) z
  have ker := PermanentOrderFour.euler_hessian (per_homogeneous K (Fin m)) z
  simp only [Fintype.card_fin,bad,zero_mul] at ker
  have nz : z≠0 := by
    rintro rfl
    apply smooth
    ext i j
    exact DeterminantHessian.grad_zero_two_rows _ (⟨0,by omega⟩:Fin m) ⟨1,by omega⟩
      (by intro q; have := congrArg Fin.val q; contradiction) (fun _ ↦ rfl) (fun _ ↦ rfl) (i,j)
  by_contra! greater
  have hw := width m z
  have eq : A.rank=Fintype.card (CellOf (Fin m)) := by
    simp only [CellOf,Fintype.card_prod,Fintype.card_fin,←pow_two]
    change A.rank≤m^2 at hw
    change m^2-1<A.rank at greater
    omega
  have onto : Function.Surjective A.mulVecLin := Matrix.mulVec_surjective_iff_rank_eq_card.mpr eq
  exact nz ((LinearMap.injective_iff_surjective.mpr onto) (ker.trans (map_zero A.mulVecLin).symm))

theorem upper (m : ℕ) (size : 2≤m) {s : ℕ} (h : AtOrder K m s) : s≤target K m := by
  by_cases two : (2:K)=0
  · rw [target,ite_eq_left two]
    exact ((DeterminantHessian.fixed_binary_smooth two m s size).mp h).le
  obtain ⟨z,_,sm,rfl⟩ := h
  by_cases bad : ((m-1:ℕ):K)=0
  · simpa only [target,ite_eq_right two,ite_eq_left bad] using euler_cap m size bad z sm
  · simpa only [target,ite_eq_right two,ite_eq_right bad] using width m z

open PermanentDeformation in
private theorem fin_witness [Infinite K] {J S : Type*} [Fintype J] [DecidableEq J]
    [Fintype S] [DecidableEq S] [Nonempty J] (two : (2:K)≠0) (m : ℕ) (sz : Fintype.card J+2=m)
    (f : S↪J) (minor : (gram K J S).det≠0) :
    ∃ r, AtOrder K m r ∧ m^2-m+2+Fintype.card S≤r := by
  obtain ⟨z,flat,sm,h⟩ := attained_by_minor two f minor
  let e : Option (Option J)≃Fin m := Fintype.equivOfCardEq (by simpa [Nat.add_assoc] using sz)
  let u := z ∘ (e.prodCongr e).symm
  have usm : cofactor u≠0 := by
    intro hu
    have hzero := congrFun (congrFun hu (e none)) (e none)
    have tr := transport_gradient e z corner
    apply sm
    exact tr.symm.trans hzero
  refine ⟨(hessian (per K _) u).rank,⟨u,(transport_value e z).trans flat,usm,rfl⟩,?_⟩
  rw [transport_rank]
  simpa only [sz] using h

theorem attained [Infinite K] (m : ℕ) (size : 2≤m) : AtOrder K m (target K m) := by
  classical
  by_cases binary : (2:K)=0
  · apply (DeterminantHessian.fixed_binary_smooth binary _ _ size).mpr
    simp [target,binary]
  by_cases small : m=2
  · subst m
    let o : Fin 2 := 0
    obtain ⟨h,sm,r⟩ := PermanentArrow.bedi_suagee binary o (by decide)
    refine ⟨_,h,?_,?_⟩
    · intro hz
      have t := congrFun (congrFun hz o) o
      exact one_ne_zero (sm.symm.trans t)
    · simpa [target,binary] using r
  obtain ⟨k,rfl⟩ : ∃ k,m=k+3 := ⟨m-3,by omega⟩
  let J := Fin (k+1)
  have sz : Fintype.card J+2=k+3 := by simp [J,Nat.add_assoc]
  have same : (((k+3-1:ℕ):K))=(Fintype.card J:K)+1 := by simp [J];ring
  have ar : k+3≤(k+3)^2 := Nat.le_self_pow (by decide) _
  by_cases bad : ((k+3-1:ℕ):K)=0
  · have vanish := same.symm.trans bad
    have mi := PermanentDeformation.gram_deleted (J:=J) (S:=Fin k) binary vanish (by simp [J])
    obtain ⟨r,hr,le⟩ := fin_witness binary _ sz (Fin.castSuccEmb : Fin k↪J) mi
    have cap := upper _ (by omega) hr
    simp only [target,ite_eq_right binary,ite_eq_left bad] at cap ⊢
    rw [Fintype.card_fin] at le
    convert hr using 2
    omega
  · have good : (Fintype.card J:K)+1≠0 := fun q ↦ bad (same.trans q)
    obtain ⟨r,hr,le⟩ := fin_witness binary _ sz (Function.Embedding.refl J) (PermanentDeformation.gram_full binary good)
    have cap := upper _ (by omega) hr
    simp only [target,ite_eq_right binary,ite_eq_right bad] at cap ⊢
    simp only [J,Fintype.card_fin] at le
    convert hr using 2
    omega

theorem maximum_smooth_hessian_rank [Infinite K] (m : ℕ) (size : 2≤m) :
    IsGreatest {r : ℕ | AtOrder K m r} (target K m) :=
  ⟨attained m size,fun _ h ↦ upper m size h⟩

#print axioms maximum_smooth_hessian_rank
end PermanentMaximum
