import DeterminantalGraph
import DeterminantalColumns
import DeterminantalDerivative
import PermanentSlice
import Mathlib.Algebra.CharP.Algebra

/-! The explicit permanent slice excludes a determinantal representation
whose polynomial matrix has two zero rows at the origin. -/
noncomputable section
namespace PermanentFive
open MvPolynomial Matrix DeterminantalRegularity DeterminantalRegularity.RankParam

private def restrictSlice (K : Type*) [Field K] : MvPolynomial Cell K →+* MvPolynomial Idx K :=
  eval₂Hom C (slice (fun i ↦ X i))

private theorem slice_origin (K : Type*) [Field K] :
    (MvPolynomial.eval 0).comp (restrictSlice K) = (MvPolynomial.eval 0 : MvPolynomial Cell K →+* K) := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp [restrictSlice]
  · intro i
    by_cases h : i.2 ≠ 2*i.1 <;> simp [restrictSlice,slice,h]

private theorem per_map {K S : Type*} [CommRing K] [CommRing S] (f : K →+* S) :
    MvPolynomial.map f (per K Idx) = per S Idx := by
  simp [per,Matrix.permanent,PermanentCuts.generic]

private theorem partial_basechange {K S : Type*} [CommRing K] [CommRing S] (f : K →+* S)
    (z : Cell → S) (e : Cell) :
    eval₂Hom f z (pderiv e (per K Idx)) = MvPolynomial.eval z (pderiv e (per S Idx)) := by
  rw [← per_map f,pderiv_map,eval_map]
  rfl

variable (K : Type*) [Field K] [CharZero K] (H : Type*) [Fintype H] [DecidableEq H]

/-- Even polynomial entries cannot represent a nonzero constant multiple
of the permanent if the two bottom rows vanish at the origin. -/
theorem no_two_zero_rows (P : Matrix (Slot H) (Slot H) (MvPolynomial Cell K))
    (A : Matrix H (Slot H) K)
    (at0 : ∀ i j, MvPolynomial.eval 0 (P i j) = fullOrigin K H A i j)
    (c : K) (hc : c ≠ 0) (rep : P.det = C c * per K Idx) : False := by
  let L := (restrictSlice K).mapMatrix P
  have zeroL (i j : Slot H) : MvPolynomial.eval 0 (L i j) = fullOrigin K H A i j := by
    change ((MvPolynomial.eval 0).comp (restrictSlice K)) (P i j) = _
    rw [slice_origin,at0]
  apply (by decide : ¬ Fintype.card Idx ≤ 4)
  apply isolated_graph_card_le K Idx H L A zeroL
  intro J prime contain
  let : J.IsPrime := prime
  let q := Ideal.Quotient.mk J
  let k := q.comp (ground K Idx H)
  let : CharZero (Coord K Idx H ⧸ J) := charZero_of_injective_ringHom k.injective
  let u := fun i ↦ q (input K Idx H i)
  let f := (evalInput K Idx H).comp (restrictSlice K)
  have map_eq : q.comp f = eval₂Hom k (slice u) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [f,evalInput,restrictSlice,k]
    · intro e
      by_cases h : e.2 ≠ 2*e.1 <;> simp [f,evalInput,restrictSlice,slice,h,u]
  have grad (e : Cell) : MvPolynomial.eval (slice u) (pderiv e (per (Coord K Idx H ⧸ J) Idx)) = 0 := by
    have deriv : (q.comp f) (pderiv e P.det) = 0 := by
      rw [derivative_determinant,map_sum]
      apply Finset.sum_eq_zero
      intro j _
      let v := fun i ↦ f (pderiv e (P i j))
      have mapeq : (q.comp f).mapMatrix (P.updateCol j (fun i ↦ pderiv e (P i j))) =
          q.mapMatrix ((entry K Idx H).updateCol j v) := by
        apply Matrix.ext
        intro i l
        by_cases h : l = j
        · subst l; simp [v]
        · simpa [h,f,L,q] using (quotient_entry K Idx H L contain i l).symm
      rw [RingHom.map_det,mapeq,← RingHom.map_det,column_zero,map_zero]
    rw [rep,pderiv_mul,pderiv_C,zero_mul,zero_add,map_mul,map_eq] at deriv
    rw [MvPolynomial.eval₂Hom_C,partial_basechange] at deriv
    exact (mul_eq_zero.mp deriv).resolve_left ((map_ne_zero k).mpr hc)
  have allzero := slice_isolated u grad
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun allzero i)

#print axioms no_two_zero_rows
end PermanentFive
