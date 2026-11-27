module

public import Quantum.Exact

/-! Cardinality bounds for quantum Latin squares and exclusion of n+1 rays.
The argument only uses the orthonormal bases formed by the rows. -/

@[expose] public section

namespace QuantumCertificate

open Finset
open scoped BigOperators

private abbrev ONB (n : ℕ) := OrthonormalBasis (Fin n) ℂ (Space n)

private noncomputable def basisRay {n : ℕ} (b : ONB n) (i : Fin n) :=
  Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i)

private theorem basisRay_injective {n : ℕ} (b : ONB n) : Function.Injective (basisRay b) := by
  intro i j he
  by_contra hij
  obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  have h := congrArg (fun x : Space n => inner ℂ (b i) x) ht
  simp [inner_smul_right, b.inner_eq_ite, hij] at h

private theorem ray_when_orthogonal_except {n : ℕ} (b : ONB n)
    (v : Space n) (hv : v ≠ 0) (j : Fin n)
    (h : ∀ k, k ≠ j → inner ℂ (b k) v = 0) :
    Projectivization.mk ℂ v hv = basisRay b j := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨inner ℂ (b j) v, ?_⟩
  calc inner ℂ (b j) v • b j = ∑ k, inner ℂ (b k) v • b k := by
        symm
        apply Finset.sum_eq_single j
        · intro k _ hk
          simp [h k hk]
        · simp
    _ = v := b.sum_repr' v

private theorem row_card_bounds {n : ℕ} [NeZero n] (b : Fin n → ONB n) :
    let f := fun p : Cell n => basisRay (b p.1) p.2
    let c := (Set.range f).ncard
    n ≤ c ∧ c ≤ n^2 ∧ c ≠ n+1 := by
  classical
  let f := fun p : Cell n => basisRay (b p.1) p.2
  let cells := Finset.univ.image f
  let row := fun i => Finset.univ.image (basisRay (b i))
  have hcard : cells.card = (Set.range f).ncard := by
    rw [← Set.ncard_coe_finset]
    simp [cells]
  have rcard (i : Fin n) : (row i).card = n := by
    simp [row, Finset.card_image_of_injective _ (basisRay_injective _)]
  have rsub (i : Fin n) : row i ⊆ cells := by
    intro q hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨(i,j), by simp, rfl⟩
  change n ≤ (Set.range f).ncard ∧ (Set.range f).ncard ≤ n^2 ∧ (Set.range f).ncard ≠ n+1
  rw [← hcard]
  have lo := Finset.card_le_card (rsub 0)
  rw [rcard] at lo
  refine ⟨lo, ?_, ?_⟩
  · simpa [cells, Cell, pow_two] using (Finset.card_image_le (f:=f) (s:=Finset.univ))
  intro hn
  obtain ⟨q,hqc,hq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (row 0).card < cells.card by rw [rcard, hn]; omega)
  obtain ⟨⟨i,j⟩,_,hqpos⟩ := Finset.mem_image.mp hqc
  change basisRay (b i) j = q at hqpos
  have hqrow : q ∈ row i := Finset.mem_image.mpr ⟨j,by simp,hqpos⟩
  have hnsub : ¬ row 0 ⊆ row i := by
    intro hs
    have eq := Finset.eq_of_subset_of_card_le hs (by rw [rcard,rcard])
    exact hq (eq ▸ hqrow)
  obtain ⟨p,hp0,hpi⟩ := Finset.not_subset.mp hnsub
  obtain ⟨k,_,hkp⟩ := Finset.mem_image.mp hp0
  have huniq : cells \ row i = {p} := by
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp (show (cells \ row i).card = 1 by
      rw [Finset.card_sdiff_of_subset (rsub i), hn, rcard]; omega)
    have hp : p ∈ cells \ row i := Finset.mem_sdiff.mpr ⟨rsub 0 hp0,hpi⟩
    rw [hx, Finset.mem_singleton] at hp
    rwa [← hp] at hx
  have hqk : basisRay (b i) j = basisRay (b 0) k := by
    apply ray_when_orthogonal_except (b 0) ((b i) j) ((b i).orthonormal.ne_zero j) k
    intro l hl
    have hl0 : basisRay (b 0) l ∈ row 0 := Finset.mem_image.mpr ⟨l,by simp,rfl⟩
    have hli : basisRay (b 0) l ∈ row i := by
      by_contra hno
      have hmem := Finset.mem_sdiff.mpr ⟨rsub 0 hl0,hno⟩
      rw [huniq, Finset.mem_singleton] at hmem
      exact hl (basisRay_injective (b 0) (hmem.trans hkp.symm))
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hli
    have htj : t ≠ j := by
      intro e
      subst t
      exact hq ((ht.symm.trans hqpos) ▸ hl0)
    obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp ht.symm
    simp [← hs, inner_smul_left, (b i).inner_eq_ite, htj]
  apply hq
  exact Finset.mem_image.mpr ⟨k,by simp,hqk.symm.trans hqpos⟩

/-- Every positive-order QLS has at least n and at most n² rays, and n+1 is impossible. -/
theorem Realized.bounds {n c : ℕ} [NeZero n] (h : Realized n c) :
    n ≤ c ∧ c ≤ n^2 ∧ c ≠ n+1 := by
  classical
  obtain ⟨v,hv,rows,_,hc⟩ := h
  choose b hb using rows
  have he : (fun p : Cell n => Projectivization.mk ℂ (v p.1 p.2) (hv p.1 p.2)) =
      fun p => basisRay (b p.1) p.2 := by
    funext p
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨1, by simpa using congrFun (hb p.1) p.2⟩
  rw [he] at hc
  simpa only [← hc] using row_card_bounds b

#print axioms Realized.bounds
end QuantumCertificate
