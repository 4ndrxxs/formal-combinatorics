import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-! Lower bounds for the height of a point by successive specialization of
polynomial parameters. Some parameters may be visible only after multiplying
them by a common polynomial. -/

noncomputable section
namespace DeterminantalRegularity
open MvPolynomial Finset
variable {K R σ : Type*} [Field K] [CommRing R] [DecidableEq σ]

/-- Substitute the chosen point in the coordinates indexed by a finite set. -/
def specialize (a : σ → K) (s : Finset σ) :
    MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom C (fun i ↦ if i ∈ s then C (a i) else X i)

@[simp] theorem specialize_const (a : σ → K) (s : Finset σ) (k : K) :
    specialize a s (C k) = C k := by simp [specialize]

@[simp] theorem specialize_var (a : σ → K) (s : Finset σ) (i : σ) :
    specialize a s (X i) = if i ∈ s then C (a i) else X i := by simp [specialize]

private theorem specialize_nested (a : σ → K) {s t : Finset σ} (sub : s ⊆ t) :
    (specialize a t).comp (specialize a s) = specialize a t := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp
  · intro i
    by_cases h : i ∈ s
    · simp [h,sub h]
    · simp [h]

/-- The prime cut out in the source by specializing a set of parameters. -/
def pointPrime (f : R →+* MvPolynomial σ K) (a : σ → K) (s : Finset σ) : Ideal R :=
  RingHom.ker ((specialize a s).comp f)

instance (f : R →+* MvPolynomial σ K) (a : σ → K) (s : Finset σ) :
    (pointPrime f a s).IsPrime := RingHom.ker_isPrime _

private lemma step_mono (f : R →+* MvPolynomial σ K) (a : σ → K)
    {s t : Finset σ} (sub : s ⊆ t) : pointPrime f a s ≤ pointPrime f a t := by
  intro w hw
  change specialize a s (f w) = 0 at hw
  change specialize a t (f w) = 0
  have eq := RingHom.congr_fun (specialize_nested a sub) (f w)
  rw [← eq,RingHom.comp_apply,hw,map_zero]

private lemma grow (f : R →+* MvPolynomial σ K) (a : σ → K) (start free : Finset σ)
    (separate : ∀ s ⊆ free, ∀ i ∈ free, i ∉ s →
      ∃ w : R, w ∉ pointPrime f a (start ∪ s) ∧ w ∈ pointPrime f a (insert i (start ∪ s))) :
    (pointPrime f a start).height + (free.card : ℕ∞) ≤ (pointPrime f a (start ∪ free)).height := by
  suffices aux : ∀ s ⊆ free, (pointPrime f a start).height + (s.card : ℕ∞) ≤
      (pointPrime f a (start ∪ s)).height from aux free (Subset.rfl)
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro si
    have sf : s ⊆ free := fun j hj ↦ si (mem_insert_of_mem hj)
    obtain ⟨w,hw,kw⟩ := separate s sf i (si (mem_insert_self ..)) hi
    have incl := step_mono f a (Finset.subset_insert i (start ∪ s))
    have strict : pointPrime f a (start ∪ s) < pointPrime f a (insert i (start ∪ s)) :=
      lt_of_le_of_ne incl (fun h ↦ hw (h ▸ kw))
    rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,← add_assoc,Finset.union_insert]
    exact (add_le_add_left (ih sf) 1).trans (Ideal.height_add_one_le_of_lt_of_isPrime strict)

omit [DecidableEq σ] in
private lemma variable_diff_ne (i : σ) (k : K) : (X i : MvPolynomial σ K) - C k ≠ 0 := by
  intro h
  have z := congrArg (MvPolynomial.eval (fun _ : σ ↦ k+1)) h
  simp at z

/-- The height of the point in a parametrized affine ring is at least
the total number of parameters when each centered parameter is in the
image, either directly or after multiplication by a polynomial that
remains nonzero while the first group of parameters is specialized. -/
theorem height_of_parameters [Fintype σ] (f : R →+* MvPolynomial σ K)
    (a : σ → K) (first : Finset σ) (D : MvPolynomial σ K)
    (survives : ∀ s ⊆ first, specialize a s D ≠ 0)
    (guarded : ∀ i ∈ first, D * (X i - C (a i)) ∈ Set.range f)
    (visible : ∀ i ∉ first, X i - C (a i) ∈ Set.range f) :
    (Fintype.card σ : ℕ∞) ≤ (pointPrime f a univ).height := by
  have first_step := grow f a ∅ first (by
    intro s sub i hi hs
    obtain ⟨w,hw⟩ := guarded i hi
    refine ⟨w,?_,?_⟩
    · change specialize a (∅ ∪ s) (f w) ≠ 0
      simpa [hw,hs] using mul_ne_zero (survives s sub) (variable_diff_ne i (a i))
    · change specialize a (insert i (∅ ∪ s)) (f w) = 0
      simp [hw])
  have first_height : (first.card : ℕ∞) ≤ (pointPrime f a first).height := by
    simpa only [empty_union] using (le_add_self : (first.card : ℕ∞) ≤
      (pointPrime f a ∅).height + first.card).trans first_step
  have second := grow f a first firstᶜ (by
    intro s _ i hi hs
    have hf : i ∉ first := Finset.mem_compl.mp hi
    obtain ⟨w,hw⟩ := visible i hf
    refine ⟨w,?_,?_⟩
    · change specialize a (first ∪ s) (f w) ≠ 0
      simpa [hw,hf,hs] using variable_diff_ne i (a i)
    · change specialize a (insert i (first ∪ s)) (f w) = 0
      simp [hw])
  have count := Finset.card_add_card_compl first
  calc
    (Fintype.card σ : ℕ∞) = (first.card : ℕ∞) + firstᶜ.card := by exact_mod_cast count.symm
    _ ≤ (pointPrime f a first).height + firstᶜ.card := add_le_add_left first_height _
    _ ≤ _ := by simpa using second

#print axioms height_of_parameters
end DeterminantalRegularity
