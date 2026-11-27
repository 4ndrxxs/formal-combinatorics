module
public import Quantum.FractionalBlockBell

/-! The untouched first block measures a genuinely nonclassical fractional
Sudoku in every size N ≥ 4. Classical mixtures restrict along the four-symbol
coordinate face. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalIntercalate
  FractionalPolygons.Sudoku Function Equiv Complex Finset
open scoped ComplexConjugate BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def Classical (p : BigProb I) : Prop :=
  ∃ f : Site I → Index I,
    (∀ d k, Function.Injective (fun j => f (arrange d (k,j)))) ∧
    ∀ q k, p q k=if f q=k then 1 else 0

def trim (L : Latin I) (p : BigProb I) : SmallProb :=
  fun q k => p (position L q) (coordinate L k)

def Supported (L : Latin I) (p : BigProb I) : Prop :=
  ∀ q k, k∉Set.range (coordinate L) → p (position L q) k=0

omit [Fintype I] [DecidableEq I] in
theorem position_line (L : Latin I) (d : Direction) (a : tiny) (i : Fin 4) :
    position L (FractionalBinary.line (lineNum d a) i)=arrange d (liftPair L.tag a,liftPair L.tag (number.symm i)) := by
  have h := tiny_line d a (number.symm i)
  rw [number.apply_symm_apply] at h
  rw [←h,position,toTiny_fromTiny,arrange_lift]

theorem trim_classical (L : Latin I) {p : BigProb I} (h : Classical p) (hz : Supported L p) :
    FractionalBell.ClassicalGrid (trim L p) := by
  obtain ⟨f,hf,hp⟩ := h
  have covered (q : FractionalBinary.Site) : ∃ k, coordinate L k=f (position L q) := by
    by_contra hh
    have z := hz q (f (position L q)) hh
    norm_num [hp] at z
  choose g hg using covered
  refine ⟨g,?_,fun q k => ?_⟩
  · intro l
    obtain ⟨d,a,rfl⟩ := all_tiny_lines l
    intro i j eq
    have he := congrArg (coordinate L) eq
    simp only [hg,position_line] at he
    exact number.symm.injective ((liftPair L.tag).injective (hf d _ he))
  · rw [trim,hp,←hg]
    simp [(coordinate L).injective.eq_iff]

/-- A convex decomposition of a supported large array restricts to a convex
decomposition by genuine classical size-two Sudoku. -/
theorem trim_classical_hull (L : Latin I) {p : BigProb I}
    (h : p∈convexHull ℝ {p | Classical p}) (hz : Supported L p) :
    trim L p∈convexHull ℝ {p | FractionalBell.ClassicalGrid p} := by
  let good : Set (BigProb I) := {p | (∀ q k,0≤p q k) ∧
    (Supported L p → trim L p∈convexHull ℝ {p | FractionalBell.ClassicalGrid p})}
  have base : {p : BigProb I | Classical p}⊆good := by
    intro z hc
    refine ⟨?_,fun hs => subset_convexHull ℝ _ (trim_classical L hc hs)⟩
    obtain ⟨_,_,hp⟩ := hc
    intro x k
    rw [hp]
    split <;> norm_num
  have cv : Convex ℝ good := by
    intro z hz w hw a b ha hb hab
    by_cases az : a=0
    · have bo : b=1 := by linarith
      simpa [az,bo] using hw
    by_cases bz : b=0
    · have ao : a=1 := by linarith
      simpa [bz,ao] using hz
    obtain ⟨zn,zt⟩ := hz
    obtain ⟨wn,wt⟩ := hw
    refine ⟨fun q k => add_nonneg (mul_nonneg ha (zn q k)) (mul_nonneg hb (wn q k)),?_⟩
    intro supp
    have both (q : FractionalBinary.Site) (k : Index I) (hk : k∉Set.range (coordinate L)) :
        z (position L q) k=0 ∧ w (position L q) k=0 := by
      have hh := supp q k hk
      change a*z (position L q) k+b*w (position L q) k=0 at hh
      obtain ⟨u,v⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg ha (zn _ _)) (mul_nonneg hb (wn _ _))).mp hh
      exact ⟨(mul_eq_zero.mp u).resolve_left az,(mul_eq_zero.mp v).resolve_left bz⟩
    exact convex_convexHull ℝ _ (zt (fun q k hk => (both q k hk).1))
      (wt (fun q k hk => (both q k hk).2)) ha hb hab
  exact ((convexHull_min base cv) h).2 hz

def permute (e : Perm (Index I)) (p : BigProb I) : BigProb I := fun q k => p q (e k)

omit [Fintype I] in
theorem permute_classical (e : Perm (Index I)) {p : BigProb I} (h : Classical p) : Classical (permute e p) := by
  obtain ⟨f,hf,hp⟩ := h
  refine ⟨fun q => e.symm (f q),fun d k => e.symm.injective.comp (hf d k),fun q k => ?_⟩
  rw [permute,hp]
  simp [e.symm_apply_eq]

omit [Fintype I] in
theorem permute_hull (e : Perm (Index I)) {p : BigProb I} (h : p∈convexHull ℝ {p | Classical p}) :
    permute e p∈convexHull ℝ {p | Classical p} := by
  have cv : Convex ℝ {p : BigProb I | permute e p∈convexHull ℝ {p | Classical p}} := by
    intro p hp q hq a b ha hb hab
    exact convex_convexHull ℝ _ hp hq ha hb hab
  have base : {p : BigProb I | Classical p}⊆{p | permute e p∈convexHull ℝ {p | Classical p}} :=
    fun _ hp => subset_convexHull ℝ _ (permute_classical e hp)
  exact (convexHull_min base cv) h

def blockReadout (z : I) (v : Grid I) : BigProb I :=
  fun q k => normSq (inner ℂ (v (z,k.1) (z,k.2)) (v q.1 q.2))

def RationalEntries (v : Grid I) : Prop :=
  ∀ r c k, ∃ a : ℚ, v r c k=(a:ℂ)

theorem untouched_block (L : Latin I) (z : I) (hz : z∉Set.range L.tag)
    (v : FractionalBinary.Site → Space 4) :
    ∃ e : Perm (Index I), blockReadout z (fun r c => inserted L v (r,c))=permute e (bareTable L v) := by
  let e := Equiv.ofBijective (fun k => symbol L (arrange .block ((z,z),k)))
    (symbol_bijective L .block (z,z))
  refine ⟨e,?_⟩
  funext q k
  have out : ((z,k.1),(z,k.2))∉Set.range (liftSite L.tag) := by
    rintro ⟨x,hx⟩
    exact hz ⟨x.1.1,congrArg (fun t : Site I => t.1.1) hx⟩
  simp only [blockReadout,inserted_outside L v _ out]
  simp [axis,EuclideanSpace.inner_single_left,permute,bareTable,e,arrange]
  rfl

theorem rational_small (q : FractionalBinary.Site) (k : Fin 4) :
    ∃ a : ℚ, FractionalBellWitness.smallVector q k=(a:ℂ) := by
  refine ⟨(FractionalBellWitness.raw q k:ℚ)/125,?_⟩
  norm_num [FractionalBellWitness.smallVector,vector,FractionalBellWitness.data,mul_comm,div_eq_mul_inv]

theorem rational_inserted (L : Latin I) (v : FractionalBinary.Site → Space 4)
    (hv : ∀ q k,∃ a : ℚ, v q k=(a:ℂ)) :
    RationalEntries (fun r c => inserted L v (r,c)) := by
  intro r c k
  change ∃ a : ℚ, inserted L v (r,c) k=(a:ℂ)
  by_cases hs : (r,c)∈Set.range (liftSite L.tag)
  · obtain ⟨x,hx⟩ := hs
    rw [←hx,inserted_inside]
    by_cases hk : k∈Set.range (coordinate L)
    · obtain ⟨a,rfl⟩ := hk
      rw [include_at]
      exact hv _ _
    · exact ⟨0,by rw [include_out L _ _ hk]; norm_num⟩
  · rw [inserted_outside L v _ hs]
    by_cases he : symbol L (r,c)=k
    · exact ⟨1,by simp [axis,he]⟩
    · exact ⟨0,by simp [axis,he]⟩

/-- For every N ≥ 4, measuring a rational real N-SudoQ in its actual first
block produces a scalar probability array outside the entire classical
Sudoku convex hull. There is no restriction on the number of components. -/
theorem designated_block_nonclassical (N : ℕ) (hN : 4≤N) :
    ∃ v : Grid (Fin N), Valid v ∧ RationalEntries v ∧
      blockReadout (⟨0,by omega⟩ : Fin N) v∉convexHull ℝ {p | Classical p} := by
  let z : Fin N := ⟨0,by omega⟩
  let A := FractionalIntercalate.ofOrders N (Or.inr hN)
  obtain ⟨o,ho⟩ : ∃ o, o∉Set.range A.tag := by
    by_contra! h
    have le := Fintype.card_le_of_surjective A.tag h
    simp at le
    omega
  let σ := Equiv.swap o z
  let L := A.reindex σ
  have hz : z∉Set.range L.tag := by
    rintro ⟨i,hi⟩
    change σ (A.tag i)=z at hi
    exact ho ⟨i,σ.injective (hi.trans (Equiv.swap_apply_left o z).symm)⟩
  let v := FractionalBellWitness.smallVector
  refine ⟨fun r c => inserted L v (r,c),inserted_valid L v FractionalBellWitness.small_grid,
    rational_inserted L v rational_small,?_⟩
  obtain ⟨e,he⟩ := untouched_block L z hz v
  change blockReadout z (fun r c => inserted L v (r,c))∉_
  rw [he]
  intro mixture
  have base := permute_hull e.symm mixture
  have undo : permute e.symm (permute e (bareTable L v))=bareTable L v := by
    funext q k; simp [permute]
  rw [undo] at base
  have small := trim_classical_hull L base (bare_supported L v)
  have eq : trim L (bareTable L v)=FractionalBellWitness.smallTable := by
    funext q k
    rw [trim,trim_bare,FractionalBellWitness.small_born]
  rw [eq] at small
  exact FractionalBellWitness.outside small

#print axioms trim_classical_hull
#print axioms designated_block_nonclassical
end FractionalBlockBell

