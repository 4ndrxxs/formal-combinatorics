module
public import Quantum.SymmetricFour

/-! The complete ray-cardinality spectrum of symmetric quantum Latin squares up to order five. -/
@[expose] public section
noncomputable section
namespace SymmetricSmall
open QuantumCertificate
open scoped BigOperators

/-- Symmetry and cardinality both use complex projective rays. No initial basis is fixed. -/
def ProjectivelySymmetric (n c : ℕ) : Prop :=
  ∃ v : Fin n → Fin n → Space n, ∃ hn : ∀ i j, v i j≠0,
    (∀ i, ∃ B : OrthonormalBasis (Fin n) ℂ (Space n), ⇑B=v i) ∧
    (∀ j, ∃ B : OrthonormalBasis (Fin n) ℂ (Space n), ⇑B=fun i => v i j) ∧
    (∀ i j, Projectivization.mk ℂ (v i j) (hn i j)=Projectivization.mk ℂ (v j i) (hn j i)) ∧
    (rayRange (fun a : Cell n => v a.1 a.2) (fun a => hn a.1 a.2)).ncard=c

theorem projective_iff_based {n c : ℕ} [NeZero n] : ProjectivelySymmetric n c ↔ Has n c := by
  constructor
  · rintro ⟨v,hn,rows,_,sym,hc⟩
    classical
    let w (i j : Fin n) := if i≤j then v i j else v j i
    have sy (i j) : w i j=w j i := by
      unfold w
      rcases lt_trichotomy i j with h|rfl|h
      · simp [h.le,not_le_of_gt h]
      · rfl
      · simp [h.le,not_le_of_gt h]
    have scale (i j) : ∃ z : ℂ, z • v i j=w i j := by
      by_cases h : i≤j
      · exact ⟨1,by simp [w,h]⟩
      · simpa [w,h] using (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp (sym j i)
    have gram (i j k : Fin n) : inner ℂ (v i j) (v i k) = if j=k then 1 else 0 := by
      obtain ⟨B,hB⟩ := rows i
      rw [← hB,B.inner_eq_ite]
    have rowsW (i : Fin n) : ∃ B : OrthonormalBasis (Fin n) ℂ (Space n), ⇑B=w i := by
      apply basedONB
      intro j k
      by_cases h : j=k
      · subst k
        by_cases h : i≤j
        · simpa only [w,ite_eq_left h] using gram i j j
        · simpa only [w,ite_eq_right h] using gram j i i
      · obtain ⟨s,hs⟩ := scale i j
        obtain ⟨t,ht⟩ := scale i k
        rw [← hs,← ht,inner_smul_left,inner_smul_right,gram]
        simp [h]
    obtain ⟨B,hB⟩ := rowsW 0
    let f := B.repr
    let u (i j : Fin n) := f (w i j)
    have nz (i j) : u i j≠0 := by
      obtain ⟨D,hD⟩ := rowsW i
      intro he
      have h0 := f.injective (he.trans (map_zero f).symm)
      exact D.orthonormal.ne_zero j (congrFun hD j |>.trans h0)
    have urows (i : Fin n) : ∃ D : OrthonormalBasis (Fin n) ℂ (Space n), ⇑D=u i := by
      obtain ⟨D,hd⟩ := rowsW i
      exact ⟨D.map f,funext fun j => by simp [u,hd]⟩
    have usym (i j) : u i j=u j i := congrArg f (sy i j)
    refine ⟨⟨u,nz,urows,?_,?_,?_⟩,usym⟩
    · intro j
      simpa [funext (fun i => usym i j)] using urows j
    · intro j
      change B.repr (w 0 j)=_
      rw [← hB,B.repr_self]
    · let proj := Projectivization.map f.toLinearEquiv.toLinearMap f.injective
      have pt (a : Cell n) : Projectivization.mk ℂ (u a.1 a.2) (nz _ _) =
          proj (Projectivization.mk ℂ (v a.1 a.2) (hn _ _)) := by
        obtain ⟨z,hz⟩ := scale a.1 a.2
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨z,(map_smul f z _).symm.trans (congrArg f hz)⟩
      have eq : rayRange (fun a : Cell n => u a.1 a.2) (fun a => nz _ _) =
          proj '' rayRange (fun a : Cell n => v a.1 a.2) (fun a => hn _ _) := by
        ext r
        constructor
        · rintro ⟨a,rfl⟩
          exact ⟨_,⟨a,rfl⟩,(pt a).symm⟩
        · rintro ⟨_,⟨a,rfl⟩,rfl⟩
          exact ⟨a,pt a⟩
      rw [eq,Set.ncard_image_of_injective _ (Projectivization.map_injective _ f.injective)]
      exact hc
  · rintro ⟨b,sy⟩
    exact ⟨b.entry,b.nz,b.rows,b.cols,fun i j => cellRay_of_eq b (sy i j),b.count⟩

theorem classical_square (n : ℕ) [NeZero n] : Has n n := by
  classical
  let v (i j : Fin n) : Space n := EuclideanSpace.single (i+j) 1
  have rows (i : Fin n) : ∃ B : OrthonormalBasis (Fin n) ℂ (Space n), ⇑B=v i := by
    apply basedONB
    intro j k
    rw [EuclideanSpace.inner_single_left]
    by_cases h : j=k
    · subst k
      simp [v]
    · simp [v,h]
  have sy (i j) : v i j=v j i := by simp [v,add_comm]
  have nz (i j) : v i j≠0 := single_nz _
  refine ⟨⟨v,nz,rows,?_,?_,?_⟩,sy⟩
  · intro j
    simpa [funext (fun i => sy i j)] using rows j
  · intro j
    simp [v]
  · have eq : rayRange (fun a : Cell n => v a.1 a.2) (fun a => nz _ _) = coordinateRays n := by
      ext r
      constructor
      · rintro ⟨⟨i,j⟩,rfl⟩
        exact ⟨i+j,rfl⟩
      · rintro ⟨i,rfl⟩
        refine ⟨(0,i),(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1,?_⟩⟩
        simp [v]
    rw [eq,ncard_coordinateRays]

theorem at_most_three {n c : ℕ} [NeZero n] (h : Has n c) (hn : n≤3) : c=n := by
  obtain ⟨b,sy⟩ := h
  have off (i j : Fin n) (hij : i≠j) : cellRay b i j ∈ coordinateRays n := by
    by_cases hi : i=0
    · subst i
      exact ⟨j,(first_ray b j).symm⟩
    by_cases hj : j=0
    · subst j
      exact ⟨i,(first_ray b i).symm.trans (cellRay_of_eq b (sy 0 i))⟩
    by_contra hax
    obtain ⟨k,l,hkl,hk,hl⟩ := two_coordinates _ _ hax
    have hki : k≠i := fun h => hk (edge_zero b sy i j k hi hj (Or.inl h))
    have hkj : k≠j := fun h => hk (edge_zero b sy i j k hi hj (Or.inr h))
    have hli : l≠i := fun h => hl (edge_zero b sy i j l hi hj (Or.inl h))
    have hlj : l≠j := fun h => hl (edge_zero b sy i j l hi hj (Or.inr h))
    let f : Fin 4 → Fin n := ![i,j,k,l]
    have inj : Function.Injective f := by
      intro s t he
      fin_cases s <;> fin_cases t <;> simp_all [f]
    have hc := Fintype.card_le_of_injective f inj
    simp at hc
    omega
  have eq : b.rays=coordinateRays n := by
    apply Set.Subset.antisymm _ b.coordinate_subset
    rintro _ ⟨⟨i,j⟩,rfl⟩
    by_cases h : i=j
    · subst j
      exact remaining_axis b i i (fun j hj => off i j hj.symm)
    · exact off i j h
  rw [← b.ncard_rays,eq,ncard_coordinateRays]

/-- Among all symmetric squares of positive order at most five, the only additional
ray cardinality is six in order four. -/
theorem small_spectrum {n c : ℕ} [NeZero n] (hn : n≤5) :
    ProjectivelySymmetric n c ↔ c=n ∨ n=4 ∧ c=6 := by
  rw [projective_iff_based]
  constructor
  · intro h
    by_cases low : n≤3
    · exact Or.inl (at_most_three h low)
    · rcases (by omega : n=4 ∨ n=5) with rfl|rfl
      · exact (four_only h).imp_right (fun g => ⟨rfl,g⟩)
      · exact Or.inl (five_only h)
  · rintro (rfl|⟨rfl,rfl⟩)
    · exact classical_square _
    · exact four_six

#print axioms projective_iff_based
#print axioms small_spectrum
end SymmetricSmall
