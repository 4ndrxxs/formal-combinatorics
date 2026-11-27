module
public import Quantum.SymmetricSmall

/-! Every symmetric order-four quantum Latin square has at most six complex rays. -/
@[expose] public section
noncomputable section
namespace SymmetricSmall
open QuantumCertificate Complex Finset
open scoped ComplexConjugate BigOperators

def fourL : Fin 3 → Fin 4 := ![2,1,1]
def fourR : Fin 3 → Fin 4 := ![3,3,2]
def fourEdge {c} (b : BasedSquare 4 c) (m : Fin 3) := b.entry (fourL m) (fourR m)
def fourEnds (m : Fin 3) (i j : Fin 4) :=
  (fourL m=i ∧ fourR m=j) ∨ (fourL m=j ∧ fourR m=i)

instance (m : Fin 3) (i j : Fin 4) : Decidable (fourEnds m i j) := by
  unfold fourEnds
  infer_instance

theorem four_entry_of_ends {c : ℕ} (b : BasedSquare 4 c) (sy : ∀ i j, b.entry i j=b.entry j i)
    {m i j} (h : fourEnds m i j) : fourEdge b m=b.entry i j := by
  rcases h with ⟨hi,hj⟩|⟨hj,hi⟩ <;> subst i <;> subst j
  · rfl
  · exact sy _ _

theorem four_edge_zeros {c : ℕ} (b : BasedSquare 4 c) (sy : ∀ i j, b.entry i j=b.entry j i)
    (m : Fin 3) (k : Fin 4) (hk : k≠0) (hm : k≠m.succ) : fourEdge b m k=0 := by
  apply edge_zero b sy _ _ _
    ((by decide +kernel : ∀ m, fourL m≠0) m) ((by decide +kernel : ∀ m, fourR m≠0) m)
  exact (by decide +kernel :
      ∀ (m : Fin 3) (k : Fin 4), k≠0 → k≠m.succ → k=fourL m ∨ k=fourR m) m k hk hm

theorem four_orth {c : ℕ} (b : BasedSquare 4 c) (sy : ∀ i j, b.entry i j=b.entry j i)
    (m t : Fin 3) (h : m≠t) : inner ℂ (fourEdge b m) (fourEdge b t)=0 := by
  obtain ⟨i,j,k,hjk,hm,ht⟩ := (by decide +kernel :
      ∀ m t, m≠t → ∃ i j k, j≠k ∧ fourEnds m i j ∧ fourEnds t i k) m t h
  rw [four_entry_of_ends b sy hm,four_entry_of_ends b sy ht]
  exact row_orth b i j k hjk

theorem four_active {c : ℕ} (b : BasedSquare 4 c) (sy : ∀ i j, b.entry i j=b.entry j i)
    (m t : Fin 3) (h : m≠t) : fourEdge b m 0=0 ∨ fourEdge b t 0=0 := by
  have ho := four_orth b sy m t h
  rw [reduced_inner _ _ 0 m.succ (Fin.succ_ne_zero _).symm
    (fun k hk hm => Or.inl (four_edge_zeros b sy m k hk hm))] at ho
  have hz := four_edge_zeros b sy t m.succ (Fin.succ_ne_zero _) (Fin.succ_injective _ |>.ne h)
  simpa [hz,mul_eq_zero,or_comm] using ho

theorem single_of_support {n : ℕ} (v : Space n) (hn : v≠0) (k : Fin n)
    (h : ∀ i, i≠k → v i=0) : Projectivization.mk ℂ v hn=coordinateRay k := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨v k,?_⟩
  ext i
  change v k * (EuclideanSpace.single k 1 : Space n) i = v i
  by_cases hi : i=k
  · subst i
    simp
  · simp [hi,h i hi]

theorem four_distinguished {c : ℕ} (b : BasedSquare 4 c) (sy : ∀ i j, b.entry i j=b.entry j i) :
    ∃ m : Fin 3, ∀ t : Fin 3, t≠m → ∀ i j, fourEnds t i j → cellRay b i j=coordinateRay t.succ := by
  classical
  have once : ∃ m : Fin 3, ∀ t, t≠m → fourEdge b t 0=0 := by
    by_cases hex : ∃ m, fourEdge b m 0≠0
    · obtain ⟨m,hm⟩ := hex
      exact ⟨m,fun t ht => (four_active b sy m t ht.symm).resolve_left hm⟩
    · push Not at hex
      exact ⟨0,fun t _ => hex t⟩
  obtain ⟨m,hm⟩ := once
  refine ⟨m,fun t ht i j hij => single_of_support _ (b.nz i j) t.succ ?_⟩
  intro k hk
  rw [← four_entry_of_ends b sy hij]
  by_cases h0 : k=0
  · subst k
    exact hm t ht
  · exact four_edge_zeros b sy t k h0 hk

theorem remaining_same {n c : ℕ} [NeZero n] (b : BasedSquare n c) (a x i y : Fin n)
    (h : ∀ j, j≠x → ∃ k, k≠y ∧ cellRay b a j=cellRay b i k) :
    cellRay b a x=cellRay b i y := by
  classical
  obtain ⟨B,hB⟩ := b.rows a
  let v := b.entry i y
  have hor (j : Fin n) (hj : j≠x) : inner ℂ (B j) v=0 := by
    obtain ⟨k,hk,hr⟩ := h j hj
    obtain ⟨z,hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hr
    rw [congrFun hB j,← hz,inner_smul_left]
    simp [v,row_orth b i k y hk]
  symm
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨inner ℂ (B x) v,?_⟩
  rw [← congrFun hB x]
  calc
    _ = ∑ j, inner ℂ (B j) v • B j := by
      symm
      apply Finset.sum_eq_single x
      · intro j _ hj
        simp [hor j hj]
      · simp
    _ = _ := B.sum_repr' v

theorem four_at_most {c : ℕ} (h : Has 4 c) : c≤6 := by
  classical
  obtain ⟨b,sy⟩ := h
  obtain ⟨m,hm⟩ := four_distinguished b sy
  let p := fourL m
  let q := fourR m
  let l := m.succ
  have corners (i : Fin 4) : i=0 ∨ i=p ∨ i=q ∨ i=l :=
    (by decide +kernel : ∀ (m : Fin 3) (i : Fin 4),
      i=0 ∨ i=fourL m ∨ i=fourR m ∨ i=m.succ) m i
  have hne : p≠q ∧ p≠l ∧ q≠l ∧ p≠0 ∧ q≠0 :=
    (by decide +kernel : ∀ m:Fin 3, fourL m≠fourR m ∧ fourL m≠m.succ ∧
      fourR m≠m.succ ∧ fourL m≠0 ∧ fourR m≠0) m
  have rs (i j : Fin 4) : cellRay b i j=cellRay b j i := cellRay_of_eq b (sy i j)
  have first (i : Fin 4) : cellRay b i 0=coordinateRay i := (rs i 0).trans (first_ray b i)
  have pl : cellRay b p l=coordinateRay q := by
    obtain ⟨t,ht,he,hq⟩ := (by decide +kernel : ∀ m:Fin 3, ∃ t, t≠m ∧
      fourEnds t (fourL m) m.succ ∧ t.succ=fourR m) m
    exact (hm t ht _ _ he).trans (congrArg coordinateRay hq)
  have ql : cellRay b q l=coordinateRay p := by
    obtain ⟨t,ht,he,hp⟩ := (by decide +kernel : ∀ m:Fin 3, ∃ t, t≠m ∧
      fourEnds t (fourR m) m.succ ∧ t.succ=fourL m) m
    exact (hm t ht _ _ he).trans (congrArg coordinateRay hp)
  have diag : cellRay b p p=cellRay b q q := by
    apply remaining_same
    intro j hj
    rcases corners j with e|e|e|e
    · subst j
      exact ⟨l,hne.2.2.1.symm,(first p).trans ql.symm⟩
    · contradiction
    · rw [e]
      exact ⟨p,hne.1,rs p q⟩
    · rw [e]
      exact ⟨0,hne.2.2.2.2.symm,pl.trans (first q).symm⟩
  have dl : cellRay b l l ∈ coordinateRays 4 := by
    apply remaining_axis
    intro j hj
    rcases corners j with e|e|e|e
    · rw [e]
      exact ⟨l,(first l).symm⟩
    · rw [e]
      exact ⟨q,pl.symm.trans (rs p l)⟩
    · rw [e]
      exact ⟨p,ql.symm.trans (rs q l)⟩
    · contradiction
  let S := coordinateRays 4 ∪ {cellRay b p q,cellRay b p p}
  have root (i) : cellRay b 0 i ∈ S := Or.inl ⟨i,(first_ray b i).symm⟩
  have memsq : cellRay b p q ∈ S := Or.inr (by simp)
  have mempp : cellRay b p p ∈ S := Or.inr (by simp)
  have memqq : cellRay b q q ∈ S := diag ▸ mempp
  have mempl : cellRay b p l ∈ S := Or.inl ⟨q,pl.symm⟩
  have memql : cellRay b q l ∈ S := Or.inl ⟨p,ql.symm⟩
  have memll : cellRay b l l ∈ S := Or.inl dl
  have rev (i j) (h : cellRay b i j ∈ S) : cellRay b j i ∈ S := rs i j ▸ h
  have sub : b.rays ⊆ S := by
    rintro _ ⟨⟨i,j⟩,rfl⟩
    change cellRay b i j ∈ S
    rcases corners i with h|h|h|h <;> rcases corners j with g|g|g|g <;> rw [h,g]
    all_goals first
      | exact root _
      | exact rev _ _ (root _)
      | exact memsq | exact mempp | exact memqq | exact mempl | exact memql | exact memll
      | exact rev _ _ memsq | exact rev _ _ mempl | exact rev _ _ memql
  have finite : S.Finite := (Set.finite_range _).union (Set.toFinite _)
  calc
    c = b.rays.ncard := b.ncard_rays.symm
    _ ≤ S.ncard := Set.ncard_le_ncard sub finite
    _ ≤ (coordinateRays 4).ncard+({cellRay b p q,cellRay b p p} : Set _).ncard :=
      Set.ncard_union_le _ _
    _ ≤ 6 := by
      rw [ncard_coordinateRays]
      by_cases he : cellRay b p q=cellRay b p p
      · simp [he]
      · simp [Set.ncard_pair he]

theorem four_only {c : ℕ} (h : Has 4 c) : c=4 ∨ c=6 := by
  have hu := four_at_most h
  obtain ⟨b,_⟩ := h
  obtain ⟨hl,_,hne⟩ := b.realized.bounds
  omega

#print axioms four_only
end SymmetricSmall
