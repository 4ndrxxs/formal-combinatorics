module

public import Quantum.IndexedArray

/-! Doubling an order with a complete cardinality spectrum. -/
@[expose] public section
namespace QuantumCertificate

def Good (n : ℕ) := ∀ c, n ≤ c → c ≤ n*n → c ≠ n+1 → Realized n c

/-- The sum of two copies of an integer interval punctured at its second element. -/
theorem add_punctured_intervals {l u z : ℕ} (width : l+3 ≤ u)
    (lo : l+l ≤ z) (hi : z ≤ u+u) (hole : z ≠ l+l+1) :
    ∃ x y : ℕ, l ≤ x ∧ x ≤ u ∧ x ≠ l+1 ∧
      l ≤ y ∧ y ≤ u ∧ y ≠ l+1 ∧ x+y=z := by
  by_cases h : z ≤ l+u
  · exact ⟨l,z-l,by omega⟩
  by_cases e : z = l+u+1
  · exact ⟨l+2,u-1,by omega⟩
  exact ⟨u,z-u,by omega⟩

abbrev Full (m : ℕ) := IndexedArray m (fun _ : Cell m => true)

/-- In one coordinate space take two coincident squares, or put them in
    general unitary position so that their finite ray sets are disjoint. -/
theorem exists_union_full {m : ℕ} (hm : 3 ≤ m) (h : Good m) (k : ℕ)
    (lo : m ≤ k) (hi : k ≤ 2*(m*m)) (hole : k ≠ m+1) :
    ∃ a b : Full m, (a.rays ∪ b.rays).ncard = k := by
  classical
  by_cases hk : k ≤ m*m
  · obtain ⟨a⟩ := (h k lo hk hole).toPartial
    refine ⟨IndexedArray.ofPartial a,IndexedArray.ofPartial a,?_⟩
    simpa only [Set.union_self,IndexedArray.rays_ofPartial] using
      (show a.rays.ncard = k from a.count)
  have width : m+m+2 ≤ m*m := by nlinarith [Nat.mul_self_le_mul_self hm]
  obtain ⟨x,y,lx,hx,ex,ly,hy,ey,hxy⟩ :=
    add_punctured_intervals (l:=m) (u:=m*m) (z:=k) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨a⟩ := (h x lx hx ex).toPartial
  obtain ⟨b⟩ := (h y ly hy ey).toPartial
  let i : Fin m := ⟨0,by omega⟩
  let : Nonempty (Used (fun _ : Cell m => true)) := ⟨⟨(i,i),rfl⟩⟩
  obtain ⟨b',dis⟩ := b.exists_disjoint_copy (by omega) a.rays a.rays_finite
  refine ⟨IndexedArray.ofPartial a,IndexedArray.ofPartial b',?_⟩
  change (a.rays ∪ b'.rays).ncard = k
  rw [Set.ncard_union_eq dis.symm a.rays_finite b'.rays_finite,
    show a.rays.ncard = x from a.count,show b'.rays.ncard = y from b'.count,hxy]

theorem Good.even {m : ℕ} (h : Good m) (hm : 3 ≤ m) : Good (m+m) := by
  classical
  intro c lo hi hole
  have width : m+m+2 ≤ m*m := by nlinarith [Nat.mul_self_le_mul_self hm]
  have upper : (m+m)*(m+m) = 2*(m*m)+2*(m*m) := by ring
  obtain ⟨x,y,lx,hx,ex,ly,hy,ey,hxy⟩ :=
    add_punctured_intervals (l:=m) (u:=2*(m*m)) (z:=c) (by omega) lo
      (by omega) hole
  obtain ⟨a,b,hab⟩ := exists_union_full hm h x lx hx ex
  obtain ⟨d,f,hdf⟩ := exists_union_full hm h y ly hy ey
  let diag := a.corners b
  let anti := (d.corners f).reindex (Equiv.refl _) (Equiv.sumComm _ _)
  let mask := IndexedArray.cornerMask (fun _ : Cell m => true) (fun _ : Cell m => true)
  have he : (fun p : (Fin m ⊕ Fin m) × (Fin m ⊕ Fin m) =>
      mask ((Equiv.refl _) p.1,(Equiv.sumComm _ _) p.2)) = (fun p => !mask p) := by
    funext ⟨i,j⟩
    cases i <;> cases j <;> rfl
  let : NeZero (m+m) := ⟨by omega⟩
  have built := IndexedArray.join diag (anti.changeMask he) finSumFinEquiv.symm
  simpa only [diag,anti,IndexedArray.rays_changeMask,IndexedArray.rays_reindex,
    IndexedArray.rays_corners,hab,hdf,hxy] using built

#print axioms Good.even
end QuantumCertificate
