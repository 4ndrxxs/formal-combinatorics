module

public import Quantum.EvenSpectrum

/-! Unions of the rays of several quantum Latin squares in one coordinate space. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
namespace Collections
open QuantumCertificate

abbrev Rays (n : ℕ) := Set (Projectivization ℂ (Space n))
def states {n k : ℕ} (F : Fin k → Full n) : Rays n := ⋃ i, (F i).rays
def Attain (n k c : ℕ) : Prop := ∃ F : Fin k → Full n, (states F).ncard = c

theorem finite_states {n k : ℕ} (F : Fin k → Full n) : (states F).Finite :=
  Set.finite_iUnion (fun i => (F i).rays_finite)

theorem state_mem {n k : ℕ} {F : Fin k → Full n} {q : Projectivization ℂ (Space n)} :
    q ∈ states F ↔ ∃ i, q ∈ (F i).rays := Set.mem_iUnion

theorem of_two {n c : ℕ} (a b : Full n) (hab : (a.rays ∪ b.rays).ncard = c) :
    Attain n 2 c := by
  let F : Fin 2 → Full n := ![a,b]
  refine ⟨F,?_⟩
  have eq : states F = a.rays ∪ b.rays := by
    ext q
    rw [state_mem]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h|h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
  rwa [eq]

theorem one {n c : ℕ} (h : Realized n c) : Attain n 1 c := by
  obtain ⟨a⟩ := h.toPartial
  refine ⟨fun _ => IndexedArray.ofPartial a,?_⟩
  have eq : states (fun _ : Fin 1 => IndexedArray.ofPartial a) = a.rays := by
    ext q
    simp [states,IndexedArray.rays_ofPartial]
  rw [eq]
  exact a.count

theorem pad {n k l c : ℕ} (hk : 0<k) (hl : k≤l) (a : Attain n k c) : Attain n l c := by
  obtain ⟨F,hF⟩ := a
  let pick (i : Fin l) : Fin k := if h : i.val<k then ⟨i.val,h⟩ else ⟨0,hk⟩
  have surj : Function.Surjective pick := fun i => ⟨⟨i.val,lt_of_lt_of_le i.isLt hl⟩,
    by apply Fin.ext; simp [pick,i.isLt]⟩
  have eq : states (F ∘ pick) = states F := by
    ext q
    rw [state_mem,state_mem]
    exact ⟨fun ⟨i,h⟩ => ⟨pick i,h⟩,fun ⟨j,h⟩ => by obtain ⟨i,rfl⟩ := surj j; exact ⟨i,h⟩⟩
  exact ⟨F ∘ pick,eq ▸ hF⟩

def mapped {n : ℕ} (u : Space n →ₗᵢ[ℂ] Space n) (a : Full n) : Full n where
  entry p := u (a.entry p)
  nz p h := a.nz p (u.injective (h.trans (map_zero _).symm))
  unit p := (u.norm_map _).trans (a.unit p)
  rows i j k hj hk h := (u.inner_map_map _ _).trans (a.rows i j k hj hk h)
  cols i j k hj hk h := (u.inner_map_map _ _).trans (a.cols i j k hj hk h)

theorem mapped_states {n k : ℕ} (u : Space n →ₗᵢ[ℂ] Space n) (F : Fin k → Full n) :
    states (fun i => mapped u (F i)) = Projectivization.map u.toLinearMap u.injective '' states F := by
  ext z
  constructor
  · intro h
    obtain ⟨i,p,rfl⟩ := state_mem.mp h
    exact ⟨_,state_mem.mpr ⟨i,p,rfl⟩,rfl⟩
  · rintro ⟨_,h,rfl⟩
    obtain ⟨i,p,rfl⟩ := state_mem.mp h
    exact state_mem.mpr ⟨i,p,rfl⟩

private theorem join_states {n k l : ℕ} (F : Fin k → Full n) (G : Fin l → Full n) :
    states (fun i => Sum.elim F G (finSumFinEquiv.symm i)) = states F ∪ states G := by
  ext z
  rw [state_mem,Set.mem_union,state_mem,state_mem]
  constructor
  · rintro ⟨i,h⟩
    rcases e : finSumFinEquiv.symm i with a|b
    · exact Or.inl ⟨a,by simpa [e] using h⟩
    · exact Or.inr ⟨b,by simpa [e] using h⟩
  · rintro (⟨a,h⟩|⟨b,h⟩)
    · exact ⟨finSumFinEquiv (.inl a),by simpa using h⟩
    · exact ⟨finSumFinEquiv (.inr b),by simpa using h⟩

theorem append {n k l x y : ℕ} (hn : 2≤n) (hl : 0<l) (a : Attain n k x)
    (b : Attain n l y) : Attain n (k+l) (x+y) := by
  classical
  obtain ⟨F,hF⟩ := a
  obtain ⟨G,hG⟩ := b
  let i0 : Fin n := ⟨0,by omega⟩
  let : Nonempty (Fin l × Sites (fun _ : Cell n => true)) :=
    ⟨(⟨0,hl⟩,⟨(i0,i0),rfl⟩)⟩
  obtain ⟨u,hu⟩ := exists_isometry_avoiding hn
    (fun t : Fin l × Sites (fun _ : Cell n => true) => (G t.1).entry t.2.val)
    (fun t => (G t.1).nz t.2) (states F) (finite_states F)
  let D := fun i => mapped u (G i)
  have hd : Disjoint (states D) (states F) := by
    apply Set.disjoint_left.mpr
    intro z hz
    obtain ⟨i,p,rfl⟩ := state_mem.mp hz
    exact hu (i,p)
  have hc : (states D).ncard = y := by
    rw [show states D = _ from mapped_states u G,
      Set.ncard_image_of_injective _ (Projectivization.map_injective _ u.injective),hG]
  refine ⟨fun i => Sum.elim F D (finSumFinEquiv.symm i),?_⟩
  rw [join_states F D,Set.ncard_union_eq hd.symm (finite_states F) (finite_states D),hF,hc]

theorem large_union {n : ℕ} (hn : 3≤n) (h : Good n) (k : ℕ) (hk : 2≤k) (c : ℕ)
    (lo : n≤c) (hi : c≤k*(n*n)) (hole : c≠n+1) : Attain n k c := by
  induction k, hk using Nat.le_induction generalizing c with
  | base =>
    obtain ⟨a,b,hab⟩ := exists_union_full hn h c lo hi hole
    exact of_two a b hab
  | succ k hk ih =>
    by_cases fit : c≤k*(n*n)
    · exact pad (by omega) (Nat.le_succ _) (ih _ lo fit hole)
    have width : n+1<n*n := by nlinarith
    have lower : 2*(n*n)≤k*(n*n) := Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at hi
    have prior := ih (c-n*n) (by omega) (by omega) (by omega)
    have top := one (h (n*n) (by omega) le_rfl (by omega))
    simpa only [Nat.sub_add_cancel (by omega : n*n≤c)] using
      append (by omega : 2≤n) (by decide : 0<1) prior top

end Collections
end QuantumSudoku
