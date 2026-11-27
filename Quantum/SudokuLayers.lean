module

public import Quantum.Sudoku
public import Quantum.SudokuCollections
public import Quantum.Bounds
public import Mathlib.Data.Set.Card.Arithmetic

/-! Counts in a quantum Sudoku. Independent order-n quantum Latin squares
    fill the n orthogonal summands, with an independent square per band. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
open QuantumCertificate Finset
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem Valid.nz {v : Grid I} (h : Valid v) (r c : Index I) : v r c ≠ 0 := by
  obtain ⟨b,hb⟩ := h.row r
  rw [←hb]
  exact b.orthonormal.ne_zero c

def gridRays {v : Grid I} (h : Valid v) : Set (Projectivization ℂ (H I)) :=
  Set.range (fun t : Index I × Index I => Projectivization.mk ℂ (v t.1 t.2) (h.nz t.1 t.2))

def Realizes (n c : ℕ) : Prop := ∃ v : Grid (Fin n), ∃ h : Valid v, (gridRays h).ncard=c

theorem to_latin {n c : ℕ} (h : Realizes n c) : QuantumCertificate.Realized (n*n) c := by
  classical
  obtain ⟨v,hv,hc⟩ := h
  let e : Index (Fin n) ≃ Fin (n*n) := finProdFinEquiv
  let u := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let w := fun a b : Fin (n*n) => u (v (e.symm a) (e.symm b))
  have hn (a b) : w a b ≠ 0 := fun eq => hv.nz _ _ (u.injective (eq.trans (map_zero _).symm))
  have bas (f : Index (Fin n) → H (Fin n)) (hf : BasisLine f) :
      ∃ b : OrthonormalBasis (Fin (n*n)) ℂ (Space (n*n)), ⇑b=fun a => u (f (e.symm a)) := by
    obtain ⟨B,rfl⟩ := hf
    exact ⟨(B.map u).reindex e,by funext a; simp⟩
  refine ⟨w,hn,fun a => bas _ (hv.row (e.symm a)),fun a => bas _ (hv.column (e.symm a)),?_⟩
  let f := Projectivization.map u.toLinearMap u.injective
  have he : Set.range (fun p : Cell (n*n) => Projectivization.mk ℂ (w p.1 p.2) (hn p.1 p.2)) =
      f '' gridRays hv := by
    ext z
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨_,⟨(e.symm a,e.symm b),rfl⟩,rfl⟩
    · rintro ⟨_,⟨⟨a,b⟩,rfl⟩,rfl⟩
      refine ⟨(e a,e b),?_⟩
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      exact ⟨1,by simp [w]⟩
  rw [he,Set.ncard_image_of_injective _ (Projectivization.map_injective _ u.injective),hc]

namespace Layers
variable {n : ℕ} [NeZero n]

private theorem row_gram (F : Full n) (a j k : Fin n) :
    inner ℂ (F.entry (a,j)) (F.entry (a,k)) = if j=k then 1 else 0 := by
  by_cases h : j=k
  · subst k
    simpa using inner_self_eq_one_of_norm_eq_one (𝕜:=ℂ) (F.unit ⟨(a,j),rfl⟩)
  · simpa [h] using F.rows a j k rfl rfl h

private theorem col_gram (F : Full n) (j a b : Fin n) :
    inner ℂ (F.entry (a,j)) (F.entry (b,j)) = if a=b then 1 else 0 := by
  by_cases h : a=b
  · subst b
    simpa using inner_self_eq_one_of_norm_eq_one (𝕜:=ℂ) (F.unit ⟨(a,j),rfl⟩)
  · simpa [h] using F.cols j a b rfl rfl h

def grid (F : Fin n → Fin n → Full n) : Grid (Fin n) := fun r c =>
  slot ((F (r.1+c.2) r.1).entry (r.2,c.1)) (r.1+c.2)

theorem valid (F : Fin n → Fin n → Full n) : Valid (grid F) := by
  constructor
  · rintro ⟨i,a⟩
    apply basis_of_gram
    rintro ⟨j,b⟩ ⟨k,c⟩
    by_cases hb : b=c
    · subst c
      simp [grid,row_gram]
    · simp [grid,hb]
  · rintro ⟨j,b⟩
    apply basis_of_gram
    rintro ⟨i,a⟩ ⟨k,c⟩
    by_cases hi : i=k
    · subst k
      simp [grid,col_gram]
    · simp [grid,hi]
  · intro i j
    apply basis_of_gram
    rintro ⟨a,b⟩ ⟨d,c⟩
    by_cases hb : b=c
    · subst c
      simp [grid,col_gram]
    · simp [grid,hb]

def embedSlot (y : Fin n) : Space n →ₗᵢ[ℂ] H (Fin n) :=
  LinearMap.isometryOfInner
    { toFun := fun v => slot v y
      map_add' := by intro v w; ext t; by_cases h : t.2=y <;> simp [slot,h]
      map_smul' := by intro z v; ext t; by_cases h : t.2=y <;> simp [slot,h] }
    (fun x y' => by simp)

def raySlot (y : Fin n) := Projectivization.map (embedSlot y).toLinearMap (embedSlot y).injective

theorem range_layers (F : Fin n → Fin n → Full n) :
    gridRays (valid F) = ⋃ y, raySlot y '' Collections.states (F y) := by
  ext z
  constructor
  · rintro ⟨⟨⟨i,a⟩,⟨j,b⟩⟩,rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+b,_,Collections.state_mem.mpr ⟨i,⟨(a,j),rfl⟩,rfl⟩,rfl⟩
  · intro hz
    obtain ⟨y,q,hq,rfl⟩ := Set.mem_iUnion.mp hz
    obtain ⟨i,p,rfl⟩ := Collections.state_mem.mp hq
    obtain ⟨⟨a,j⟩,hp⟩ := p
    refine ⟨((i,a),(j,y-i)),?_⟩
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨1,by simp [grid,embedSlot]⟩

omit [NeZero n] in
theorem different_slots (F : Fin n → Fin n → Full n) {y z : Fin n} (hne : y≠z) :
    Disjoint (raySlot y '' Collections.states (F y)) (raySlot z '' Collections.states (F z)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨q,hq,rfl⟩ ⟨t,ht,he⟩
  obtain ⟨i,p,rfl⟩ := Collections.state_mem.mp hq
  obtain ⟨j,r,rfl⟩ := Collections.state_mem.mp ht
  obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  let A := (F y i).entry p.val
  let B := (F z j).entry r.val
  change s • slot A y = slot B z at hs
  apply (F z j).nz r
  ext b
  have tb := congrArg (fun v : H (Fin n) => v (b,z)) hs
  simpa [slot,Ne.symm hne,B] using tb.symm

theorem gives_sum (F : Fin n → Fin n → Full n) :
    Realizes n (∑ y, (Collections.states (F y)).ncard) := by
  refine ⟨grid F,valid F,?_⟩
  rw [range_layers,Set.ncard_iUnion_of_finite
    (fun y => (Collections.finite_states (F y)).image _) (fun _ _ => different_slots F),
    finsum_eq_sum_of_fintype]
  exact sum_congr rfl (fun y _ => Set.ncard_image_of_injective _
    (Projectivization.map_injective _ (embedSlot y).injective))

end Layers
end QuantumSudoku
