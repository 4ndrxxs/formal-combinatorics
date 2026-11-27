module
public import Quantum.FractionalBlockThreeClassical
public import Quantum.FractionalBellClassicalReverse

/-! Every legal placement of one digit extends to an ordinary Sudoku.
The six permutations record the positions within three bands and stacks. -/
@[expose] public section
noncomputable section
namespace FractionalBlockThree
open QuantumSudoku FractionalLayouts FractionalBlockBell FractionalPolygons.Sudoku Finset
open scoped BigOperators

abbrev Marginal := Site F → ℝ
def project : P →ₗ[ℝ] Marginal where
  toFun p q := p q outcome
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectedHull : Set Marginal := project '' convexHull ℝ {p : P | Classical p}

theorem projected_convex : Convex ℝ projectedHull :=
  (convex_convexHull ℝ {p : P | Classical p}).linear_image project

def permutations3 : Fin 6 → F → F :=
  ![![0,1,2],![0,2,1],![1,0,2],![1,2,0],![2,0,1],![2,1,0]]

def perm (i : Fin 6) : Equiv.Perm F := Equiv.ofBijective (permutations3 i)
  (Finite.injective_iff_bijective.mp ((by decide +kernel : ∀ i, Function.Injective (permutations3 i)) i))

def placement (A B : F→Fin 6) (q : Site F) : Prop :=
  q.1.2=permutations3 (A q.1.1) q.2.1 ∧ q.2.2=permutations3 (B q.2.1) q.1.1

instance (A B : F→Fin 6) (q : Site F) : Decidable (placement A B q) := by
  unfold placement
  infer_instance

def fillSymbol (A B : F→Fin 6) (q : Site F) : Index F :=
  ((perm (A q.1.1)).symm q.1.2-q.2.1+1, (perm (B q.2.1)).symm q.2.2-q.1.1+1)

theorem fillSymbol_lines (A B : F→Fin 6) (d : Direction) (k : Index F) :
    Function.Injective (fun j => fillSymbol A B (arrange d (k,j))) := by
  rcases k with ⟨x,a⟩
  rintro ⟨y,b⟩ ⟨z,c⟩ h
  cases d
  · change ((perm (A x)).symm a-y+1,(perm (B y)).symm b-x+1)=
        ((perm (A x)).symm a-z+1,(perm (B z)).symm c-x+1) at h
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
    have e : y=z := sub_right_injective (add_right_cancel h₁)
    subst z
    exact Prod.ext rfl ((perm (B y)).symm.injective (sub_left_inj.mp (add_right_cancel h₂)))
  · change ((perm (A y)).symm b-x+1,(perm (B x)).symm a-y+1)=
        ((perm (A z)).symm c-x+1,(perm (B x)).symm a-z+1) at h
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
    have e : y=z := sub_right_injective (add_right_cancel h₂)
    subst z
    exact Prod.ext rfl ((perm (A y)).symm.injective (sub_left_inj.mp (add_right_cancel h₁)))
  · change ((perm (A x)).symm y-a+1,(perm (B a)).symm b-x+1)=
        ((perm (A x)).symm z-a+1,(perm (B a)).symm c-x+1) at h
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj h
    exact Prod.ext ((perm (A x)).symm.injective (sub_left_inj.mp (add_right_cancel h₁)))
      ((perm (B a)).symm.injective (sub_left_inj.mp (add_right_cancel h₂)))

theorem fillSymbol_iff (A B : F→Fin 6) (q : Site F) : fillSymbol A B q=outcome ↔ placement A B q := by
  rcases q with ⟨⟨x,a⟩,⟨y,b⟩⟩
  change ((perm (A x)).symm a-y+1,(perm (B y)).symm b-x+1)=((1:F),1) ↔
    a=(perm (A x)) y ∧ b=(perm (B y)) x
  have cancel (t : F) : t+1=1 ↔ t=0 := by
    constructor
    · intro h
      simpa using h
    · rintro rfl
      simp
  simp only [Prod.mk.injEq,cancel,sub_eq_zero,Equiv.symm_apply_eq]

def marginal (A B : F→Fin 6) : Marginal := fun q => if placement A B q then 1 else 0

theorem marginal_mem (A B : F→Fin 6) : marginal A B∈projectedHull := by
  refine ⟨atomic (fillSymbol A B),subset_convexHull ℝ _ ⟨_,fillSymbol_lines A B,fun _ _ => rfl⟩,?_⟩
  ext q
  change (if fillSymbol A B q=outcome then (1:ℝ) else 0)=_
  simp [marginal,fillSymbol_iff]

def flat : Marginal := fun _ => 1/9

theorem flat_mem : flat∈projectedHull := by
  refine ⟨_,uniform_in_hull (I:=F),?_⟩
  ext q
  change (Fintype.card (Index F):ℝ)⁻¹=1/9
  norm_num [F,Index]

def mix (eta : ℝ) : Marginal := eta • project reading+(1-eta) • flat

#print axioms marginal_mem
end FractionalBlockThree
