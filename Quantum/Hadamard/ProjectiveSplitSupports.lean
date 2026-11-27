import Quantum.Hadamard.TorusFrobeniusPaley

/-! The four cyclotomic sets displayed in Momihara, Suda and Xiang (2022),
Theorem 4.1, as supports of two finite blocks of a Paley conference matrix.
The border and the assembly of the two near-Hadamard classes are separate. -/

noncomputable section
open HadamardMod.TorusFrobenius

namespace Hadamard.MSXCore

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def cosetSign (i : Bool) : ℤ := if i then -1 else 1

def cyclo (i : Bool) : Set F := {x | quadraticChar F x=cosetSign i}

theorem mem_cyclo_zero (x : F) : x∈cyclo false ↔ x≠0 ∧ IsSquare x := by
  change quadraticChar F x=1 ↔ _
  by_cases h : x=0
  · simp [h]
  · rw [quadraticChar_one_iff_isSquare h]
    exact (and_iff_right h).symm

theorem mem_cyclo_one (x : F) : x∈cyclo true ↔ ¬IsSquare x := by
  exact quadraticChar_neg_one_iff_not_isSquare

/-- The sets (s(C_i+1)) intersected with the nonzero squares. The two
columns in Theorem 4.1 use s=1 and s equal to the chosen nonsquare. -/
def translated (s : F) (i : Bool) : Set F :=
  ((fun z : F ↦ s*(z+1)) '' cyclo i) ∩ cyclo false

theorem mem_translated {s t : F} (nz : s≠0) (i : Bool) :
    t∈translated s i ↔ quadraticChar F t=1 ∧ quadraticChar F (t/s-1)=cosetSign i := by
  constructor
  · rintro ⟨⟨x,hx,eq⟩,ht⟩
    refine ⟨ht,?_⟩
    rw [←eq,show s*(x+1)/s-1=x by field_simp; ring]
    exact hx
  · rintro ⟨ht,h⟩
    refine ⟨⟨t/s-1,h,?_⟩,ht⟩
    field_simp
    ring

/-- With square coordinates x,y, the within-square block and the mixed
block give the supports of all four translated sets. The mixed block
interchanges the two signs. -/
theorem split_core_supports (x y w : F) (hx : quadraticChar F x=1)
    (hy : quadraticChar F y=1) (hw : quadraticChar F w= -1) (i : Bool) :
    (x/y∈translated 1 i ↔ entry (some y) (some x)=cosetSign i) ∧
    (x/y∈translated w i ↔ entry (some (w*y)) (some x)= -cosetSign i) := by
  have yn : y≠0 := by intro h; subst y; simp at hy
  have wn : w≠0 := by intro h; subst w; simp at hw
  have ratio : quadraticChar F (x/y)=1 := by
    have id : y*(x/y)=x := by field_simp
    have h := congrArg (quadraticChar F) id
    simpa only [map_mul,hy,one_mul,hx] using h
  have plain : entry (some y) (some x)=quadraticChar F (x/y-1) := by
    change quadraticChar F (x-y)=_
    rw [show x-y=y*(x/y-1) by field_simp,map_mul,hy,one_mul]
  have mixed : entry (some (w*y)) (some x)= -quadraticChar F (x/y/w-1) := by
    change quadraticChar F (x-w*y)=_
    rw [show x-w*y=(w*y)*(x/y/w-1) by field_simp,map_mul,map_mul,hw,hy]
    ring
  rw [mem_translated one_ne_zero i,mem_translated wn i,plain,mixed]
  simp [ratio]

#print axioms split_core_supports

end Hadamard.MSXCore
