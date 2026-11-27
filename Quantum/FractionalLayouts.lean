module
public import Quantum.FractionalDenseBasis
public import Quantum.FractionalIntercalate
public import Mathlib.Logic.Equiv.Fintype

/-! Inserting a four-by-four balanced pattern into a larger Sudoku preserves
each line's multiset. The unchanged exterior is tracked by permutations. -/
@[expose] public section
noncomputable section
namespace FractionalLayouts
open Function Equiv QuantumSudoku FractionalPolygons.Sudoku

inductive Direction | row | column | block deriving DecidableEq

def arrange {I : Type*} (d : Direction) : Site I ≃ Site I :=
  match d with
  | .row => Equiv.refl _
  | .column => Equiv.prodComm _ _
  | .block => {
      toFun := fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))
      invFun := fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def liftPair {I J : Type*} (t : I↪J) : Index I ↪ Index J := t.prodMap t
def liftSite {I J : Type*} (t : I↪J) : Site I ↪ Site J := liftPair (liftPair t)

theorem arrange_lift {I J : Type*} (d : Direction) (t : I↪J) (a b : Index I) :
    arrange d (liftPair t a,liftPair t b)=liftSite t (arrange d (a,b)) := by cases d <;> rfl

theorem inside_line {I J : Type*} (d : Direction) (t : I↪J) (a b : Index J) :
    arrange d (a,b)∈Set.range (liftSite t) ↔
      a∈Set.range (liftPair t) ∧ b∈Set.range (liftPair t) := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨⟨u,v⟩,rfl⟩ := (arrange d).surjective x
    rw [←arrange_lift] at hx
    have hp := (arrange d).injective hx
    exact ⟨⟨u,congrArg Prod.fst hp⟩,⟨v,congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    exact ⟨_,(arrange_lift d t u v).symm⟩

def fill {I J A : Type*} (t : I↪J) (small : Site I→A) (big : Site J→A) : Site J→A :=
  Function.extend (liftSite t) small big

theorem fill_at {I J A : Type*} (t : I↪J) (small : Site I→A) (big : Site J→A) (x : Site I) :
    fill t small big (liftSite t x)=small x :=
  (liftSite t).injective.extend_apply _ _ _

theorem shuffled {I J A : Type*} (d : Direction) (t : I↪J) (small : Site I→A) (big : Site J→A)
    (h : ∀ a, ∃ σ : Perm (Index I), ∀ b,
      small (arrange d (a,b))=big (liftSite t (arrange d (a,σ b)))) (k : Index J) :
    ∃ ρ : Perm (Index J), ∀ j, fill t small big (arrange d (k,j))=big (arrange d (k,ρ j)) := by
  classical
  by_cases hk : k∈Set.range (liftPair t)
  · obtain ⟨a,rfl⟩ := hk
    obtain ⟨σ,hs⟩ := h a
    let e := Equiv.ofInjective (liftPair t) (liftPair t).injective
    let ρ := σ.extendDomain e
    refine ⟨ρ,fun j => ?_⟩
    by_cases hj : j∈Set.range (liftPair t)
    · obtain ⟨b,rfl⟩ := hj
      have he : ρ (liftPair t b)=liftPair t (σ b) := σ.extendDomain_apply_image e b
      rw [he,arrange_lift,arrange_lift,fill_at]
      exact hs b
    · rw [show ρ j=j from σ.extendDomain_apply_not_subtype e hj]
      apply Function.extend_apply'
      exact fun hh => hj ((inside_line d t _ _).mp hh).2
  · refine ⟨Equiv.refl _,fun j => ?_⟩
    apply Function.extend_apply'
    exact fun hh => hk ((inside_line d t _ _).mp hh).1

/-- A common permutation sends each prescribed distinguished label to the
specified row of the orthostochastic matrix. -/
theorem align {K J : Type*} [Finite J] (s t : K↪J) :
    ∃ e : Perm J, ∀ i, e (s i)=t i := by
  classical
  let a := Equiv.ofInjective s s.injective
  let b := Equiv.ofInjective t t.injective
  let f := a.symm.trans b
  refine ⟨f.extendSubtype,fun i => ?_⟩
  have e := Equiv.extendSubtype_apply_of_mem f (s i) (Set.mem_range_self i)
  rw [e]
  change ((b (a.symm (a i))):J)=t i
  simp [b]

def symbol {I : Type*} (L : FractionalIntercalate.Latin I) (s : Site I) : Index I :=
  (L.op s.1.2 s.2.1,L.op s.2.2 s.1.1)

theorem symbol_bijective {I : Type*} (L : FractionalIntercalate.Latin I) (d : Direction)
    (a : Index I) : Bijective (fun b => symbol L (arrange d (a,b))) := by
  let : Nonempty I := ⟨a.1⟩
  rcases a with ⟨i,j⟩
  cases d
  · exact Prod.map_bijective.mpr ⟨L.row j,L.col i⟩
  · exact (Prod.map_bijective.mpr ⟨L.col i,L.row j⟩).comp (Equiv.prodComm _ _).bijective
  · exact Prod.map_bijective.mpr ⟨L.col j,L.col i⟩

def tinySymbol (s : Site (Fin 2)) : Index (Fin 2) := (s.1.2+s.2.1,s.2.2+s.1.1)

theorem symbol_lift {I : Type*} (L : FractionalIntercalate.Latin I) (s : Site (Fin 2)) :
    symbol L (liftSite L.tag s)=liftPair L.tag (tinySymbol s) := by
  rcases s with ⟨⟨i,a⟩,⟨j,b⟩⟩
  change (L.op (L.tag a) (L.tag j),L.op (L.tag b) (L.tag i))=_
  rw [L.sub,L.sub]; rfl

abbrev tiny := Index (Fin 2)
def number : tiny≃Fin 4 := finProdFinEquiv

def flag (s : Site (Fin 2)) : Bool :=
  ![![true,false,true,false],![false,true,false,true],![true,false,false,true],
    ![false,true,true,false]] (number s.1) (number s.2)

def shifts : Direction → Fin 4 → Fin 4 → Fin 4
  | .row => ![![0,2,1,3],![0,2,1,3],![0,2,3,1],![0,2,3,1]]
  | .column => ![![0,1,2,3],![1,0,3,2],![1,0,2,3],![0,1,3,2]]
  | .block => ![![0,2,3,1],![2,0,1,3],![0,2,3,1],![0,2,3,1]]

theorem shifts_injective (d : Direction) (k : Fin 4) : Injective (shifts d k) := by
  cases d <;> fin_cases k <;> decide +kernel

def tinyPerm (d : Direction) (k : tiny) : Perm tiny :=
  number.trans ((Equiv.ofBijective _ (Finite.injective_iff_bijective.mp
    (shifts_injective d (number k)))).trans number.symm)

theorem flag_shuffle : ∀ d k i,
    flag (arrange d (k,i))=decide ((tinySymbol (arrange d (k,tinyPerm d k i))).1=0) := by
  intro d; cases d <;> decide +kernel

theorem adjacent_lift {I J : Type*} (t : I↪J) {x y : Site I} (h : Adjacent x y) :
    Adjacent (liftSite t x) (liftSite t y) := by
  refine ⟨fun e => h.1 ((liftSite t).injective e),?_⟩
  rcases h.2 with row|col|⟨h1,h2⟩
  · exact Or.inl (congrArg (liftPair t) row)
  · exact Or.inr (Or.inl (congrArg (liftPair t) col))
  · exact Or.inr (Or.inr ⟨congrArg t h1,congrArg t h2⟩)

def walk5 (k : ℕ) : Site (Fin 2) :=
  let p : Fin 4 × Fin 4 := ![(0,0),(1,1),(3,1),(3,2),(0,2),(0,0)] ⟨k%6,Nat.mod_lt _ (by decide)⟩
  (number.symm p.1,number.symm p.2)

theorem walk5_edges : ∀ k : Fin 5, Adjacent (walk5 k) (walk5 (k.val+1)) := by
  unfold Adjacent; decide +kernel

theorem walk5_flags : ∀ k : Fin 6, flag (walk5 k)=true := by decide +kernel

def dist {I : Type*} [Fintype I] [DecidableEq I] (B : FractionalDenseBasis.Basis (Index I))
    (i a : Index I) : ℚ := B.m i a^2

structure Marked (I : Type*) [Fintype I] [DecidableEq I] where
  B : FractionalDenseBasis.Basis (Index I)
  p : Site I → Index I → ℚ
  lines : ∀ (d : Direction) (k : Index I), ∃ θ : Perm (Index I),
    ∀ j, p (arrange d (k,j))=dist B (θ j)
  length : ℕ
  odd : Odd length
  short : length≤7
  walk : ℕ → Site I
  closes : walk length=walk 0
  edges : ∀ k<length, Adjacent (walk k) (walk (k+1))
  flags : ∀ k≤length, p (walk k)=dist B (B.special 0)

theorem small_distribution {I : Type*} [Fintype I] [DecidableEq I]
    (B : FractionalDenseBasis.Basis (Index I)) (s : tiny) :
    dist B (B.special (number s))=
      if decide (s.1=0) then dist B (B.special 0) else dist B (B.special 2) := by
  rcases s with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact funext fun k => (B.sameA k).symm
  · rfl
  · exact funext fun k => (B.sameC k).symm

def fromLatin {I : Type*} [Fintype I] [DecidableEq I] (L : FractionalIntercalate.Latin I)
    (B : FractionalDenseBasis.Basis (Index I)) : Marked I := by
  apply Classical.choice
  obtain ⟨ρ,hρ⟩ := align (liftPair L.tag) (number.toEmbedding.trans B.special)
  let big : Site I → Index I → ℚ := fun x => dist B (ρ (symbol L x))
  let small : Site (Fin 2) → Index I → ℚ := fun x =>
    if flag x then dist B (B.special 0) else dist B (B.special 2)
  have old (x : Site (Fin 2)) : big (liftSite L.tag x)=
      if decide ((tinySymbol x).1=0) then dist B (B.special 0) else dist B (B.special 2) := by
    dsimp [big]
    rw [symbol_lift,hρ]
    exact small_distribution B _
  let p := fill L.tag small big
  refine ⟨{
    B := B
    p := p
    lines := ?_
    length := 5
    odd := by decide
    short := by decide
    walk := fun k => liftSite L.tag (walk5 k)
    closes := rfl
    edges := fun k hk => adjacent_lift L.tag (walk5_edges ⟨k,hk⟩)
    flags := ?_ }⟩
  · intro d a
    obtain ⟨γ,hγ⟩ := shuffled d L.tag small big (fun k => ⟨tinyPerm d k,fun i => by
      rw [old]; dsimp [small]; rw [flag_shuffle]⟩) a
    let e := Equiv.ofBijective _ (symbol_bijective L d a)
    exact ⟨(γ.trans e).trans ρ,hγ⟩
  · intro k hk
    change fill L.tag small big (liftSite L.tag (walk5 k))=_
    rw [fill_at]
    dsimp [small]
    rw [walk5_flags ⟨k,by omega⟩]; rfl

#print axioms fromLatin

end FractionalLayouts
