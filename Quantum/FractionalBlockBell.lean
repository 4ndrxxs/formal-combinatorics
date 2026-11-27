module
public import Quantum.FractionalBellWitness
public import Quantum.FractionalLayouts

/-! A size-two SudoQ may replace the sixteen entries on a Latin intercalate
inside a larger classical Sudoku. Every full line remains an orthonormal basis. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalIntercalate
  FractionalPolygons.Sudoku Function Equiv Complex Finset
open scoped ComplexConjugate BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev BigProb (I : Type*) := Site I → Index I → ℝ
abbrev SmallProb := FractionalBinary.Prob

def fromTiny (s : Site (Fin 2)) : FractionalBinary.Site := (number s.1,number s.2)
def toTiny (s : FractionalBinary.Site) : Site (Fin 2) := (number.symm s.1,number.symm s.2)
@[simp] theorem fromTiny_toTiny (s : FractionalBinary.Site) : fromTiny (toTiny s)=s := by simp [fromTiny,toTiny]
@[simp] theorem toTiny_fromTiny (s : Site (Fin 2)) : toTiny (fromTiny s)=s := by simp [fromTiny,toTiny]

def lineNum (d : Direction) (a : tiny) : Fin 12 :=
  match d with
  | .row => ⟨(number a).val,by omega⟩
  | .column => ⟨4+(number a).val,by omega⟩
  | .block => ⟨8+(number a).val,by omega⟩

theorem tiny_line (d : Direction) (a b : tiny) :
    fromTiny (arrange d (a,b))=FractionalBinary.line (lineNum d a) (number b) := by
  cases d <;> revert a b <;> decide +kernel

theorem all_tiny_lines : ∀ l, ∃ d a, lineNum d a=l := by
  intro l
  fin_cases l <;> first
    | exact ⟨.row,number.symm 0,rfl⟩ | exact ⟨.row,number.symm 1,rfl⟩
    | exact ⟨.row,number.symm 2,rfl⟩ | exact ⟨.row,number.symm 3,rfl⟩
    | exact ⟨.column,number.symm 0,rfl⟩ | exact ⟨.column,number.symm 1,rfl⟩
    | exact ⟨.column,number.symm 2,rfl⟩ | exact ⟨.column,number.symm 3,rfl⟩
    | exact ⟨.block,number.symm 0,rfl⟩ | exact ⟨.block,number.symm 1,rfl⟩
    | exact ⟨.block,number.symm 2,rfl⟩ | exact ⟨.block,number.symm 3,rfl⟩

def coordinate (L : Latin I) : Fin 4 ↪ Index I := number.symm.toEmbedding.trans (liftPair L.tag)
def position (L : Latin I) (q : FractionalBinary.Site) : Site I := liftSite L.tag (toTiny q)

def axis (k : Index I) : H I := EuclideanSpace.single k 1
def includeVector (L : Latin I) (v : Space 4) : H I := ∑ k, v k • axis (coordinate L k)

@[simp] theorem axis_inner (i j : Index I) : inner ℂ (axis i) (axis j)=if i=j then 1 else 0 := by
  simp [axis,EuclideanSpace.inner_single_left,PiLp.single_apply]

theorem include_at (L : Latin I) (v : Space 4) (k : Fin 4) : includeVector L v (coordinate L k)=v k := by
  simp [includeVector,axis,Pi.single_apply,(coordinate L).injective.eq_iff]

theorem include_out (L : Latin I) (v : Space 4) (k : Index I) (h : k∉Set.range (coordinate L)) :
    includeVector L v k=0 := by
  have hn (i : Fin 4) : coordinate L i≠k := fun he => h ⟨i,he⟩
  simp [includeVector,axis,hn]

theorem include_inner (L : Latin I) (v w : Space 4) :
    inner ℂ (includeVector L v) (includeVector L w)=inner ℂ v w := by
  rw [show includeVector L v=∑ k,v k • axis (coordinate L k) by rfl,sum_inner]
  simp [inner_smul_left,axis,include_at,PiLp.inner_apply,mul_comm]

theorem axis_include_out (L : Latin I) (w : Space 4) {k : Index I} (h : k∉Set.range (coordinate L)) :
    inner ℂ (axis k) (includeVector L w)=0 := by
  simp [axis,EuclideanSpace.inner_single_left,include_out _ _ _ h]

def inserted (L : Latin I) (v : FractionalBinary.Site → Space 4) (q : Site I) : H I :=
  fill L.tag (fun q => includeVector L (v (fromTiny q))) (fun q => axis (symbol L q)) q

theorem inserted_inside (L : Latin I) (v : FractionalBinary.Site → Space 4) (q : Site (Fin 2)) :
    inserted L v (liftSite L.tag q)=includeVector L (v (fromTiny q)) := fill_at _ _ _ _

theorem inserted_outside (L : Latin I) (v : FractionalBinary.Site → Space 4) (q : Site I)
    (h : q∉Set.range (liftSite L.tag)) : inserted L v q=axis (symbol L q) := by
  unfold inserted fill
  exact Function.extend_apply' _ (fun z => axis (symbol L z)) q h

theorem tiny_symbol_surj (d : Direction) (k : tiny) :
    Surjective (fun b => tinySymbol (arrange d (k,b))) := by cases d <;> revert k <;> decide +kernel

omit [Fintype I] [DecidableEq I] in
theorem exterior_symbol (L : Latin I) (d : Direction) (k : tiny) (j : Index I)
    (h : j∉Set.range (liftPair L.tag)) :
    symbol L (arrange d (liftPair L.tag k,j))∉Set.range (coordinate L) := by
  rintro ⟨a,ha⟩
  obtain ⟨b,hb⟩ := tiny_symbol_surj d k (number.symm a)
  change tinySymbol (arrange d (k,b))=number.symm a at hb
  have he : symbol L (arrange d (liftPair L.tag k,liftPair L.tag b))=coordinate L a := by
    rw [arrange_lift,symbol_lift,hb]
    rfl
  exact h ⟨b,(symbol_bijective L d _).injective (he.trans ha)⟩

theorem inserted_gram (L : Latin I) (v : FractionalBinary.Site → Space 4) (valid : FractionalBinary.Grid v)
    (d : Direction) (k i j : Index I) :
    inner ℂ (inserted L v (arrange d (k,i))) (inserted L v (arrange d (k,j)))=
      if i=j then 1 else 0 := by
  classical
  have outside (k i : Index I) (h : ¬(k∈Set.range (liftPair L.tag) ∧ i∈Set.range (liftPair L.tag))) :
      inserted L v (arrange d (k,i))=axis (symbol L (arrange d (k,i))) :=
    inserted_outside _ _ _ (fun hh => h ((inside_line d _ _ _).mp hh))
  by_cases hk : k∈Set.range (liftPair L.tag)
  · obtain ⟨a,rfl⟩ := hk
    by_cases hi : i∈Set.range (liftPair L.tag) <;> by_cases hj : j∈Set.range (liftPair L.tag)
    · obtain ⟨r,rfl⟩ := hi
      obtain ⟨c,rfl⟩ := hj
      obtain ⟨B,hB⟩ := valid (lineNum d a)
      rw [arrange_lift,arrange_lift,inserted_inside,inserted_inside,include_inner,tiny_line,tiny_line,
        ←congrFun hB (number r),←congrFun hB (number c),B.inner_eq_ite]
      simp [(liftPair L.tag).injective.eq_iff]
    · obtain ⟨r,rfl⟩ := hi
      rw [outside _ _ (fun hh => hj hh.2),arrange_lift,inserted_inside,←inner_conj_symm]
      rw [axis_include_out L _ (exterior_symbol L d a j hj)]
      simp [show liftPair L.tag r≠j from fun e => hj ⟨r,e⟩]
    · obtain ⟨r,rfl⟩ := hj
      rw [outside _ _ (fun hh => hi hh.2),arrange_lift,inserted_inside,
        axis_include_out L _ (exterior_symbol L d a i hi)]
      simp [show i≠liftPair L.tag r from fun e => hi ⟨r,e.symm⟩]
    · rw [outside _ _ (fun hh => hi hh.2),outside _ _ (fun hh => hj hh.2),axis_inner]
      simp [(symbol_bijective L d _).injective.eq_iff]
  · rw [outside _ _ (fun hh => hk hh.1),outside _ _ (fun hh => hk hh.1),axis_inner]
    simp [(symbol_bijective L d _).injective.eq_iff]

/-- Every size-two SudoQ inserts into every intercalate-bearing larger order. -/
theorem inserted_valid (L : Latin I) (v : FractionalBinary.Site → Space 4) (valid : FractionalBinary.Grid v) :
    Valid (fun r c => inserted L v (r,c)) := by
  let : Nonempty I := ⟨L.tag 0⟩
  constructor
  · intro r
    exact basis_of_gram _ (inserted_gram L v valid .row r)
  · intro c
    exact basis_of_gram _ (inserted_gram L v valid .column c)
  · intro i j
    exact basis_of_gram _ (inserted_gram L v valid .block (i,j))

def bareTable (L : Latin I) (v : FractionalBinary.Site → Space 4) : BigProb I :=
  fun q k => normSq (inserted L v q k)

theorem trim_bare (L : Latin I) (v : FractionalBinary.Site → Space 4) (q : FractionalBinary.Site)
    (k : Fin 4) : bareTable L v (position L q) (coordinate L k)=normSq (v q k) := by
  rw [bareTable,position,inserted_inside,fromTiny_toTiny,include_at]

theorem bare_supported (L : Latin I) (v : FractionalBinary.Site → Space 4) (q : FractionalBinary.Site)
    (k : Index I) (h : k∉Set.range (coordinate L)) : bareTable L v (position L q) k=0 := by
  rw [bareTable,position,inserted_inside,include_out L _ _ h]
  exact Complex.normSq_zero

#print axioms inserted_valid
end FractionalBlockBell

