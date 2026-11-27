module
public import Quantum.SudokuTradeAtlas

/-! The second completion uses normalized four-dimensional Peres rays. All
exterior labels occupy their individual computational coordinate throughout. -/
@[expose] public section
noncomputable section
namespace SudokuTrade
variable [C : Config] [L : Laws]
open Laws
include L
open QuantumSudoku QuantumCertificate FractionalLayouts Finset Complex
open scoped ComplexConjugate

def axis (k : Pair) : H I := EuclideanSpace.single k 1

def spread (v : Space 4) : H I :=
  ∑ i : Color, EuclideanSpace.single (activeAxis i) (v i)

theorem spread_at (v : Space 4) (i : Color) : spread v (activeAxis i)=v i := by
  simp [spread,Pi.single_apply,axis_inj.eq_iff]

theorem spread_off (v : Space 4) {k : Pair} (hk : ¬∃ i, k=activeAxis i) : spread v k=0 := by
  have off (i : Color) : k≠activeAxis i := fun eq => hk ⟨i,eq⟩
  simp [spread,Pi.single_apply,off]

theorem spread_inner (v w : Space 4) : inner ℂ (spread v) (spread w)=inner ℂ v w := by
  conv_lhs => lhs; unfold spread
  rw [sum_inner,PiLp.inner_apply]
  apply sum_congr rfl
  intro i _
  simp [EuclideanSpace.inner_single_left,spread_at,mul_comm]

theorem axis_inner (a b : Pair) : inner ℂ (axis a) (axis b)=if a=b then 1 else 0 := by
  simp [axis,EuclideanSpace.inner_single_left,PiLp.single_apply]

theorem exterior_inner (v : Space 4) {k : Pair} (h : ¬∃ i, k=activeAxis i) :
    inner ℂ (axis k) (spread v)=0 := by simp [axis,EuclideanSpace.inner_single_left,spread_off v h]

def smallVec (r : I) (i : Color) := vector 1 16 (num (ray r i))

theorem frame_inner (d : Direction) (k : I) (i j : Color) :
    inner ℂ (smallVec (sourceRow d k i) i) (smallVec (sourceRow d k j) j)=
    if i=j then 1 else 0 := by
  rw [smallVec,smallVec,inner_vector,tested_frames]
  by_cases h : i=j <;> simp [h]

def value (r : I) (w : Pair) : H I :=
  if small : w.1.val<4 then
    if w.2=0 then spread (smallVec r ⟨w.1.val,small⟩) else axis w
  else axis w

@[simp] theorem value_active (r : I) (i : Color) : value r (activeAxis i)=spread (smallVec r i) := by
  simp [value,activeAxis,cap,i.isLt]

theorem value_ext (r : I) {w : Pair} (h : ¬∃ i,w=activeAxis i) : value r w=axis w := by
  unfold value
  split
  · rename_i lt
    split
    · rename_i zero
      exact (h ⟨⟨_,lt⟩,Prod.ext (Fin.ext rfl) zero⟩).elim
    · rfl
  · rfl

def field (r c t : I) := value r (word r c t)

theorem at_active (d : Direction) (k : I) (i : Color) :
    slice field d k (pos d k (activeAxis i))=spread (smallVec (sourceRow d k i) i) := by
  cases d with
  | row => change value _ (slice word .row k (pos .row k (activeAxis i)))=_
           rw [word_pos,value_active]; rfl
  | column => change value _ (slice word .column k (pos .column k (activeAxis i)))=_
              rw [word_pos,value_active]; rfl
  | block => change value _ (slice word .block k (pos .block k (activeAxis i)))=_
             rw [word_pos,value_active]; simp [pos,sourceRow,activeAxis]

theorem at_exterior (d : Direction) (k : I) {w : Pair} (h : ¬∃ i,w=activeAxis i) :
    slice field d k (pos d k w)=axis w := by
  cases d with
  | row => change value _ (slice word .row k (pos .row k w))=_
           rw [word_pos,value_ext _ h]
  | column => change value _ (slice word .column k (pos .column k w))=_
              rw [word_pos,value_ext _ h]
  | block => change value _ (slice word .block k (pos .block k w))=_
             rw [word_pos,value_ext _ h]

theorem gram_on_slice (d : Direction) (k : I) (p q : Pair) :
    inner ℂ (slice field d k p) (slice field d k q)=if p=q then 1 else 0 := by
  obtain ⟨u,rfl⟩ := (arranged d k).surjective p
  obtain ⟨w,rfl⟩ := (arranged d k).surjective q
  change inner ℂ (slice field d k (pos d k u)) (slice field d k (pos d k w))=
    if arranged d k u=arranged d k w then 1 else 0
  simp only [Equiv.apply_eq_iff_eq]
  by_cases activeU : ∃ i,u=activeAxis i
  · obtain ⟨i,rfl⟩ := activeU
    by_cases activeW : ∃ j,w=activeAxis j
    · obtain ⟨j,rfl⟩ := activeW
      simp only [at_active,spread_inner,frame_inner,axis_inj.eq_iff]
    · rw [at_active,at_exterior d k activeW,← inner_conj_symm,exterior_inner _ activeW]
      simp [show activeAxis i≠w from fun eq => activeW ⟨i,eq.symm⟩]
  · by_cases activeW : ∃ j,w=activeAxis j
    · obtain ⟨j,rfl⟩ := activeW
      rw [at_exterior d k activeU,at_active,exterior_inner _ activeU]
      simp [show u≠activeAxis j from fun eq => activeU ⟨j,eq⟩]
    · rw [at_exterior d k activeU,at_exterior d k activeW,axis_inner]

def quantumBoard : Grid I := SudokuCyclicLift.board field

theorem quantum_valid : Valid quantumBoard :=
  SudokuCyclicLift.valid field (gram_on_slice .row) (gram_on_slice .column) (gram_on_slice .block)

theorem small_reference {r : I} {i : Color} (eq : ray r i=refRay i) :
    spread (smallVec r i)=axis (activeAxis i) := by
  ext p
  by_cases h : ∃ j,p=activeAxis j
  · obtain ⟨j,rfl⟩ := h
    rw [spread_at]
    change (Real.sqrt (16:ℝ):ℂ)⁻¹ * embed 1 (num (ray r i) j)=_
    rw [eq,ref_num]
    by_cases ij : j=i <;> simp [ij,axis,PiLp.single_apply,axis_inj.eq_iff] <;> norm_num
  · rw [spread_off _ h]
    simp [axis,PiLp.single_apply,show p≠activeAxis i from fun eq => h ⟨i,eq⟩]

def QuantumCompletes (p : Pair→Pair→Option Pair) (v : Grid I) : Prop :=
  Valid v ∧ ∀ r c k, p r c=some k → ∃ z : Circle, v r c=(z:ℂ) • axis k

theorem quantum_completes : QuantumCompletes puzzle quantumBoard := by
  refine ⟨quantum_valid,?_⟩
  intro r c k given
  obtain rfl := (baseline_completes.2 r c k given).symm
  refine ⟨1,?_⟩
  simp only [Circle.coe_one,one_smul]
  change value r.2 (baseline r c)=axis (baseline r c)
  by_cases active : ∃ i, baseline r c=activeAxis i
  · obtain ⟨i,eq⟩ := active
    have h : ray r.2 i=refRay i := by
      by_contra ne
      simpa [puzzle,eq,activeAxis,cap,i.isLt,ne] using given
    rw [eq,value_active,small_reference h]
  · exact value_ext _ active

end SudokuTrade
