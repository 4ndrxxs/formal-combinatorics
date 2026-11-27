module
public import Quantum.FractionalOddCycle
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Positive rational orthostochastic matrices with two prescribed pairs of
equal probability rows. The first pair puts 49/100 on each of two outcomes. -/
@[expose] public section
noncomputable section
namespace FractionalDenseBasis
open Finset Matrix Polynomial
open scoped BigOperators Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def Ortho (M : Matrix J J ℚ) : Prop :=
  ∀ i j, ∑ k, M i k*M j k=if i=j then 1 else 0

theorem Ortho.transpose {M : Matrix J J ℚ} (h : Ortho M) : Ortho Mᵀ := by
  have he : M*Mᵀ=1 := by
    ext i j
    simpa [Matrix.mul_apply,Matrix.one_apply] using h i j
  have ht := mul_eq_one_comm.mp he
  intro i j
  simpa [Matrix.mul_apply,Matrix.one_apply] using congrFun (congrFun ht i) j

theorem Ortho.reindex {M : Matrix I I ℚ} (h : Ortho M) (e : I≃J) :
    Ortho (fun i j => M (e.symm i) (e.symm j)) := by
  intro i j
  rw [←e.sum_comp]
  simpa using h (e.symm i) (e.symm j)

def rotate {J : Type*} [DecidableEq J] (a b : J) (c s : ℚ) (v : J → ℚ) (k : J) : ℚ :=
  if k=a then c*v a+s*v b else if k=b then -s*v a+c*v b else v k

private theorem splitSum (a b : J) (hn : a≠b) (f : J → ℚ) :
    ∑ i, f i=(∑ i ∈ (univ.erase a).erase b, f i)+f b+f a := by
  rw [sum_erase_add _ _ (by simp [Ne.symm hn]),sum_erase_add _ _ (mem_univ _)]

theorem rotate_dot (a b : J) (hn : a≠b) (c s : ℚ) (hcs : c^2+s^2=1) (v w : J → ℚ) :
    ∑ k, rotate a b c s v k*rotate a b c s w k = ∑ k, v k*w k := by
  rw [splitSum a b hn,splitSum a b hn (fun k => v k*w k)]
  have same : (∑ k ∈ (univ.erase a).erase b, rotate a b c s v k*rotate a b c s w k)=
      ∑ k ∈ (univ.erase a).erase b, v k*w k := by
    apply sum_congr rfl
    intro k hk
    simp only [mem_erase,mem_univ,and_true] at hk
    simp [rotate,hk.1,hk.2]
  rw [same]
  simp [rotate,Ne.symm hn]
  linear_combination (v a*w a+v b*w b)*hcs

theorem Ortho.rotateCols {M : Matrix J J ℚ} (h : Ortho M) (a b : J) (hn : a≠b)
    (c s : ℚ) (hcs : c^2+s^2=1) : Ortho (fun i => rotate a b c s (M i)) := by
  intro i j
  rw [rotate_dot a b hn c s hcs]
  exact h i j

theorem Ortho.rotateRows {M : Matrix J J ℚ} (h : Ortho M) (a b : J) (hn : a≠b)
    (c s : ℚ) (hcs : c^2+s^2=1) :
    Ortho (fun i j => rotate a b c s (fun k => M k j) i) :=
  (h.transpose.rotateCols a b hn c s hcs).transpose

def extended (M : Matrix J J ℚ) : Matrix (Option J) (Option J) ℚ
  | some i,some j => M i j
  | none,none => 1
  | _,_ => 0

theorem Ortho.extended {M : Matrix J J ℚ} (h : Ortho M) : Ortho (extended M) := by
  intro i j
  cases i <;> cases j <;> simp [FractionalDenseBasis.extended,Fintype.sum_option]
  exact h _ _

structure Basis (J : Type*) [Fintype J] [DecidableEq J] where
  m : Matrix J J ℚ
  gram : Ortho m
  nz : ∀ i j, m i j ≠ 0
  special : Fin 4 ↪ J
  left : J
  right : J
  distinct : left≠right
  sameA : ∀ j, m (special 0) j ^ 2=m (special 1) j ^ 2
  sameC : ∀ j, m (special 2) j ^ 2=m (special 3) j ^ 2
  massL : m (special 0) left ^ 2=49/100
  massR : m (special 0) right ^ 2=49/100

def Basis.reindex (d : Basis I) (e : I≃J) : Basis J where
  m i j := d.m (e.symm i) (e.symm j)
  gram := d.gram.reindex e
  nz _ _ := d.nz _ _
  special := d.special.trans e.toEmbedding
  left := e d.left
  right := e d.right
  distinct := fun h => d.distinct (e.injective h)
  sameA j := by simpa using d.sameA (e.symm j)
  sameC j := by simpa using d.sameC (e.symm j)
  massL := by simpa using d.massL
  massR := by simpa using d.massR

structure Extendable (J : Type*) [Fintype J] [DecidableEq J] extends Basis J where
  spare : J
  spare_ne : ∀ i, spare≠special i
  split : J
  split_ne : split≠left ∧ split≠right

def Extendable.reindex (d : Extendable I) (e : I≃J) : Extendable J where
  toBasis := d.toBasis.reindex e
  spare := e d.spare
  spare_ne i := fun h => d.spare_ne i (e.injective h)
  split := e d.split
  split_ne := ⟨fun h => d.split_ne.1 (e.injective h),fun h => d.split_ne.2 (e.injective h)⟩

private def numerator (a b : ℚ) : ℚ[X] := (1-X^2)*C a+2*X*C b

private theorem numerator_ne {a b : ℚ} (h : a≠0 ∨ b≠0) : numerator a b≠0 := by
  intro he
  have h0 := congrArg (Polynomial.eval 0) he
  have h1 := congrArg (Polynomial.eval 1) he
  simp [numerator] at h0 h1
  aesop

omit [DecidableEq J] in
theorem rational_rotation (x y : J → ℚ) (hn : ∀ j, x j≠0 ∨ y j≠0) :
    ∃ c s : ℚ, c^2+s^2=1 ∧
      ∀ j, c*x j+s*y j≠0 ∧ -s*x j+c*y j≠0 := by
  let bad : J → Set ℚ := fun j => {t | (numerator (x j) (y j)).IsRoot t} ∪
    {t | (numerator (y j) (-x j)).IsRoot t}
  have finite (j : J) : (bad j).Finite := by
    apply Set.Finite.union (finite_setOfPred_isRoot (numerator_ne (hn j)))
    apply finite_setOfPred_isRoot (numerator_ne ?_)
    rcases hn j with h|h
    · exact Or.inr (neg_ne_zero.mpr h)
    · exact Or.inl h
  obtain ⟨t,ht⟩ := (Set.finite_iUnion finite).exists_notMem
  let c := (1-t^2)/(1+t^2)
  let s := 2*t/(1+t^2)
  have den : 1+t^2≠0 := by nlinarith [sq_nonneg t]
  refine ⟨c,s,?_,fun j => ⟨?_,?_⟩⟩
  · dsimp [c,s]; field_simp; ring
  · intro he
    apply ht (Set.mem_iUnion.mpr ⟨j,Or.inl ?_⟩)
    change (numerator (x j) (y j)).eval t=0
    simp only [numerator,eval_add,eval_sub,eval_one,eval_pow,eval_X,eval_mul,eval_C,
      eval_ofNat]
    dsimp [c,s] at he
    field_simp [den] at he
    linear_combination he
  · intro he
    apply ht (Set.mem_iUnion.mpr ⟨j,Or.inr ?_⟩)
    change (numerator (y j) (-x j)).eval t=0
    simp only [numerator,eval_add,eval_sub,eval_one,eval_pow,eval_X,eval_mul,eval_C,
      eval_ofNat]
    dsimp [c,s] at he
    field_simp [den] at he
    linear_combination he

def Extendable.extend (d : Extendable J) : Extendable (Option J) := by
  apply Classical.choice
  let A : Matrix (Option J) (Option J) ℚ :=
    fun i => rotate (some d.split) none (3/5) (4/5) ((extended d.m) i)
  have gramA : Ortho A :=
    d.gram.extended.rotateCols (some d.split) none (by simp) _ _ (by norm_num)
  have old (i : J) (j : Option J) : A (some i) j≠0 := by
    cases j with
    | none => simp [A,rotate,extended,d.nz]
    | some k =>
      by_cases h : k=d.split <;> simp [A,rotate,extended,h,d.nz]
  have saved (i j : J) (h : ∀ k, d.m i k^2=d.m j k^2) (k : Option J) :
      A (some i) k^2=A (some j) k^2 := by
    cases k with
    | none => simp [A,rotate,extended,mul_pow,h]
    | some k =>
      by_cases eq : k=d.split <;> simp [A,rotate,extended,eq,mul_pow,h]
  obtain ⟨c,s,cs,good⟩ := rational_rotation (A (some d.spare)) (A none)
    (fun j => Or.inl (old _ j))
  let B : Matrix (Option J) (Option J) ℚ :=
    fun i j => rotate (some d.spare) none c s (fun k => A k j) i
  have keep (i : J) (hi : i≠d.spare) (j : Option J) : B (some i) j=A (some i) j := by
    simp [B,rotate,hi]
  let special : Fin 4 ↪ Option J := d.special.trans ⟨some,Option.some_injective _⟩
  have kept (i : Fin 4) (j : Option J) : B (special i) j=A (some (d.special i)) j :=
    keep _ (Ne.symm (d.spare_ne i)) _
  refine ⟨{
    m := B
    gram := gramA.rotateRows (some d.spare) none (by simp) c s cs
    nz := ?_
    special := special
    left := some d.left
    right := some d.right
    distinct := by simpa using d.distinct
    sameA := ?_
    sameC := ?_
    massL := ?_
    massR := ?_
    spare := some d.spare
    spare_ne := ?_
    split := some d.split
    split_ne := ?_ }⟩
  · intro i j
    cases i with
    | none => simpa [B,rotate] using (good j).2
    | some i =>
      by_cases hi : i=d.spare
      · subst i; simpa [B,rotate] using (good j).1
      · rw [keep _ hi]; exact old _ _
  · intro j; simpa only [kept] using saved _ _ d.sameA j
  · intro j; simpa only [kept] using saved _ _ d.sameC j
  · simpa [kept,A,rotate,extended,Ne.symm d.split_ne.1] using d.massL
  · simpa [kept,A,rotate,extended,Ne.symm d.split_ne.2] using d.massR
  · intro i; simpa [special] using d.spare_ne i
  · simpa using d.split_ne

def fourM : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  ![![7,7,1,1],![7,-7,1,-1],![1,1,-7,-7],![1,-1,-7,7]] i j / 10

def four : Basis (Fin 4) where
  m := fourM
  gram := by unfold Ortho; decide +kernel
  nz := by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
  special := Function.Embedding.refl _
  left := 0
  right := 1
  distinct := by decide
  sameA := by decide +kernel
  sameC := by decide +kernel
  massL := by decide +kernel
  massR := by decide +kernel

def sixM : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  ![![525,525,45,45,60,60],![525,-525,45,-45,60,-60],
    ![25,25,-505,-505,160,160],![25,-25,-505,505,160,-160],
    ![-60,-80,132,176,426,568],![-80,60,176,-132,568,-426]] i j/750

def includeFour : Fin 4 ↪ Fin 6 := Fin.castLEEmb (by omega)

def six : Extendable (Fin 6) where
  m := sixM
  gram := by unfold Ortho; decide +kernel
  nz := by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
  special := includeFour
  left := 0
  right := 1
  distinct := by decide
  sameA := by decide +kernel
  sameC := by decide +kernel
  massL := by decide +kernel
  massR := by decide +kernel
  spare := 5
  spare_ne := by decide
  split := 5
  split_ne := by decide

def fromSix : (k : ℕ) → Extendable (Fin (6+k))
  | 0 => six
  | k+1 => (fromSix k).extend.reindex (Fintype.equivOfCardEq (by simp; omega))

def ofCard (h : Fintype.card J=4 ∨ 6≤Fintype.card J) : Basis J := by
  apply Classical.choice
  rcases h with h|h
  · exact ⟨four.reindex (Fintype.equivOfCardEq (by simpa using h.symm))⟩
  · exact ⟨(fromSix (Fintype.card J-6)).toBasis.reindex (Fintype.equivOfCardEq (by simp;omega))⟩

#print axioms ofCard

end FractionalDenseBasis
