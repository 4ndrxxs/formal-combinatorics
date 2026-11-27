module
public import Quantum.FractionalBellMix

/-! A 3-4-5 rational real size-two SudoQ measured in a rational real basis,
outside the scalar classical Sudoku polytope by a single-symbol inequality. -/
@[expose] public section
noncomputable section
namespace FractionalBellWitness
open QuantumCertificate FractionalBinary FractionalBell Complex Finset
open scoped BigOperators

def raw (q : Site) (k : Fin 4) : ℤ :=
  (![![![60,-80,75,0],![-45,60,100,0],![80,60,0,75],![-60,-45,0,100]],
     ![![60,45,0,100],![80,60,0,-75],![45,-60,100,0],![60,-80,-75,0]],
     ![![91,12,-60,-60],![12,84,-45,80],![12,-91,-60,60],![84,-12,80,45]],
     ![![12,84,80,-45],![84,-37,60,60],![-84,12,45,80],![37,84,-60,60]]] :
    Fin 4 → Fin 4 → Fin 4 → ℤ) q.1 q.2 k

def data (q : Site) (k : Fin 4) : IQ := (raw q k,0)
def smallVector (q : Site) := vector 1 15625 (data q)
def smallTable (q : Site) (k : Fin 4) : ℝ := ((raw q k:ℝ)/125)^2

theorem small_grid : Grid smallVector := by
  intro l
  exact basis_of_test (by decide : 0<15625) _ ((by decide +kernel :
    ∀ l, GramTest 1 15625 (fun j => data (line l j))) l)

theorem small_born (q : Site) (k : Fin 4) : normSq (smallVector q k)=smallTable q k := by
  norm_num [smallVector,vector,data,smallTable,Complex.normSq_apply,
    Complex.mul_re,Complex.mul_im,Complex.inv_re,Complex.inv_im]
  ring

def oneScore (p : Prob) := ∑ q, mask q*p q 0
def maskZ (q : Site) : ℤ := if pattern q then 1 else -1

theorem classical_score {p : Prob} (h : ClassicalGrid p) : oneScore p≤2 := by
  obtain ⟨f,hj,born⟩ := h
  have row (r : Fin 4) : Function.Injective (fun c => f (r,c)) := by
    let l : Fin 12 := ⟨r.val,by omega⟩
    have hline (c : Fin 4) : line l c=(r,c) := by fin_cases r <;> fin_cases c <;> rfl
    simpa only [hline] using hj l
  have each (r : Fin 4) : ∃ c, f (r,c)=0 := (Finite.injective_iff_bijective.mp (row r)).surjective 0
  choose g hg using each
  have eqg (r c : Fin 4) : f (r,c)=0 ↔ c=g r :=
    ⟨fun he => row r (he.trans (hg r).symm),fun he => he ▸ hg r⟩
  have in_line (l : Fin 12) (i j : Fin 4) (hi : (line l i).2=g (line l i).1)
      (hk : (line l j).2=g (line l j).1) : i=j :=
    hj l (((eqg _ _).mpr hi).trans ((eqg _ _).mpr hk).symm)
  have enum : ∀ g : Fin 4 → Fin 4, (∀ l i j, (line l i).2=g (line l i).1 →
      (line l j).2=g (line l j).1 → i=j) →
      (∑ r, maskZ (r,g r))≤2 := by decide +kernel
  have val : oneScore p=∑ r, mask (r,g r) := by
    unfold oneScore
    rw [Fintype.sum_prod_type]
    simp [born,eqg,mul_ite]
  rw [val]
  have cast (q : Site) : (maskZ q:ℝ)=mask q := by simp [maskZ,mask]
  simpa only [←cast] using (show (∑ r,(maskZ (r,g r):ℝ))≤2 by exact_mod_cast enum _ in_line)

theorem convex_classical_score {p : Prob} (h : p∈convexHull ℝ {p | ClassicalGrid p}) : oneScore p≤2 := by
  have cv : Convex ℝ {p : Prob | oneScore p≤2} := by
    intro p hp q hq a b ha hb hab
    change oneScore p≤2 at hp
    change oneScore q≤2 at hq
    have linear : oneScore (a • p+b • q)=a*oneScore p+b*oneScore q := by
      simp only [oneScore,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
        ←Finset.sum_add_distrib]
      apply sum_congr rfl
      intro _ _
      ring
    change oneScore (a • p+b • q)≤2
    rw [linear]
    calc
      _≤a*2+b*2 := by gcongr
      _=2 := by linarith
  exact convexHull_min (fun _ hp => classical_score hp) cv h

theorem value : oneScore smallTable=36398/15625 := by
  norm_num [oneScore,Fintype.sum_prod_type,Fin.sum_univ_four,mask,pattern,smallTable,raw]

theorem outside : smallTable∉convexHull ℝ {p | ClassicalGrid p} := by
  intro h
  have b := convex_classical_score h
  rw [value] at b
  norm_num at b

theorem measured_outside : ArbitraryMeasurement smallTable ∧
    smallTable∉convexHull ℝ {p | ClassicalGrid p} :=
  ⟨any_basis.mpr ⟨smallVector,small_grid,small_born⟩,outside⟩

#print axioms measured_outside
end FractionalBellWitness

