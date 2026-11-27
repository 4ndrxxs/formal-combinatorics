module
public import Quantum.FractionalBlockThreeClassical

/-! The first-block measurement of a genuine real SudoQ can lie outside the
scalar classical polytope in every size N ≥ 3. A separate gauge makes all
normalized coordinates Gaussian rational. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalPolygons.Sudoku Complex Finset
open scoped ComplexConjugate BigOperators

def RealCoordinates {I : Type*} [Fintype I] (v : Grid I) : Prop := ∀ r c k, (v r c k).im=0

def GaussianCoordinates {I : Type*} [Fintype I] (v : Grid I) : Prop :=
  ∀ r c k, ∃ a b : ℚ, v r c k=(a:ℂ)+(b:ℂ)*Complex.I

theorem rephase_valid {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J] (v : Grid J)
    (h : Valid v) (z : Site J → ℂ) (hz : ∀ q,normSq (z q)=1) :
    Valid (fun r c => z (r,c) • v r c) := by
  have basis {f : Index J → H J} (b : BasisLine f) (t : Index J → Site J) :
      BasisLine (fun k => z (t k) • f k) := by
    obtain ⟨B,he⟩ := b
    apply basis_of_gram
    intro i j
    rw [inner_smul_left,inner_smul_right,←congrFun he i,←congrFun he j,B.inner_eq_ite]
    by_cases eq : i=j
    · subst j; simp [mul_comm,Complex.mul_conj,hz]
    · simp [eq]
  exact ⟨fun r => basis (h.row r) (fun c => (r,c)),fun c => basis (h.column c) (fun r => (r,c)),
    fun r c => basis (h.block r c) (fun k => ((r,k.1),(c,k.2)))⟩

theorem block_rephase {J : Type*} [Fintype J] (v : Grid J)
    (z : Site J → ℂ) (hz : ∀ q,normSq (z q)=1) (r : J) :
    blockReadout r (fun i j => z (i,j) • v i j)=blockReadout r v := by
  funext q k
  simp only [blockReadout,inner_smul_left,inner_smul_right,Complex.normSq_mul,
    Complex.normSq_conj,hz,one_mul]

end FractionalBlockBell
namespace FractionalBlockThree
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalBlockBell FractionalPolygons.Sudoku
  Complex Finset
open scoped ComplexConjugate BigOperators

def phase (q : Site F) : ℂ := if size (label q)=2 then ((1:ℂ)-I)/(Real.sqrt 2:ℂ) else 1

theorem phase_unit (q : Site F) : normSq (phase q)=1 := by
  unfold phase
  split
  · rw [Complex.normSq_div,Complex.normSq_ofReal]
    norm_num [Complex.normSq_apply,Real.mul_self_sqrt]
  · simp

def realGrid : Grid F := fun r c => phase (r,c) • v r c

theorem real_grid : RealCoordinates realGrid := by
  intro r c k
  by_cases pair : size (label (r,c))=2
  · have zero : size (label (r,c))≠1 := by omega
    norm_num [realGrid,phase,pair,v,vector,embed,raw,rep,zero,
      Complex.mul_im,Complex.mul_re,Complex.div_re,Complex.div_im,Complex.normSq_ofReal]
    ring
  · by_cases single : size (label (r,c))=1 <;>
      norm_num [realGrid,phase,pair,v,vector,embed,raw,rep,single,Complex.mul_im]

theorem real_designated : Valid realGrid ∧ RealCoordinates realGrid ∧
    blockReadout 0 realGrid∉convexHull ℝ {p | Classical p} := by
  refine ⟨rephase_valid v v_valid phase phase_unit,real_grid,?_⟩
  change blockReadout 0 (fun i j => phase (i,j) • v i j)∉_
  rw [block_rephase v phase phase_unit]
  exact outside

theorem gaussian_grid : GaussianCoordinates v := by
  intro r c k
  obtain ⟨a,b,h⟩ := gaussian_coordinates r c k
  refine ⟨(a:ℚ)/2,(b:ℚ)/2,?_⟩
  rw [h]; push_cast; ring

end FractionalBlockThree
namespace FractionalBlockBell
open QuantumSudoku FractionalLayouts FractionalPolygons.Sudoku Complex
open scoped BigOperators

/-- Beyond sizes one and two the classical decomposition property fails in
every size, even with all grid vectors real and its first block measuring. -/
theorem real_designated_block_nonclassical (N : ℕ) (hN : 3≤N) :
    ∃ v : Grid (Fin N), Valid v ∧ RealCoordinates v ∧
      blockReadout (⟨0,by omega⟩ : Fin N) v∉convexHull ℝ {p | Classical p} := by
  by_cases h : N=3
  · subst N; exact ⟨FractionalBlockThree.realGrid,FractionalBlockThree.real_designated⟩
  · obtain ⟨v,hv,hr,hc⟩ := designated_block_nonclassical N (by omega)
    refine ⟨v,hv,fun r c k => ?_,hc⟩
    obtain ⟨a,ha⟩ := hr r c k
    rw [ha]; simp

/-- The same all-size failure has representatives entirely over Q(i). -/
theorem gaussian_designated_block_nonclassical (N : ℕ) (hN : 3≤N) :
    ∃ v : Grid (Fin N), Valid v ∧ GaussianCoordinates v ∧
      blockReadout (⟨0,by omega⟩ : Fin N) v∉convexHull ℝ {p | Classical p} := by
  by_cases h : N=3
  · subst N
    exact ⟨FractionalBlockThree.v,FractionalBlockThree.v_valid,FractionalBlockThree.gaussian_grid,
      FractionalBlockThree.outside⟩
  · obtain ⟨v,hv,hr,hc⟩ := designated_block_nonclassical N (by omega)
    refine ⟨v,hv,fun r c k => ?_,hc⟩
    obtain ⟨a,ha⟩ := hr r c k
    exact ⟨a,0,by simp [ha]⟩

#print axioms real_designated_block_nonclassical
#print axioms gaussian_designated_block_nonclassical
end FractionalBlockBell

