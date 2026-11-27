module
public import Quantum.FractionalBellAllSizes

/-! The 24 real Peres rays and five exterior coordinate axes, placed in a
genuine size-three SudoQ. A projective rephasing gives Gaussian integer
numerators over two for every normalized entry. -/
@[expose] public section
noncomputable section
namespace FractionalBlockThree
open QuantumCertificate QuantumSudoku FractionalLayouts FractionalBlockBell
  FractionalPolygons.Sudoku Complex Finset
open scoped BigOperators ComplexConjugate

abbrev F := Fin 3
abbrev P := BigProb F
def order : Index F ≃ Fin 9 := finProdFinEquiv
def cell (r c : Fin 9) : Site F := (order.symm r,order.symm c)
def outcome : Index F := (1,1)
def reference : Site F := ((0,1),(0,1))

def signs : Fin 29 → Fin 9 → ℤ :=
    ![![1,0,0,0,0,0,0,0,0],
      ![0,1,0,0,0,0,0,0,0],
      ![0,0,1,0,0,0,0,0,0],
      ![0,0,0,1,0,0,0,0,0],
      ![0,0,0,0,1,0,0,0,0],
      ![0,0,0,0,0,1,0,0,0],
      ![0,0,0,0,0,0,1,0,0],
      ![0,0,0,0,0,0,0,1,0],
      ![0,0,0,0,0,0,0,0,1],
      ![0,0,1,-1,0,0,0,0,0],
      ![0,0,1,1,0,0,0,0,0],
      ![0,1,-1,0,0,0,0,0,0],
      ![0,1,0,-1,0,0,0,0,0],
      ![0,1,0,1,0,0,0,0,0],
      ![0,1,1,0,0,0,0,0,0],
      ![1,-1,0,0,0,0,0,0,0],
      ![1,0,-1,0,0,0,0,0,0],
      ![1,0,0,-1,0,0,0,0,0],
      ![1,0,0,1,0,0,0,0,0],
      ![1,0,1,0,0,0,0,0,0],
      ![1,1,0,0,0,0,0,0,0],
      ![1,-1,-1,-1,0,0,0,0,0],
      ![1,-1,-1,1,0,0,0,0,0],
      ![1,-1,1,-1,0,0,0,0,0],
      ![1,-1,1,1,0,0,0,0,0],
      ![1,1,-1,-1,0,0,0,0,0],
      ![1,1,-1,1,0,0,0,0,0],
      ![1,1,1,-1,0,0,0,0,0],
      ![1,1,1,1,0,0,0,0,0]]
def size : Fin 29 → ℕ := ![1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,4,4,4,4,4,4,4,4]
def rep (a : Fin 29) (k : Fin 9) : IQ :=
  let u := signs a k
  if size a=1 then (2*u,0) else if size a=2 then (u,u) else (u,0)

def layout : Fin 9 → Fin 9 → Fin 29 :=
    ![![6,8,7,4,16,13,27,5,24],
      ![5,1,3,8,7,19,4,6,16],
      ![2,0,4,6,12,5,7,8,13],
      ![1,10,0,7,6,8,5,9,4],
      ![8,9,5,25,28,4,15,7,6],
      ![4,7,6,23,5,22,10,20,8],
      ![7,6,14,18,23,25,8,4,5],
      ![18,4,11,5,8,7,6,21,27],
      ![17,5,8,14,4,6,26,24,7]]
def label (q : Site F) : Fin 29 := layout (order q.1) (order q.2)
def raw (q : Site F) := rep (label q)
def v (r c : Index F) : H F := WithLp.toLp 2 (fun k => vector 1 4 (raw (r,c)) (order k))
def reading := blockReadout 0 v

theorem inner_v (q h : Site F) :
    inner ℂ (v q.1 q.2) (v h.1 h.2)=(4:ℂ)⁻¹*embed 1 (gram 1 (raw q) (raw h)) := by
  rw [show (4:ℂ)⁻¹*embed 1 (gram 1 (raw q) (raw h))=
    inner ℂ (vector 1 4 (raw q)) (vector 1 4 (raw h)) from (inner_vector 1 4 _ _).symm]
  rw [PiLp.inner_apply,PiLp.inner_apply]
  exact Equiv.sum_comp order (fun k => inner ℂ (vector 1 4 (raw q) k) (vector 1 4 (raw h) k))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem certificate : ∀ d : Direction, ∀ k i j : Index F,
    gram 1 (raw (arrange d (k,i))) (raw (arrange d (k,j)))=
      if i=j then (4,0) else (0,0) := by intro d; cases d <;> decide +kernel

theorem v_valid : Valid v := by
  have line (d : Direction) (k i j : Index F) :
      inner ℂ (v (arrange d (k,i)).1 (arrange d (k,i)).2)
        (v (arrange d (k,j)).1 (arrange d (k,j)).2)=if i=j then 1 else 0 := by
    rw [inner_v,certificate]
    split <;> norm_num
  exact ⟨fun r => basis_of_gram _ (line .row r),fun c => basis_of_gram _ (line .column c),
    fun x y => basis_of_gram _ (line .block (x,y))⟩

def weight (r c : Fin 9) : ℤ :=
  let z := gram 1 (raw reference) (raw (cell r c))
  z.1^2+z.2^2

theorem outcome_weight (r c : Fin 9) :
    reading (cell r c) outcome=(weight r c:ℝ)/16 := by
  change normSq (inner ℂ (v reference.1 reference.2) (v (cell r c).1 (cell r c).2))=_
  rw [inner_v,Complex.normSq_mul,Complex.normSq_inv]
  norm_num [embed,weight,Complex.normSq_apply]
  ring

theorem target : reading (cell 0 6) outcome=1/4 := by
  rw [outcome_weight,show weight 0 6=4 by decide +kernel]
  norm_num

def permitted (r c : Fin 9) : Prop :=
  if r=2 then c=4 ∨ c=8 else if r=4 then c=3 ∨ c=4 ∨ c=6
  else if r=5 then c=3 ∨ c=5 ∨ c=7 else if r=8 then c=3 ∨ c=6 ∨ c=7 else True

instance (r c : Fin 9) : Decidable (permitted r c) := by unfold permitted; infer_instance

theorem forbidden_zero (r c : Fin 9) (h : ¬permitted r c) : reading (cell r c) outcome=0 := by
  have all : ∀ r c, ¬permitted r c → weight r c=0 := by decide +kernel
  rw [outcome_weight,all r c h]
  norm_num

theorem gaussian_coordinates (r c k : Index F) :
    ∃ a b : ℤ, v r c k=((a:ℂ)+(b:ℂ)*I)/2 := by
  refine ⟨(raw (r,c) (order k)).1,(raw (r,c) (order k)).2,?_⟩
  apply Complex.ext <;> norm_num [v,vector,embed,Complex.mul_re,Complex.mul_im] <;> ring

#print axioms v_valid
#print axioms target
end FractionalBlockThree

