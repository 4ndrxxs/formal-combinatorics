module
public import Quantum.DiagonalSix
public import Quantum.DiagonalSixColors

/-! The unordered orthogonal pairs of a fixed two-dimensional sector. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix Finset
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace Model
variable (g : Model)

theorem Xorth (i j : Tri) (hne : i≠j) : g.X i*g.X j=0 := by
  let H := g.X j
  have hh : Hᴴ=H := g.Xherm j
  have gram (k) : (g.X k*H)ᴴ*(g.X k*H)=H*g.X k*H := by
    rw [Matrix.conjTranspose_mul,hh,g.Xherm,mul_assoc,← mul_assoc (g.X k),g.Xidem,mul_assoc]
  have nn (k) : 0≤H*g.X k*H := by
    rw [← gram]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  have ht := congrArg (fun m : M => H*m*H) g.Xtotal
  simp only [Finset.mul_sum,Finset.sum_mul,mul_one,show H*H=H from g.Xidem j] at ht
  classical
  have z : ∑ k ∈ Finset.univ.erase j, H*g.X k*H=0 := by
    have e := Finset.sum_erase_add (s:=Finset.univ) (a:=j) (f:=fun k => H*g.X k*H) (by simp)
    rw [ht,show H*g.X j*H=H by dsimp [H]; rw [g.Xidem,g.Xidem]] at e
    exact add_right_cancel (b:=H) (show _+H=0+H by simpa using e)
  have zz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => nn k)).mp z i (by simp [hne])
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  exact (gram i).trans zz

theorem tile_eq (i j : Tri) : g.tile i j=g.P (label i j) := by
  let T := g.tile i j
  let P := g.P (label i j)
  have hu : Tᴴ=T := by simp [T,tile,e,Matrix.conjTranspose_sum,g.herm]
  have hm : T*T=T := by simp [T,tile,Finset.sum_mul,Finset.mul_sum,g.tileProd]
  have hp : T*P=T := by simp [T,P,tile,Finset.sum_mul,g.supported]
  have hP : Pᴴ=P := g.Pherm _
  have ph : P*T=T := by simpa only [Matrix.conjTranspose_mul,hP,hu] using congrArg Matrix.conjTranspose hp
  have tt (u v : Tri) : (g.tile u v).trace=4 := by
    simp [tile,e,Matrix.trace_sum,g.trace]
    <;> norm_num
  have z : P-T=0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [Matrix.conjTranspose_sub,hP,hu,sub_mul,mul_sub,mul_sub,hp,ph,hm,g.Pidem,
      sub_self,sub_zero,Matrix.trace_sub,show P.trace=4 from tt _ _,show T.trace=4 from tt _ _,sub_self]
  exact (sub_eq_zero.mp z).symm

/-- A sector as seen from any one of its cell projectors. -/
def pair (H p : M) : Finset M := by classical exact {p,H-p}

theorem pair_same {u v H : M} (s : u+v=H) : pair H u=pair H v := by
  classical
  have hv : H-u=v := by rw [← s]; abel
  have hu : H-v=u := by rw [← s]; abel
  simp [pair,hu,hv,Finset.pair_comm]

def occurs (k : Tri) (r c : Idx) := g.p r c*g.X k=g.p r c

def code (k : Tri) (C : Finset M → Colors.Code) (r c : Idx) : Colors.Code := by
  classical
  exact if g.occurs k r c then C (pair (g.X k) (g.p r c)) else 0

theorem code_line {α : Type} [Fintype α] (r c : α → Idx) (k : Tri)
    (cover : (∑ i, g.p (r i) (c i))*g.X k=g.X k) (C : Finset M → Colors.Code)
    (hnz : ∀ p, C p≠0) : Colors.line (fun i => g.code k C (r i) (c i)) := by
  classical
  obtain ⟨a,b,hab,hs,hh⟩ := g.slice_of_coverage k cover (fun i => g.trace _ _)
    (fun i => g.binary (r i) (c i) k)
  refine ⟨a,b,hab,?_,?_⟩
  · have ha := (hh a).mpr (Or.inl rfl)
    have hb := (hh b).mpr (Or.inr rfl)
    simp [code,occurs,ha,hb,pair_same hs]
  · intro i
    by_cases hit : g.occurs k (r i) (c i)
    · have hx := (hh i).mp hit
      simpa only [code,if_pos hit,iff_true_intro hx,iff_true] using hnz (pair (g.X k) (g.p (r i) (c i)))
    · have hx := mt (hh i).mpr hit
      simp [code,hit,hx]

theorem code_valid (k : Tri) (C : Finset M → Colors.Code) (hnz : ∀ p, C p≠0) :
    Colors.valid (g.code k C) k := by
  classical
  refine ⟨fun r => g.code_line (fun _ => r) id k (by simp [g.row]) C hnz,
    fun c => g.code_line id (fun _ => c) k (by simp [g.col]) C hnz,
    g.code_line id id k (by simpa only [id_eq,g.main,one_mul]) C hnz,
    g.code_line id (fun r => (r.1,r.2.rev)) k (by simpa only [id_eq,g.anti,one_mul]) C hnz,?_⟩
  intro i j
  split
  next h =>
    intro a b
    have z := g.missing i j (a,b)
    simp only [e,h] at z
    have ne : g.p (i,a) (j,b)≠0 := by
      intro he
      have t := g.trace (i,a) (j,b)
      simp [he] at t
    simp [code,occurs,z,ne.symm]
  next h =>
    apply g.code_line (fun ab : Pair => (i,ab.1)) (fun ab => (j,ab.2)) k _ C hnz
    change g.tile i j*g.X k=g.X k
    rw [g.tile_eq]
    have hf := g.Xorth (label i j) k h
    change (1-g.P (label i j))*g.X k=0 at hf
    rw [sub_mul,one_mul,sub_eq_zero] at hf
    exact hf.symm

end Model
end DiagonalSix
