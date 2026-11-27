module
public import Quantum.FractionalNoisy
public import Mathlib.Analysis.Matrix.Order

/-! A genuine positive-operator-valued measurement on a SudoQ and its
Hermitian contrast. Its basis-independent entry and trace bounds use the
matrix Loewner order. -/
@[expose] public section
noncomputable section
namespace FractionalBell
open QuantumCertificate FractionalBinary FractionalPositive FractionalProjectors
  FractionalTensor Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder Matrix MatrixOrder BigOperators

def mask (q : Site) : ℝ := if pattern q then 1 else -1
def weightSign : Fin 4 → ℝ := ![1,1,-1,-1]
def family (t : ℝ) := noisy ((1-t)/2)

theorem family_apply (t : ℝ) (q : Site) (a : Fin 4) :
    family t q a=(1+t*mask q*weightSign a)/4 := by
  unfold family noisy noisyWeight mask
  cases e : pattern q <;> fin_cases a <;> norm_num [first,second,weightSign] <;> ring

/-- Independently chosen pure unit readout states on the very same grid. -/
def Separate (p : Prob) : Prop :=
  ∃ v : Site → Space 4, Grid v ∧ ∀ k, ∃ f : Space 4, ‖f‖=1 ∧
    ∀ q, Complex.normSq (inner ℂ f (v q))=p q k

/-- A four-outcome POVM in the same Hilbert space as the grid. -/
def Generalized (p : Prob) : Prop :=
  ∃ (v : Site → Space 4) (E : Fin 4 → M), Grid v ∧ (∀ k, (E k).PosSemidef) ∧
    (∑ k, E k)=1 ∧ ∀ q k, expectation (⇑(v q)) (E k)=p q k

def pairing (H K : M) : ℝ := (H*K).trace.re

theorem pairing_projection (H : M) (v : V) :
    pairing H (projection v)=expectation v H := by
  simp [pairing,expectation,projection,ip,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

@[simp] theorem pairing_add (H K L : M) : pairing H (K+L)=pairing H K+pairing H L := by
  simp [pairing,mul_add]
@[simp] theorem pairing_neg (H K : M) : pairing H (-K)= -pairing H K := by simp [pairing]
@[simp] theorem pairing_sub (H K L : M) : pairing H (K-L)=pairing H K-pairing H L := by
  simp [pairing,mul_sub]

theorem conjugate_pair_mul (T : M) (h : T*Tᴴ=1) (H K : M) :
    (Tᴴ*H*T)*(Tᴴ*K*T)=Tᴴ*(H*K)*T := by
  calc
    _ = Tᴴ*H*(T*Tᴴ)*K*T := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [h,Matrix.mul_assoc]

theorem pairing_change (T : M) (h : T*Tᴴ=1) (H K : M) :
    pairing (Tᴴ*H*T) (Tᴴ*K*T)=pairing H K := by
  unfold pairing
  rw [conjugate_pair_mul _ h,Matrix.trace_mul_cycle,h,one_mul]

structure Contract (H : M) : Prop where
  herm : Hᴴ=H
  defect : (1-H*H).PosSemidef

theorem Contract.change {H : M} (C : Contract H) (T : M) (h : T*Tᴴ=1) :
    Contract (Tᴴ*H*T) where
  herm := by simp [C.herm,Matrix.mul_assoc]
  defect := by
    rw [conjugate_pair_mul _ h]
    have he : Tᴴ*(1-H*H)*T = 1-Tᴴ*(H*H)*T := by
      simp [Matrix.sub_mul,Matrix.mul_sub,mul_eq_one_comm.mp h]
    exact he ▸ C.defect.conjTranspose_mul_mul_same T

theorem Contract.energy_col {H : M} (C : Contract H) (j : Fin 4) :
    (∑ i, normSq (H i j))≤1 := by
  have dd : (1-Hᴴ*H).PosSemidef := by rw [C.herm]; exact C.defect
  have he : 0≤((1-Hᴴ*H) j j).re := (dd.diag_nonneg (i:=j)).1
  have elem (z : ℂ) : (conj z*z).re=normSq z := by rw [mul_comm,Complex.mul_conj]; rfl
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,elem] using he

theorem Contract.entry {H : M} (C : Contract H) (i j : Fin 4) : normSq (H i j)≤1 :=
  (Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (H k j)) (mem_univ i)).trans (C.energy_col j)

theorem Contract.of_involution {H : M} (h : Hᴴ=H) (square : H*H=1) : Contract H :=
  ⟨h,by rw [square,sub_self]; exact PosSemidef.zero⟩

open scoped Matrix.Norms.L2Operator in
theorem Contract.of_pos {H : M} (h : Hᴴ=H) (plus : (1+H).PosSemidef) (minus : (1-H).PosSemidef) :
    Contract H := by
  have comm : Commute (1+H) (1-H) := by change _*_= _*_; noncomm_ring
  have he : (1+H)*(1-H)=1-H*H := by noncomm_ring
  exact ⟨h,he ▸ Matrix.nonneg_iff_posSemidef.mp (comm.mul_nonneg plus.nonneg minus.nonneg)⟩

def contrast (E : Fin 4 → M) := (E 0+E 1)-(E 2+E 3)

theorem contract_contrast (E : Fin 4 → M) (hp : ∀ k, (E k).PosSemidef) (hs : ∑ k, E k=1) :
    Contract (contrast E) := by
  have hpos := (hp 0).add (hp 1)
  have hneg := (hp 2).add (hp 3)
  have he : (E 0+E 1)+(E 2+E 3)=1 := by simpa [Fin.sum_univ_four,add_assoc] using hs
  apply Contract.of_pos
  · simp [contrast,(hp 0).isHermitian.eq,(hp 1).isHermitian.eq,(hp 2).isHermitian.eq,
      (hp 3).isHermitian.eq]
  · rw [←he]
    convert hpos.add hpos using 1
    unfold contrast
    abel
  · rw [←he]
    convert hneg.add hneg using 1
    unfold contrast
    abel

theorem unit_ip {f : Space 4} (h : ‖f‖=1) : ip (⇑f) (⇑f)=1 := by
  rw [ip_inner,inner_self_eq_norm_sq_to_K,h]
  norm_num

theorem projective_contrast {f : Space 4} (h : ‖f‖=1) :
    Contract (projection (⇑f)+projection (⇑f)-1) := by
  let P := projection (⇑f)
  have pp : P*P=P := by
    change vecMulVec _ _*vecMulVec _ _=_
    rw [Matrix.vecMulVec_mul_vecMulVec]
    change vecMulVec (⇑f) ((ip (⇑f) (⇑f)) • star (⇑f : V))=_
    rw [unit_ip h,one_smul]
    rfl
  apply Contract.of_involution
  · simp [projection_hermitian]
  · change (P+P-1)*(P+P-1)=1
    noncomm_ring [pp]

#print axioms contract_contrast
#print axioms projective_contrast
end FractionalBell

