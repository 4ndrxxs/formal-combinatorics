module

public import Quantum.Sudoku

/-! Vary an undetectable phase in one band while holding two opposite blocks
    fixed. A four-state Bargmann invariant recovers the phase. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
namespace Measurements
open Finset Complex
open scoped BigOperators ComplexConjugate

variable {I : Type*} [Fintype I] [DecidableEq I]

def mix (p q j : I) : Slice I :=
  if j=p then (3/5 : ℂ) • point p + (4/5 : ℂ) • point q
  else if j=q then (-4/5 : ℂ) • point p + (3/5 : ℂ) • point q
  else point j

theorem mix_gram {p q : I} (hn : p≠q) (j k : I) :
    inner ℂ (mix p q j) (mix p q k) = if j=k then 1 else 0 := by
  by_cases jp : j=p <;> by_cases jq : j=q <;> by_cases kp : k=p <;> by_cases kq : k=q <;>
    simp_all only [mix,ite_true,ite_false,inner_add_left,inner_add_right,inner_smul_left,
      inner_smul_right,point_inner,map_div₀,map_neg,map_ofNat] <;>
    (try split_ifs) <;> simp_all <;> norm_num

def phaseAt (p : I) (z : Circle) (v : Slice I) : Slice I := WithLp.toLp 2
  (fun x => if x=p then (z:ℂ)*v x else v x)

theorem phase_gram (p : I) (z : Circle) (v w : Slice I) :
    inner ℂ (phaseAt p z v) (phaseAt p z w) = inner ℂ v w := by
  have hz : conj (z:ℂ)*(z:ℂ) = 1 := by rw [RCLike.conj_mul,Circle.norm_coe]; norm_num
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply sum_congr rfl
  intro k _
  by_cases h : k=p
  · change (if k=p then (z:ℂ)*w k else w k)*conj (if k=p then (z:ℂ)*v k else v k) = _
    rw [ite_eq_left h,ite_eq_left h,map_mul]
    change _ = w k * conj (v k)
    linear_combination w k * conj (v k) * hz
  · simp [phaseAt,h]

@[simp] theorem phase_abs (p t : I) (z : Circle) (v : Slice I) :
    ‖phaseAt p z v t‖ = ‖v t‖ := by
  by_cases ht : t=p <;> simp [phaseAt,ht]

variable [AddCommGroup I]

/-- The first band uses the point basis, the last chosen band uses a fixed
    real rotation, and the moving band uses that rotation with one phase. -/
def band (m f p q : I) (z : Circle) (i j : I) : Slice I :=
  if i=m then phaseAt p z (mix p q j) else if i=f then mix p q j else point j

def family (m f p q : I) (z : Circle) : Grid I := fromBands (band m f p q z)

theorem family_valid (m f : I) {p q : I} (hpq : p≠q) (z : Circle) :
    Valid (family m f p q z) := by
  apply fromBands_valid
  intro i a b
  unfold band
  split_ifs <;> simp only [phase_gram,mix_gram hpq,point_inner] <;> simp_all

theorem fixed_band {m : I} (f p q : I) (z w : Circle) {i : I} (hi : i≠m)
    (a : I) (c : Index I) : family m f p q z (i,a) c = family m f p q w (i,a) c := by
  simp [family,fromBands,band,hi]

theorem first_measurement {m f : I} (hm : (0:I)≠m) (hf : (0:I)≠f)
    (p q : I) (z w : Circle) (x y : I) (r c : Index I) :
    probability (family m f p q z (0,x) (0,y)) (family m f p q z r c) =
      probability (family m f p q w (0,x) (0,y)) (family m f p q w r c) := by
  simp only [probability,family,fromBands,zero_add,add_zero,band,ite_eq_right hm,ite_eq_right hf,slot_inner]
  split_ifs <;> simp_all [point,EuclideanSpace.inner_single_left,phase_abs]

def sample (i a : I) : Index I × Index I := ((i,a),(0,-i))

@[simp] theorem sample_value (m f p q : I) (z : Circle) (i a : I) :
    family m f p q z (sample i a).1 (sample i a).2 = slot (band m f p q z i a) 0 := by
  simp [sample,family,fromBands]

theorem phase_signal {m f p q : I} (hm : (0:I)≠m) (hf : (0:I)≠f)
    (hfm : f≠m) (hpq : p≠q) (z : Circle) :
    let v := family m f p q z
    let e := fun s : Index I × Index I => v s.1 s.2
    fourOverlap (e (sample 0 p)) (e (sample m p)) (e (sample 0 q)) (e (sample f p)) =
      (144/625 : ℂ)*(z:ℂ) := by
  dsimp only
  simp only [sample_value,fourOverlap,slot_inner,ite_true,band,ite_eq_right hm,ite_eq_right hf,
    ite_eq_right hfm,ite_true,mix,phaseAt,point,EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right]
  simp [hpq,Ne.symm hpq,map_ofNat]
  ring

theorem equivalent_only_same {m f p q : I} (hm : (0:I)≠m) (hf : (0:I)≠f)
    (hfm : f≠m) (hpq : p≠q) {z w : Circle}
    (h : Equivalent (family m f p q z) (family m f p q w)) : z=w := by
  have e := equivalent_four h (sample 0 p) (sample m p) (sample 0 q) (sample f p)
  rw [phase_signal hm hf hfm hpq z,phase_signal hm hf hfm hpq w] at e
  exact Circle.ext (mul_left_cancel₀ (by norm_num : (144/625 : ℂ)≠0) e)

theorem conjugate_cell (m f p q : I) (z : Circle) (r c t : Index I) :
    family m f p q z⁻¹ r c t = conj (family m f p q z r c t) := by
  have hz : (z:ℂ)⁻¹ = conj (z:ℂ) := Circle.coe_inv_eq_conj z
  unfold family fromBands slot band phaseAt mix
  split_ifs <;> simp_all [point,PiLp.single_apply] <;>
    split_ifs <;> simp_all [hz,map_ofNat,map_div₀]

omit [DecidableEq I] [AddCommGroup I] in
theorem conjugate_inner {v w v' w' : H I} (hv : ∀ t, v' t=conj (v t))
    (hw : ∀ t, w' t=conj (w t)) : inner ℂ v' w'=conj (inner ℂ v w) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,map_sum]
  apply sum_congr rfl
  intro t _
  change w' t*conj (v' t) = conj (w t*conj (v t))
  simp [hv,hw]

theorem same_full_overlaps (m f p q : I) (z : Circle) (r c s t : Index I) :
    probability (family m f p q z⁻¹ r c) (family m f p q z⁻¹ s t) =
    probability (family m f p q z r c) (family m f p q z s t) := by
  rw [probability,probability,conjugate_inner (conjugate_cell m f p q z r c)
      (conjugate_cell m f p q z s t)]
  rw [Complex.norm_conj]

/-- All sizes N at least three admit an entire circle of mutually inequivalent
    grids sharing both opposite blocks and all first-block measurement probabilities.
    Inverse phases also have identical pairwise transition probabilities everywhere. -/
theorem larger_sudoku (n : ℕ) (hn : 3≤n) :
    ∃ F : Circle → Grid (Fin n), ∀ z w : Circle,
      Valid (F z) ∧
      (∀ a b, F z (⟨0,by omega⟩,a) (⟨0,by omega⟩,b) =
        F w (⟨0,by omega⟩,a) (⟨0,by omega⟩,b)) ∧
      (∀ a b, F z (⟨n-1,by omega⟩,a) (⟨n-1,by omega⟩,b) =
        F w (⟨n-1,by omega⟩,a) (⟨n-1,by omega⟩,b)) ∧
      (∀ a b r c, probability (F z (⟨0,by omega⟩,a) (⟨0,by omega⟩,b)) (F z r c) =
        probability (F w (⟨0,by omega⟩,a) (⟨0,by omega⟩,b)) (F w r c)) ∧
      (Equivalent (F z) (F w) → z=w) ∧
      ∀ r c s t, probability (F z⁻¹ r c) (F z⁻¹ s t) = probability (F z r c) (F z s t) := by
  let : NeZero n := ⟨by omega⟩
  let m : Fin n := ⟨1,by omega⟩
  let f : Fin n := ⟨n-1,by omega⟩
  have hm : (0 : Fin n) ≠ m := fun h => by have := congrArg Fin.val h; simp [m] at this
  have hf : (0 : Fin n) ≠ f := fun h => by have := congrArg Fin.val h; simp [f] at this; omega
  have hfm : f ≠ m := fun h => by have := congrArg Fin.val h; dsimp [f,m] at this; omega
  refine ⟨family m f 0 m,fun z w => ⟨family_valid m f hm z,?_,?_,?_,
    equivalent_only_same hm hf hfm hm,same_full_overlaps m f 0 m z⟩⟩
  · exact fun a b => fixed_band f 0 m z w hm a (0,b)
  · exact fun a b => fixed_band f 0 m z w hfm a (f,b)
  · exact first_measurement hm hf 0 m z w

#print axioms larger_sudoku

end Measurements
end QuantumSudoku
