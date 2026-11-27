import Quantum.Hadamard.ConferenceCubicThreshold
import Quantum.Hadamard.ConferencePrincipalDet

/-! The four-fifths determinant estimate at every balanced completion for q≥169.
Below that threshold the cubic trace of the positive principal submatrix
gives an explicit integer certificate from order 30 onward. -/

open Finset Matrix
open scoped BigOperators

namespace Hadamard.DeterminantRatio

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

private theorem trace_cube_eq_sum {E : Matrix I I ℝ} (h : E.IsHermitian) :
    (E^3).trace=∑ i, h.eigenvalues i^3 := by
  let u := h.eigenvectorUnitary
  let D := diagonal h.eigenvalues
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) u
  have esp : E=α D := h.spectral_theorem
  calc
    _ = ((α D)^3).trace := congrArg (fun A : Matrix I I ℝ ↦ (A^3).trace) esp
    _ = (α (D^3)).trace := by rw [map_pow]
    _ = (D^3).trace := trace_units_conj (Unitary.toUnits u) _
    _ = _ := by simp [D, diagonal_pow]

theorem four_fifths_principal_cubic {C : Matrix K K ℝ} (k : ℕ) (card : Fintype.card I=k+1)
    (size : 29≤2*(k:ℝ)+1) (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix K K ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) (f : I→K) (hf : Function.Injective f)
    (cert : 169≤2*(k:ℝ)+1 ∨
      let v := (k:ℝ)+1
      0 ≤ 87*v^3+375*v*(4*v-3)+1000*((C.submatrix f f)^3).trace-1110*(2*v-1)*(v-1)) :
    (4/5:ℝ)*ewBound k ≤
      ((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix f f).det := by
  let v : ℝ := (k:ℝ)+1
  let q : ℝ := 2*(k:ℝ)+1
  let t := Real.sqrt q
  let B := C.submatrix f f
  let E := (2:ℝ) • B
  let hE : E.IsHermitian := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  let x (i : I) := hE.eigenvalues i/(2*v)
  have vp : 0<v := by dsimp [v]; positivity
  have v15 : 15≤v := by dsimp [v]; linarith
  have qp : 0<q := by dsimp [q]; positivity
  have tp : 0<t := Real.sqrt_pos.mpr qp
  have ts : t^2=q := Real.sq_sqrt qp.le
  have qv : q=2*v-1 := by dsimp [q,v]; ring
  have vk : 0<(k:ℝ) := by linarith
  have hk : 0<k := by exact_mod_cast vk
  have offE (i j : I) (hne : i≠j) : E i j^2=4 := by
    have h := off _ _ (hf.ne hne)
    change (2*C (f i) (f j))^2=4
    nlinarith
  have diagE (i : I) : E i i=0 := by simp [E,B,Matrix.smul_apply,Matrix.submatrix_apply,diag]
  obtain ⟨m0,m2⟩ := gram_moments k card hE diagE offE
  have mean : ∑ i, x i=0 := by simp only [x, ←sum_div, m0,zero_div]
  have second : ∑ i, x i^2=1-1/v := by
    simp only [x,div_pow,←sum_div,m2,v]
    field_simp; ring
  have bound (i : I) : |x i|≤t/v := by
    rw [show |x i| = |hE.eigenvalues i|/(2*v) by
      change |hE.eigenvalues i/(2*v)| = _
      rw [abs_div, abs_of_pos (by positivity : 0<2*v)]]
    apply (div_le_iff₀ (by positivity : 0<2*v)).mpr
    have h : |hE.eigenvalues i|≤2*t := conference_principal_abs qp hc square f hf i
    have cancel : (t/v)*(2*v)=2*t := by field_simp
    linarith
  have small : t/v ≤ 3/8 := by
    apply (div_le_iff₀ vp).mpr
    apply (sq_le_sq₀ tp.le (by positivity)).mp
    rw [ts,qv]
    nlinarith [sq_nonneg (v-15)]
  have lo (i : I) : -(3:ℝ)/8 ≤ x i := by linarith [(abs_le.mp (bound i)).1]
  have rad (i : I) : x i^2 ≤ q/v^2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (div_nonneg tp.le vp.le)).mpr (bound i)
    simpa only [sq_abs,div_pow,ts] using h
  have cx : (∑ i, x i^3)=(B^3).trace/v^3 := by
    simp only [x,div_pow,←sum_div,←trace_cube_eq_sum hE,E, smul_pow,Matrix.trace_smul,smul_eq_mul]
    field_simp
  have condition : 0 ≤ 29/1000+(4*v-3)/(8*v^2)+(∑ i, x i^3)/3-
      (37/100)*(q/v^2)*(1-1/v) := by
    rcases cert with big | tr
    · have t13 : 13≤t := by
        apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤13) tp.le).mp
        rw [ts]; norm_num; exact big
      have cardR : (Fintype.card I:ℝ)=v := by dsimp [v]; exact_mod_cast card
      rw [qv]
      exact cubic_certificate_at_169 x v t (by dsimp [v]; linarith) cardR t13 (ts.trans qv) mean
        second (fun i ↦ (abs_le.mp (bound i)).1)
    · change 0 ≤ 87*v^3+375*v*(4*v-3)+1000*(B^3).trace-1110*(2*v-1)*(v-1) at tr
      rw [cx,qv]
      have scaled : 0 ≤ (87*v^3+375*v*(4*v-3)+1000*(B^3).trace-1110*(2*v-1)*(v-1))/(3000*v^3) :=
        div_nonneg tr (by positivity)
      convert scaled using 1
      field_simp
      ring
  have norm := normalized_cubic_four_fifths k hk x mean second lo (q/v^2) rad condition
  have pa : 0<1-1/(2*v) := sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  have pb : 0<1-1/v := sub_pos.mpr ((div_lt_one vp).mpr (by linarith))
  have wp : 0<ewBound k := by
    unfold ewBound
    exact mul_pos (by linarith) (pow_pos (by linarith) _)
  apply (le_div_iff₀ wp).mp
  rw [gram_ratio_identity k card hE]
  change 4/5 ≤ (∏ i, (1+x i))/(2*(1-1/(2*v))*(1-1/v)^k)
  apply (le_div_iff₀ (by positivity)).mpr
  convert norm using 1
  ring

/-- Every balanced signing meets the four-fifths bound at q≥169. At smaller
orders q≥29 it suffices to verify one explicit cubic trace inequality. -/
theorem balanced_four_fifths_cubic {C : Matrix (I⊕J) (I⊕J) ℝ} (k : ℕ)
    (ci : Fintype.card I=k+1) (cj : Fintype.card J=k+1) (size : 29≤2*(k:ℝ)+1)
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1)
    (cert : 169≤2*(k:ℝ)+1 ∨
      let v := (k:ℝ)+1
      0 ≤ 87*v^3+375*v*(4*v-3)+1000*((C.submatrix Sum.inl Sum.inl : Matrix I I ℝ)^3).trace-
        1110*(2*v-1)*(v-1)) :
    (4/5:ℝ)*ewBound k ≤ |(C+diagonal completionSign).det| := by
  have tr : C.trace=0 := by simp [Matrix.trace,Matrix.diag,diag]
  rw [Hadamard.ConferenceAverage.balanced_principal_det C (k+1) (2*(k:ℝ)+1)
    ci cj (by linarith) hc square tr, show 2*(k:ℝ)+1+1=2*((k:ℝ)+1) by ring]
  exact four_fifths_principal_cubic k ci size hc square diag off Sum.inl Sum.inl_injective cert

/-- At every order q+1 ≥ 170, all balanced signings work without a trace computation. -/
theorem balanced_conference_four_fifths_169 {C : Matrix (I⊕J) (I⊕J) ℝ} (k : ℕ)
    (ci : Fintype.card I=k+1) (cj : Fintype.card J=k+1) (large : 169≤2*(k:ℝ)+1)
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) :
    (4/5:ℝ)*ewBound k ≤ |(C+diagonal completionSign).det| :=
  balanced_four_fifths_cubic k ci cj (by linarith) hc square diag off (Or.inl large)

#print axioms balanced_four_fifths_cubic
#print axioms balanced_conference_four_fifths_169

end Hadamard.DeterminantRatio
