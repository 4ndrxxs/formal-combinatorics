import Quantum.Hadamard.ConferenceShiftedLog

/-! Every balanced completion has determinant at least four fifths of
the Ehlich–Wojtas bound from order 110. The intermediate dimensions use
rational certificates that are uniform over the matrix and its signs. -/

noncomputable section
open Finset Matrix
open scoped BigOperators
open Hadamard.DeterminantRatio.Shifted

namespace Hadamard.DeterminantRatio

private theorem middle_parameters (k : ℕ) (lo : 54≤k) (hi : k≤83) :
    ∃ a b : ℝ, 0≤a ∧ a<1 ∧ 0≤b ∧
      2*(k:ℝ)+1≤((((k:ℝ)+1)*a)^2) ∧ 0 ≤ margin ((k:ℝ)+1) a b := by
  interval_cases k
  · refine ⟨1899/10000,47/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨941/5000,93/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨373/2000,23/250,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1849/10000,23/250,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨917/5000,91/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1819/10000,9/100,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨451/2500,89/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1789/10000,89/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨71/400,11/125,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1761/10000,87/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨437/2500,87/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨347/2000,43/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨861/5000,17/200,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1709/10000,17/200,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1697/10000,21/250,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨337/2000,21/250,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1673/10000,83/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1661/10000,41/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨33/200,41/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1639/10000,81/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨407/2500,81/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1617/10000,2/25,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1607/10000,2/25,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1597/10000,79/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1587/10000,79/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1577/10000,39/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1567/10000,39/500,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1557/10000,77/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨387/2500,77/1000,?_⟩
    norm_num [margin,posSix,subThree,negK]
  · refine ⟨1539/10000,19/250,?_⟩
    norm_num [margin,posSix,subThree,negK]

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

private theorem middle_principal {C : Matrix K K ℝ} (k : ℕ) (card : Fintype.card I=k+1)
    (middle : 54≤k) (upper : k≤83) (hc : C.IsHermitian)
    (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix K K ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1)
    (f : I→K) (hf : Function.Injective f) :
    (4/5:ℝ)*ewBound k ≤
      ((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix f f).det := by
  let v : ℝ := (k:ℝ)+1
  let q : ℝ := 2*(k:ℝ)+1
  let E := (2:ℝ) • C.submatrix f f
  let hE : E.IsHermitian := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  let x (i : I) := hE.eigenvalues i/(2*v)
  have vp : 0<v := by dsimp [v]; positivity
  have qp : 0<q := by dsimp [q]; positivity
  have hk : 0<k := by omega
  have kr : 0<(k:ℝ) := by exact_mod_cast hk
  obtain ⟨a,b,ap,a1,bp,radius,positive⟩ := middle_parameters k middle upper
  have dia : ∀ i : I, E i i=0 := by simp [E,Matrix.smul_apply,Matrix.submatrix_apply,diag]
  have sg (i j : I) (hne : i≠j) : E i j^2=4 := by
    have h := off _ _ (hf.ne hne)
    change (2*C (f i) (f j))^2=4
    nlinarith
  obtain ⟨m0,m2⟩ := gram_moments k card hE dia sg
  have mean : ∑ i, x i=0 := by simp only [x,←sum_div,m0,zero_div]
  have second : ∑ i, x i^2=1-1/v := by
    simp only [x,div_pow,←sum_div,m2,v]
    field_simp; ring
  have root : Real.sqrt q≤v*a := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg vp.le ap)).mp
    rw [Real.sq_sqrt qp.le]
    exact radius
  have lo (i : I) : -a≤x i := by
    have eig := (abs_le.mp (conference_principal_abs qp hc square f hf i)).1
    change -a≤hE.eigenvalues i/(2*v)
    apply (le_div_iff₀ (by positivity : 0<2*v)).mpr
    change -(2*Real.sqrt q)≤hE.eigenvalues i at eig
    nlinarith
  have norm := normalized_shifted k hk card x a b ap a1 bp lo mean second positive
  have hv : 1<v := by dsimp [v]; linarith
  have pa : 0<1-1/(2*v) := sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  have pb : 0<1-1/v := sub_pos.mpr ((div_lt_one vp).mpr hv)
  have wp : 0<ewBound k := by
    unfold ewBound
    exact mul_pos (by linarith) (pow_pos (by linarith) _)
  apply (le_div_iff₀ wp).mp
  rw [gram_ratio_identity k card hE]
  change 4/5 ≤ (∏ i, (1+x i))/(2*(1-1/(2*v))*(1-1/v)^k)
  apply (le_div_iff₀ (by positivity)).mpr
  convert norm using 1
  ring

/-- Uniform four-fifths bound from order 110, with arbitrary signs of each
kind on equal-sized blocks. -/
theorem balanced_conference_four_fifths_109 {C : Matrix (I⊕J) (I⊕J) ℝ} (k : ℕ)
    (ci : Fintype.card I=k+1) (cj : Fintype.card J=k+1) (size : 109≤2*(k:ℝ)+1)
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) :
    (4/5:ℝ)*ewBound k ≤ |(C+diagonal completionSign).det| := by
  by_cases big : 169≤2*(k:ℝ)+1
  · exact balanced_conference_four_fifths_169 k ci cj big hc square diag off
  have low : (54:ℝ)≤k := by linarith
  have high : (k:ℝ)<84 := by linarith
  have lk : 54≤k := by exact_mod_cast low
  have hk : k<84 := by exact_mod_cast high
  have tr : C.trace=0 := by simp [Matrix.trace,Matrix.diag,diag]
  rw [Hadamard.ConferenceAverage.balanced_principal_det C (k+1) (2*(k:ℝ)+1)
    ci cj (by linarith) hc square tr, show 2*(k:ℝ)+1+1=2*((k:ℝ)+1) by ring]
  exact middle_principal k ci lk (by omega) hc square diag off Sum.inl Sum.inl_injective

#print axioms balanced_conference_four_fifths_109

end Hadamard.DeterminantRatio
