module
public import Quantum.RealHypercubeFrame

/-! Quaternionic Fourier frames for every real dimension at least four. -/
@[expose] public section
noncomputable section
namespace RealHypercubes

open Complex Matrix Finset MaximalHypercubes
open scoped ComplexConjugate Matrix BigOperators

def qblock (w : ℂ) : M := quaternionMatrix (scale2*w) (scale2*w^2)

theorem qblock_unitary {w : ℂ} (h : conj w*w=1) :
    (qblock w)ᴴ * qblock w=1 ∧ qblock w * (qblock w)ᴴ=1 := by
  have hs : scale2*scale2+scale2*scale2=1 := by linear_combination scale2_sq
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qblock,quaternionMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,scale2_conj,pow_succ] <;> grind

theorem trace_qblock (x y : ℂ) :
    2*Matrix.trace ((qblock x)ᴴ * qblock y) =
      (conj x*y) + (conj x*y)^2 + conj (conj x*y) + conj (conj x*y)^2 := by
  simp [qblock,quaternionMatrix,Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_two,scale2_conj]
  have hs:=scale2_sq
  grind

theorem phase_complement {z : ℂ} (hu : conj z*z=1) {m n : ℕ} (h : z^(m+n)=1) :
    conj (z^m) = z^n := by
  have hh : conj (z^m)*z^m=1 := by rw [map_pow,←mul_pow,hu,one_pow]
  rw [pow_add] at h
  calc conj (z^m) = conj (z^m) * (z^m*z^n) := by rw [h,mul_one]
    _ = z^n := by rw [←mul_assoc,hh,one_mul]

def freq {s : ℕ} : Fin (s+1) → ℕ := Fin.cases 0 (fun i => i.val+3)

def flipFreq (s : ℕ) : Equiv.Perm (Fin (s+1)) :=
  Function.Involutive.toPerm (Fin.cases 0 (fun i : Fin s => i.rev.succ)) (by
    intro i
    refine Fin.cases (by simp) (fun j=> ?_) i
    simp)

def realBasis {s : ℕ} (x : Fin (s+5)) : A (s+1) :=
  (qblock (phase x),fun i => phase x ^ freq i)

theorem realBasis_unitary {s : ℕ} (x : Fin (s+5)) : IsUnitary (realBasis x) := by
  have h:=qblock_unitary (phase_unit x)
  refine ⟨h.1,h.2,fun i => ?_⟩
  change conj (phase x ^ freq i)*phase x^freq i=1
  rw [map_pow,←mul_pow,phase_unit,one_pow]

theorem realBasis_shape {s : ℕ} (x : Fin (s+5)) : Shape (flipFreq s) (realBasis x) := by
  refine ⟨rfl,rfl,fun i => ?_⟩
  refine Fin.cases (by simp [realBasis,flipFreq,freq]) (fun j=> ?_) i
  change conj (phase x^(j.val+3))=phase x^(j.rev.val+3)
  apply phase_complement (phase_unit x)
  convert phase_pow_card x using 2
  simp [Fin.val_rev]
  omega

theorem split_sum (s : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin (s+5), f i.val) =
      f 0+f 1+f 2+(∑ i : Fin s, f (i.val+3))+f (s+3)+f (s+4) := by
  rw [Fin.sum_univ_eq_sum_range,Finset.sum_range_succ,Finset.sum_range_succ,
    show s+3=3+s by omega,Finset.sum_range_add,
    ← Fin.sum_univ_eq_sum_range (fun i => f (3+i))]
  simp [Finset.sum_range_succ,Nat.add_comm]

theorem realBasis_gram {s : ℕ} (x y : Fin (s+5)) :
    Gram (realBasis x) (realBasis y) = if x=y then ((s+5:ℕ):ℂ) else 0 := by
  rw [← fourier_gram x y]
  let z := conj (phase x)*phase y
  have hu : conj z*z=1 := by
    simp [z,map_mul]
    grind [phase_unit x,phase_unit y]
  have hp : z^(s+5)=1 := by
    simp [z,mul_pow,←map_pow,phase_pow_card]
  have h1 : conj z=z^(s+4) := by
    simpa using phase_complement hu (m:=1) (n:=s+4)
      (by simpa [show 1+(s+4)=s+5 by omega] using hp)
  have h2 : conj z^2=z^(s+3) := by
    simpa using phase_complement hu (m:=2) (n:=s+3)
      (by simpa [show 2+(s+3)=s+5 by omega] using hp)
  simp only [Gram,realBasis,trace_qblock,map_pow,←mul_pow]
  change z+z^2+conj z+conj z^2 + (∑ i : Fin (s+1),z^freq i) =
    ∑ i : Fin (s+5),z^i.val
  rw [split_sum s (fun i=> z^i), Fin.sum_univ_succ, h2,h1]
  simp [freq]
  ring

def fourierFrame (s : ℕ) : Frame (s+1) where
  basis := realBasis
  e := flipFreq s
  unitary := realBasis_unitary
  shape := realBasis_shape
  gram := realBasis_gram
  slope := phase
  injective := phase_injective _
  nz x := mul_ne_zero scale2_ne (phase_ne x)
  col x := by simp [realBasis,qblock,quaternionMatrix];ring

def fourA : Fin 4 → ℂ := ![1,I,-2,2*I]
def fourB : Fin 4 → ℂ := ![2,-2*I,1,I]
def fourSlope : Fin 4 → ℂ := ![2,-2,-(1/2),1/2]

def fourQ (i : Fin 4) : A 0 :=
  (quaternionMatrix (normalizer 5*fourA i) (normalizer 5*fourB i),1)

theorem norm_four (i : Fin 4) :
    conj (fourA i)*fourA i+conj (fourB i)*fourB i=5 := by
  fin_cases i <;> norm_num [fourA,fourB,Complex.I_mul_I] <;> ring_nf
  all_goals norm_num [map_ofNat]

theorem gram_four_raw (i j : Fin 4) :
    conj (fourA i)*fourA j+conj (fourB i)*fourB j+
    fourA i*conj (fourA j)+fourB i*conj (fourB j) = if i=j then 10 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [fourA,fourB,Complex.I_mul_I] <;> ring_nf
  all_goals norm_num [map_ofNat]

theorem four_normalizer : 5*normalizer 5*normalizer 5=1 := by
  have h:=normalizer_sq 5
  have hz : conj (normalizer 5)=normalizer 5 := by simp [normalizer]
  rw [hz] at h
  norm_num at h
  linear_combination 5*h

theorem fourQ_unitary (i : Fin 4) : IsUnitary (fourQ i) := by
  have hs:=four_normalizer
  have hn:=norm_four i
  have hz : conj (normalizer 5)=normalizer 5 := by simp [normalizer]
  refine ⟨?_,?_,fun i=>Fin.elim0 i⟩ <;> ext k l <;> fin_cases k <;> fin_cases l <;>
    simp [fourQ,quaternionMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fin.sum_univ_two,hz] <;> grind

theorem fourQ_gram (i j : Fin 4) :
    Gram (fourQ i) (fourQ j) = if i=j then 4 else 0 := by
  have hs:=four_normalizer
  have hg:=gram_four_raw i j
  have hz : conj (normalizer 5)=normalizer 5 := by simp [normalizer]
  simp [Gram,fourQ,quaternionMatrix,Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_two,hz]
  by_cases he : i=j <;> simp [he] at hg ⊢ <;> grind

def quaternionFrame : Frame 0 where
  basis := fourQ
  e := 1
  unitary := fourQ_unitary
  shape i := ⟨rfl,rfl,fun j=>Fin.elim0 j⟩
  gram := fourQ_gram
  slope := fourSlope
  injective := by intro i j;fin_cases i <;> fin_cases j <;> norm_num [fourSlope]
  nz i := by
    apply mul_ne_zero (normalizer_ne (q:=5))
    fin_cases i <;> norm_num [fourA]
  col i := by
    change normalizer 5*fourB i = fourSlope i*(normalizer 5*fourA i)
    fin_cases i <;> norm_num [fourA,fourB,fourSlope] <;> ring

theorem frame_exists (r : ℕ) : Nonempty (Frame r) := by
  cases r with
  | zero => exact ⟨quaternionFrame⟩
  | succ s => exact ⟨fourierFrame s⟩

end RealHypercubes
