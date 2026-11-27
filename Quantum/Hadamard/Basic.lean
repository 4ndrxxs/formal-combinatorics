import Mathlib

/-! Sign matrices with orthogonal distinct rows. At modulus zero, ZMod 0 is
the integers. The public formulation in terms of integer matrices uses
ordinary divisibility for each entry of the Gram matrix. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m n : ℕ} {I J : Type*} [Fintype I] [Fintype J]

abbrev RowMatrix (m : ℕ) (I : Type*) := I → I → ZMod m
def Sign {R : Type*} [Ring R] (x : R) : Prop := x=1 ∨ x= -1

structure Good (H : RowMatrix m I) : Prop where
  sign : ∀ i j, Sign (H i j)
  ortho : ∀ i k, i ≠ k → ∑ j, H i j * H k j = 0

def AtOrder (m n : ℕ) : Prop := ∃ H : RowMatrix m (Fin n), Good H

theorem sign_sq {R : Type*} [Ring R] {x : R} (h : Sign x) : x*x=1 := by
  rcases h with h|h <;> simp [h]

theorem sign_mul {R : Type*} [Ring R] {x y : R} (h : Sign x) (g : Sign y) : Sign (x*y) := by
  rcases h with h|h <;> rcases g with g|g <;> simp [h,g,Sign]

theorem Good.transport {H : RowMatrix m I} (h : Good H) (e : J ≃ I) :
    Good (fun i j => H (e i) (e j)) := by
  refine ⟨fun i j => h.sign _ _,fun i k ne => ?_⟩
  exact (e.sum_comp (fun j => H (e i) j * H (e k) j)).trans
    (h.ortho _ _ (fun he => ne (e.injective he)))

theorem Good.norm_rows {H : RowMatrix m I} (h : Good H) :
    ∀ i, ∑ j, H i j * H i j = (Fintype.card I : ZMod m) := by
  intro i
  simp [fun j => sign_sq (h.sign i j)]

def normalize (H : RowMatrix m I) (a i j : I) : ZMod m := (H i a*H a a)*(H a j*H i j)

theorem Good.normalize {H : RowMatrix m I} (h : Good H) (a : I) : Good (normalize H a) := by
  refine ⟨fun i j => sign_mul (sign_mul (h.sign _ _) (h.sign _ _))
    (sign_mul (h.sign _ _) (h.sign _ _)),fun i k ne => ?_⟩
  calc
    _ = ∑ j, ((H i a*H a a)*(H k a*H a a))*(H i j*H k j) := by
      apply sum_congr rfl
      intro j _
      unfold HadamardMod.normalize
      calc
        _ = ((H i a*H a a)*(H k a*H a a))*(H i j*H k j)*(H a j*H a j) := by ring
        _ = _ := by rw [sign_sq (h.sign a j),mul_one]
    _ = 0 := by rw [←mul_sum,h.ortho _ _ ne,mul_zero]

theorem normalized_first {H : RowMatrix m I} (h : Good H) (a i : I) :
    normalize H a a i=1 ∧ normalize H a i a=1 := by
  dsimp [normalize]
  constructor
  · rw [sign_sq (h.sign _ _),sign_sq (h.sign _ _),one_mul]
  · calc
      _ = (H i a*H i a)*(H a a*H a a) := by ring
      _ = 1 := by rw [sign_sq (h.sign _ _),sign_sq (h.sign _ _),one_mul]

theorem product {A : RowMatrix m I} {B : RowMatrix m J} (h : Good A) (g : Good B) :
    Good (fun i j : I×J => A i.1 j.1*B i.2 j.2) := by
  refine ⟨fun i j => sign_mul (h.sign _ _) (g.sign _ _),?_⟩
  rintro ⟨i,a⟩ ⟨k,b⟩ ne
  rw [Fintype.sum_prod_type]
  dsimp
  have factor : ∀ j t, A i j*B a t*(A k j*B b t)=(A i j*A k j)*(B a t*B b t) := by
    intro j t; ring
  simp only [factor,←mul_sum,←sum_mul]
  by_cases same : i=k
  · have nd : a≠b := fun hf => ne (Prod.ext same hf)
    rw [g.ortho _ _ nd,mul_zero]
  · rw [h.ortho _ _ same,zero_mul]

theorem at_mul {a b : ℕ} (x : AtOrder m a) (y : AtOrder m b) : AtOrder m (a*b) := by
  obtain ⟨A,h⟩:=x
  obtain ⟨B,g⟩:=y
  exact ⟨_,(product h g).transport finProdFinEquiv.symm⟩

theorem of_card {I : Type*} [Fintype I] {A : RowMatrix m I} (h : Good A) (e : Fintype.card I=n) :
    AtOrder m n := ⟨_,h.transport (Fintype.equivFinOfCardEq e).symm⟩

theorem empty_order (m : ℕ) : AtOrder m 0 :=
  ⟨fun i => i.elim0,⟨fun i => i.elim0,fun i => i.elim0⟩⟩

theorem ones {n m : ℕ} (h : (n : ZMod m)=0) : AtOrder m n := by
  refine ⟨fun _ _ => 1,⟨fun _ _ => Or.inl rfl,?_⟩⟩
  intro i k _
  simpa using h

theorem offdiag_four {n m : ℕ} (h : (n : ZMod m)=4) : AtOrder m n := by
  let A : RowMatrix m (Fin n) := fun i j => if j=i then -1 else 1
  refine ⟨A,⟨fun i j => by by_cases e : j=i <;> simp [A,e,Sign],?_⟩⟩
  intro i k ne
  have expand (j : Fin n) : A i j*A k j=(1:ZMod m)-(if j=i then 2 else 0)-(if j=k then 2 else 0) := by
    by_cases a : j=i <;> by_cases b : j=k
    · exact (ne (a.symm.trans b)).elim
    all_goals simp [A,a,b,ne,ne.symm] <;> ring
  simp only [expand,Finset.sum_sub_distrib]
  simp [h]
  ring

theorem order_two (m : ℕ) : AtOrder m 2 := by
  let A : RowMatrix m (Fin 2) := fun i j => if i=1 ∧ j=1 then -1 else 1
  refine ⟨A,⟨fun i j => by by_cases e : i=1 ∧ j=1 <;> simp [A,e,Sign],?_⟩⟩
  intro i j ne
  fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two,A]

def IntegralSolution (m n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ, (∀ i j, Sign (H i j)) ∧
    ∀ i k, (m:ℤ) ∣ (H*H.transpose) i k-(if i=k then (n:ℤ) else 0)

theorem integer_gram {m n : ℕ} (h : AtOrder m n) : IntegralSolution m n := by
  classical
  obtain ⟨A,g⟩:=h
  let H : Matrix (Fin n) (Fin n) ℤ := fun i j => if A i j=1 then 1 else -1
  have cast (i j) : ((H i j : ℤ) : ZMod m)=A i j := by
    rcases g.sign i j with h|h
    · simp [H,h]
    · by_cases e : A i j=1
      · simp [H,e]
      · simpa [H,e] using h.symm
  refine ⟨H,fun i j => by by_cases h : A i j=1 <;> simp [H,h,Sign],?_⟩
  intro i k
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
  rw [Matrix.mul_apply]
  push_cast
  simp only [Matrix.transpose_apply,cast]
  by_cases e : i=k
  · subst k
    simpa using sub_eq_zero.mpr (g.norm_rows i)
  · simp [e,g.ortho i k e]

#print axioms integer_gram
end HadamardMod
