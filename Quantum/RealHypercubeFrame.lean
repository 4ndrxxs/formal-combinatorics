module

public import Quantum.MaximalHypercubes
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Multiplication in a real form of a complex matrix and scalar algebra
preserves orthogonality. Diagonal unit quaternions separate first columns. -/

@[expose] public section
noncomputable section
namespace RealHypercubes

open Complex Matrix Finset MaximalHypercubes
open scoped ComplexConjugate Matrix

def quaternionMatrix (s t : ℂ) : M := !![s, -conj t; t, conj s]

def Shape {r : ℕ} (e : Equiv.Perm (Fin r)) (a : A r) : Prop :=
  a.1 0 1 = -conj (a.1 1 0) ∧ a.1 1 1 = conj (a.1 0 0) ∧ ∀ i, conj (a.2 i) = a.2 (e i)

theorem shape_one {r : ℕ} (e : Equiv.Perm (Fin r)) : Shape e (1 : A r) := by
  simp [Shape]

theorem shape_mul {r : ℕ} {e : Equiv.Perm (Fin r)} {a b : A r}
    (ha : Shape e a) (hb : Shape e b) : Shape e (a*b) := by
  rcases ha with ⟨ha0,ha1,ha2⟩
  rcases hb with ⟨hb0,hb1,hb2⟩
  simp [Shape, Matrix.mul_apply, Fin.sum_univ_two,ha0,ha1,ha2,hb0,hb1,hb2]
  ring

theorem gram_real {r : ℕ} {e : Equiv.Perm (Fin r)} {a b : A r}
    (ha : Shape e a) (hb : Shape e b) : conj (Gram a b) = Gram a b := by
  rcases ha with ⟨ha0,ha1,ha2⟩
  rcases hb with ⟨hb0,hb1,hb2⟩
  have H : (∑ i, conj (conj (a.2 i) * b.2 i)) = ∑ i, conj (a.2 i) * b.2 i := by
    rw [← Equiv.sum_comp e (fun i => conj (a.2 i)*b.2 i)]
    simp only [map_mul,ha2,hb2]
  simp only [map_mul] at H
  simp only [Gram,map_add,map_mul,map_ofNat,map_sum,H]
  congr 1
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,ha0,ha1,hb0,hb1]
  ring

def inter {r : ℕ} (u : ℂ) : A r := (!![conj u,0;0,u],1)

theorem inter_shape {r : ℕ} (e : Equiv.Perm (Fin r)) (u : ℂ) : Shape e (inter u) := by
  simp [Shape,inter]

theorem inter_unitary {r : ℕ} {u : ℂ} (hu : conj u*u=1) : IsUnitary (inter (r:=r) u) := by
  refine ⟨?_,?_,by simp [inter]⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [inter,Matrix.mul_apply,Matrix.conjTranspose_apply, Fin.sum_univ_two,hu,mul_comm u]

structure Frame (r : ℕ) where
  basis : Fin (r+4) → A r
  e : Equiv.Perm (Fin r)
  unitary : ∀ x, IsUnitary (basis x)
  shape : ∀ x, Shape e (basis x)
  gram : ∀ x y, Gram (basis x) (basis y) = if x=y then ((r+4:ℕ):ℂ) else 0
  slope : Fin (r+4) → ℂ
  injective : Function.Injective slope
  nz : ∀ x, (basis x).1 0 0 ≠ 0
  col : ∀ x, (basis x).1 1 0 = slope x * (basis x).1 0 0

theorem sqrt_phase {z : ℂ} (hz : conj z*z=1) :
    ∃ u : ℂ, u^2=z ∧ conj u*u=1 ∧ conj u*z=u := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq z zero_lt_two
  have hnormz : ‖z‖^2=1 := by
    rw [Complex.conj_mul'] at hz
    exact_mod_cast hz
  have hn : ‖u‖^2=‖z‖ := by simpa using congrArg norm hu
  have hnormz' : ‖z‖=1 := by nlinarith [norm_nonneg z]
  have hnorm : ‖u‖=1 := by nlinarith [norm_nonneg u]
  have hunit : conj u*u=1 := by simp [Complex.conj_mul',hnorm]
  obtain rfl := hu
  exact ⟨u,rfl,hunit,by linear_combination u*hunit⟩

theorem frame_extend {r : ℕ} (F : Frame r) {ι : Type*} [Fintype ι] (p : ι → A r)
    (hu : ∀ a, IsUnitary (p a))
    (hs : Pairwise (fun a b => firstDet (p a).1 (p b).1 ≠ 0)) :
    ∃ c : A r, IsUnitary c ∧ Shape F.e c ∧ Pairwise (fun a b : ι × Fin (r+4) =>
      firstDet (p a.1 * c * F.basis a.2).1 (p b.1 * c * F.basis b.2).1 ≠ 0) := by
  classical
  let J := ι × Fin (r+4)
  let I := { s : J × J // s.1 ≠ s.2 }
  let P : I → Polynomial ℂ := fun s => collisionPolynomial (p s.val.1.1).1 (p s.val.2.1).1
    (F.slope s.val.1.2) (F.slope s.val.2.2)
  have hP (s : I) : P s ≠ 0 := by
    rcases s with ⟨⟨⟨a,x⟩, ⟨b,y⟩⟩, h⟩
    change collisionPolynomial (p a).1 (p b).1 (F.slope x) (F.slope y) ≠ 0
    intro he
    by_cases hab : a = b
    · subst b
      have hxy : y ≠ x := fun e => h (by simp [e])
      have hh := congrArg (Polynomial.eval 1) he
      rw [collisionPolynomial_self, Polynomial.eval_zero] at hh
      exact mul_ne_zero (sub_ne_zero.mpr (fun e => hxy (F.injective e))) (det_ne (hu a)) hh
    · apply hs hab
      simpa only [collisionPolynomial_zero, Polynomial.eval_zero] using
        congrArg (Polynomial.eval 0) he
  obtain ⟨z,hz,hgood⟩ := avoid_polynomials P hP
  obtain ⟨u,_,hu,huz⟩ := sqrt_phase hz
  refine ⟨inter u,inter_unitary hu,inter_shape _ _,?_⟩
  intro a b h
  have eval : firstDet (p a.1 * inter u * F.basis a.2).1 (p b.1 * inter u * F.basis b.2).1 =
    (conj u)^2 * (F.basis a.2).1 0 0 * (F.basis b.2).1 0 0 * (P (⟨(a,b),h⟩ : I)).eval z := by
    simp only [firstDet,Prod.fst_mul,inter,Matrix.mul_apply,Fin.sum_univ_two]
    simp [P,collisionPolynomial,F.col]
    grind
  rw [eval]
  have hnu : conj u ≠ 0 := by intro h0; simp [h0] at hu
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hnu) (F.nz a.2)) (F.nz b.2))
    (hgood _)

theorem frame_words {r : ℕ} (F : Frame r) (d : ℕ) :
    ∃ p : Grid (r+4) d → A r, Good p ∧ ∀ a, Shape F.e (p a) := by
  induction d with
  | zero =>
    refine ⟨fun _=>1,⟨fun _=>unitary_one _, ?_,fun k=>Fin.elim0 k⟩,fun _=>shape_one _⟩
    exact fun a b h => (h (Subsingleton.elim a b)).elim
  | succ d ih =>
    obtain ⟨p,hp,hshape⟩ := ih
    obtain ⟨c,hc,hcs,hsep⟩ := frame_extend F p hp.unitary hp.separated
    refine ⟨fun a => p (tail a) * c * F.basis (a 0),⟨?_,?_,?_⟩,?_⟩
    · exact fun _ => unitary_mul (unitary_mul (hp.unitary _) hc) (F.unitary _)
    · intro a b hab
      apply hsep (i := (tail a,a 0)) (j := (tail b,b 0))
      intro he
      apply hab
      funext k
      exact Fin.cases (congrArg Prod.snd he) (fun u => congrFun (congrArg Prod.fst he) u) k
    · intro k
      refine Fin.cases ?_ (fun u => ?_) k
      · intro a b ho
        have ht : tail a = tail b := funext fun i => ho _ (Fin.succ_ne_zero i)
        rw [ht, Gram_left _ _ _ (unitary_mul (hp.unitary _) hc), F.gram]
      · intro a b ho
        have h0 : a 0 = b 0 := ho _ (Fin.succ_ne_zero _).symm
        rw [h0, Gram_right _ _ _ (F.unitary _), Gram_right _ _ _ hc]
        exact hp.line u (tail a) (tail b) fun i h => ho i.succ
          (fun he => h (Fin.succ_injective _ he))
    · exact fun _ => shape_mul (shape_mul (hshape _) hcs) (F.shape _)

end RealHypercubes
