module

public import Quantum.Diagonal
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! A Fourier construction with translations or inversion on the second diagonal. -/
@[expose] public section
noncomputable section

namespace QuantumCertificate.AbelianDiagonal
open scoped BigOperators ComplexConjugate

structure Pairing (G : Type) [AddCommGroup G] where
  char : G →+ AddChar G ℂ
  inj : Function.Injective char

def cyclic (n : ℕ) [NeZero n] : Pairing (ZMod n) :=
  ⟨(AddChar.zmodAddEquiv (n := n)).toAddMonoidHom, (AddChar.zmodAddEquiv (n := n)).injective⟩

def productPairing {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (p : Pairing A) (q : Pairing B) : Pairing (A × B) := by
  let left : A × B →+ A := AddMonoidHom.fst _ _
  let right : A × B →+ B := AddMonoidHom.snd _ _
  let pair (a : A × B) : AddChar (A × B) ℂ :=
    (p.char a.1).compAddMonoidHom left + (q.char a.2).compAddMonoidHom right
  have ev (a z : A × B) : pair a z = p.char a.1 z.1 * q.char a.2 z.2 := rfl
  refine ⟨{ toFun := pair, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · ext z
    simp [ev]
  · intro x y
    ext z
    simp [ev]
    ring
  · intro x y h
    change pair x = pair y at h
    apply Prod.ext
    · apply p.inj
      ext a
      simpa only [ev, AddChar.map_zero_eq_one, mul_one] using
        DFunLike.congr_fun h (a, (0 : B))
    · apply q.inj
      ext b
      simpa only [ev, AddChar.map_zero_eq_one, one_mul] using
        DFunLike.congr_fun h ((0 : A), b)

variable {G : Type} [AddCommGroup G]

def defect (f : G → G) (x y : G) : G := f (x+y) - f x - f y

def Spans (f : G → G) : Prop :=
  ∀ z, ∃ a b c d, defect f a b + defect f c d = z

private theorem characters_separate (f : G → G) (span : Spans f)
    (A B : AddChar G ℂ) (h : ∀ x, A x * B (f x) = 1) : A = 0 ∧ B = 0 := by
  have hf (x : G) : B (f x) = (A x)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h x)
  have hd (x y : G) : B (defect f x y) = 1 := by
    rw [defect, AddChar.map_sub_eq_div, AddChar.map_sub_eq_div, hf, hf, hf,
      AddChar.map_add_eq_mul]
    have hx := (A.val_isUnit x).ne_zero
    have hy := (A.val_isUnit y).ne_zero
    field_simp
  have hb : B = 0 := by
    ext x
    obtain ⟨a,b,c,d,e⟩ := span x
    rw [← e, AddChar.map_add_eq_mul, hd, hd]
    simp
  exact ⟨by ext x; simpa [hb] using h x, hb⟩

private def complexCoeff : Coefficients ℂ where
  eval := AddMonoidHom.id _
  faithful := fun _ _ h => h
  mul := (· * ·)
  mul_eval := fun _ _ => rfl
  bar := conj
  bar_eval := fun _ => rfl

variable {n : ℕ} [NeZero n] [Fintype G]

omit [NeZero n] in
private theorem char_orthogonal (p : Pairing G) (axis t : Fin n ≃ G)
    (u : Fin n → ℂ) (hu : ∀ k, conj (u k) * u k = 1) :
    complexCoeff.Orthogonal (fun i k => u k * p.char (axis i) (t k)) := by
  intro i j hij
  have hne : p.char (axis j) - p.char (axis i) ≠ 0 :=
    sub_ne_zero.mpr fun h => hij (axis.injective (p.inj h.symm))
  change (∑ k, conj (u k * p.char (axis i) (t k)) * (u k * p.char (axis j) (t k))) = 0
  calc
    _ = ∑ x : G, (p.char (axis j) - p.char (axis i)) x := by
      apply Fintype.sum_equiv t
      intro k
      rw [map_mul, AddChar.sub_apply', ← AddChar.inv_apply_eq_conj, div_eq_mul_inv]
      calc
        _ = (conj (u k) * u k) * (p.char (axis j) (t k) * (p.char (axis i) (t k))⁻¹) := by ring
        _ = _ := by rw [hu, one_mul]
    _ = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hne

private theorem char_unit (a : AddChar G ℂ) (x : G) : conj (a x) * a x = 1 := by
  rw [← AddChar.inv_apply_eq_conj, inv_mul_cancel₀ (a.val_isUnit x).ne_zero]

/-- The coordinate ordering is independent of the common row and column ordering.
    For even orders a translation pairing the reverse indices needs only a complete mapping. -/
theorem construct (p : Pairing G) (axis coord : Fin n ≃ G) (hcoord : coord 0 = 0)
    (f : G → G) (hf0 : f 0 = 0) (hf : Function.Bijective f)
    (plus : Function.Bijective (fun x => x + f x)) (span : Spans f)
    (reverse : (∃ h : G, ∀ i, axis i.rev = axis i + h) ∨
      ((∀ i, axis i.rev = -axis i) ∧ Function.Bijective (fun x => x - f x))) :
    MaximalDiagonal n := by
  let u (ij : Cell n) (k : Fin n) := p.char (axis ij.1) (coord k) * p.char (axis ij.2) (f (coord k))
  refine complexCoeff.maximal_diagonal u 1 one_ne_zero ?_ ?_ ?_ ?_ ?_ ?_
  · intro ij
    simp [u,hcoord,hf0]
  · intro ij kl he
    have h (x : G) : p.char (axis ij.1) x * p.char (axis ij.2) (f x) =
        p.char (axis kl.1) x * p.char (axis kl.2) (f x) := by
      simpa only [u,Equiv.apply_symm_apply] using congrFun he (coord.symm x)
    have eqn (x : G) : (p.char (axis ij.1) - p.char (axis kl.1)) x *
        (p.char (axis ij.2) - p.char (axis kl.2)) (f x) = 1 := by
      simp only [AddChar.sub_apply']
      rw [div_mul_div_comm, h, div_self]
      exact mul_ne_zero ((p.char _).val_isUnit _).ne_zero ((p.char _).val_isUnit _).ne_zero
    obtain ⟨ha,hb⟩ := characters_separate f span _ _ eqn
    exact Prod.ext (axis.injective (p.inj (sub_eq_zero.mp ha)))
      (axis.injective (p.inj (sub_eq_zero.mp hb)))
  · intro i
    exact char_orthogonal p axis (coord.trans (Equiv.ofBijective f hf))
      (fun k => p.char (axis i) (coord k)) (fun _ => char_unit _ _)
  · intro j
    simpa only [u, mul_comm] using (char_orthogonal p axis coord
      (fun k => p.char (axis j) (f (coord k))) (fun _ => char_unit _ _))
  · simpa only [mainDiag,u,Equiv.trans_apply,Equiv.ofBijective_apply,
      AddChar.map_add_eq_mul,one_mul] using
      char_orthogonal p axis (coord.trans (Equiv.ofBijective _ plus)) (fun _ => 1) (by simp)
  · rcases reverse with ⟨h,hr⟩ | ⟨hr,minus⟩
    · simpa only [antiDiag,u,hr,map_add,AddChar.add_apply,Equiv.trans_apply,
        Equiv.ofBijective_apply,AddChar.map_add_eq_mul,mul_left_comm,mul_comm,mul_assoc] using
        char_orthogonal p axis (coord.trans (Equiv.ofBijective _ plus))
          (fun k => p.char h (f (coord k))) (fun _ => char_unit _ _)
    · simpa only [antiDiag,u,hr,map_neg,AddChar.neg_apply',Equiv.trans_apply,
        Equiv.ofBijective_apply,AddChar.map_sub_eq_div,div_eq_mul_inv,one_mul] using
        char_orthogonal p axis (coord.trans (Equiv.ofBijective _ minus))
          (fun _ => 1) (by simp)

end QuantumCertificate.AbelianDiagonal
