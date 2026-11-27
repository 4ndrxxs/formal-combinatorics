module

public import Quantum.PartialCertificates

/-! Maximal quantum Latin squares with two prescribed orthonormal diagonals. -/
@[expose] public section
namespace QuantumCertificate

def IsBasisLine {n : ℕ} (v : Cell n → Space n) (l : Fin n → Cell n) : Prop :=
  ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = fun i => v (l i)

structure MaximalSquare (n : ℕ) where
  entry : Cell n → Space n
  nz : ∀ p, entry p ≠ 0
  rows : ∀ i, IsBasisLine entry (fun j => (i,j))
  cols : ∀ j, IsBasisLine entry (fun i => (i,j))
  distinct : Function.Injective (fun p => Projectivization.mk ℂ (entry p) (nz p))

theorem MaximalSquare.realized {n : ℕ} (a : MaximalSquare n) : Realized n (n*n) := by
  refine ⟨fun i j => a.entry (i,j),fun i j => a.nz (i,j),a.rows,a.cols,?_⟩
  rw [Set.ncard_range_of_injective a.distinct]
  simp

def mainDiag (n : ℕ) (i : Fin n) : Cell n := (i,i)
def antiDiag (n : ℕ) (i : Fin n) : Cell n := (i,i.rev)

def MaximalDiagonal (n : ℕ) : Prop :=
  ∃ a : MaximalSquare n, IsBasisLine a.entry (mainDiag n) ∧ IsBasisLine a.entry (antiDiag n)

def MaximalIdempotent (n : ℕ) : Prop :=
  ∃ a : MaximalSquare n, ∀ i, a.entry (i,i) = EuclideanSpace.single i 1

theorem MaximalDiagonal.idempotent {n : ℕ} (h : MaximalDiagonal n) : MaximalIdempotent n := by
  obtain ⟨a,⟨d,hd⟩,_⟩ := h
  let f := d.repr
  let v (p : Cell n) := f (a.entry p)
  have nz (p : Cell n) : v p ≠ 0 :=
    fun h => a.nz p (f.injective (h.trans (map_zero f).symm))
  have trans {l : Fin n → Cell n} (hl : IsBasisLine a.entry l) : IsBasisLine v l := by
    obtain ⟨b,hb⟩ := hl
    exact ⟨b.map f,funext fun i => by simpa [v] using congrArg f (congrFun hb i)⟩
  refine ⟨⟨v,nz,fun i => trans (a.rows i),fun j => trans (a.cols j),?_⟩,?_⟩
  · exact (Projectivization.map_injective f.toLinearEquiv.toLinearMap f.injective).comp a.distinct
  · intro i
    change f (a.entry (i,i)) = _
    have e : d i = a.entry (i,i) := congrFun hd i
    exact (congrArg f e).symm.trans (d.repr_self i)

namespace Coefficients

variable {T : Type} [AddCommMonoid T] {n : ℕ} [NeZero n] (a : Coefficients T)

/-- One common nonzero chart coordinate reduces projective injectivity to
    injectivity of exact coefficient words before normalization. -/
theorem maximal_diagonal (u : Cell n → Fin n → T) (M : T) (hM : M ≠ 0)
    (common : ∀ p, u p 0 = M) (inj : Function.Injective u)
    (rows : ∀ i, a.Orthogonal (fun j => u (i,j)))
    (cols : ∀ j, a.Orthogonal (fun i => u (i,j)))
    (main : a.Orthogonal (fun i => u (mainDiag n i)))
    (anti : a.Orthogonal (fun i => u (antiDiag n i))) : MaximalDiagonal n := by
  let w (p : Cell n) := a.raw (u p)
  have nz (p : Cell n) : w p ≠ 0 := by
    intro hh
    have ee := congrArg (fun v : Space n => v 0) hh
    change a.eval (u p 0) = 0 at ee
    rw [common p] at ee
    exact hM (a.faithful (ee.trans (map_zero a.eval).symm))
  let v (p : Cell n) := (‖w p‖ : ℂ)⁻¹ • w p
  have unit (p : Cell n) : ‖v p‖ = 1 := by
    simp [v,norm_smul,Complex.norm_real,norm_ne_zero_iff.mpr (nz p)]
  have vn (p : Cell n) : v p ≠ 0 := by intro he; simpa [he] using unit p
  have basis {l : Fin n → Cell n} (hh : a.Orthogonal (fun i => u (l i))) :
      IsBasisLine v l := by
    have on : Orthonormal ℂ (fun i => v (l i)) := by
      refine ⟨fun i => unit _,fun i j h => ?_⟩
      simp [v,w,inner_smul_left,inner_smul_right,a.raw_inner,hh i j h]
    exact ⟨OrthonormalBasis.mk on
      (on.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge,
      OrthonormalBasis.coe_mk _ _⟩
  refine ⟨⟨v,vn,fun i => basis (rows i),fun j => basis (cols j),?_⟩,basis main,basis anti⟩
  have same (p : Cell n) : Projectivization.mk ℂ (v p) (vn p) =
      Projectivization.mk ℂ (w p) (nz p) :=
    (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨_,rfl⟩
  intro i j hij
  obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    ((same i).symm.trans (hij.trans (same j)))
  have he x : s * a.eval (u j x) = a.eval (u i x) := congrArg (fun v : Space n => v x) hs
  have hn : a.eval M ≠ 0 := fun he => hM (a.faithful (he.trans (map_zero a.eval).symm))
  have h1 := he 0
  rw [common,common] at h1
  have eq : s = 1 := mul_right_cancel₀ hn (h1.trans (one_mul _).symm)
  apply inj
  funext x
  exact a.faithful (by simpa [eq] using (he x).symm)

end Coefficients
end QuantumCertificate
