module

public import Quantum.SudokuLayers
public import Quantum.PartialCertificates

/-! A finite certificate for a full quantum Sudoku, using exact coefficients
    and a chart for projective rays. All three sorts of lines are checked. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
open QuantumCertificate Finset
open scoped BigOperators

def flatPos {n : ℕ} (p : Index (Fin n)) : Fin (n*n) := finProdFinEquiv p

theorem of_certificate {n c : ℕ} [NeZero n] {T : Type} [AddCommMonoid T] (a : Coefficients T)
    (r : Fin c → Fin (n*n) → T) (label : Index (Fin n) → Index (Fin n) → Fin c)
    (p : Fin c → Fin (n*n)) (M : T) (hM : M ≠ 0) (chart : Coefficients.Chart r p M)
    (distinct : Function.Injective r)
    (cover : ∀ k, ∃ i j, label i j=k)
    (rows : ∀ i j k, j≠k → a.dot (r (label i j)) (r (label i k))=0)
    (cols : ∀ j i k, i≠k → a.dot (r (label i j)) (r (label k j))=0)
    (blocks : ∀ i j (x y : Index (Fin n)), x≠y →
      a.dot (r (label (i,x.1) (j,x.2))) (r (label (i,y.1) (j,y.2)))=0) : Realizes n c := by
  classical
  let u := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (finProdFinEquiv.symm : Fin (n*n) ≃ Index (Fin n))
  have nz (k : Fin c) : a.raw (r k) ≠ 0 := by
    intro h
    have eq := congrArg (fun v : Space (n*n) => v (p k)) h
    change a.eval (r k (p k))=0 at eq
    rw [(chart k).1] at eq
    exact hM (a.faithful (eq.trans (map_zero a.eval).symm))
  let vec (k : Fin c) : H (Fin n) := u ((‖a.raw (r k)‖ : ℂ)⁻¹ • a.raw (r k))
  have unit (k : Fin c) : ‖vec k‖=1 := by
    simp [vec,norm_smul,Complex.norm_real,norm_ne_zero_iff.mpr (nz k)]
  have wn (k : Fin c) : vec k≠0 := fun h => by simpa [h] using unit k
  have basis (f : Index (Fin n) → Fin c)
      (h : ∀ i j, i≠j → a.dot (r (f i)) (r (f j))=0) : BasisLine (fun x => vec (f x)) := by
    apply basis_of_gram
    intro i j
    by_cases e : i=j
    · subst j
      simpa using inner_self_eq_one_of_norm_eq_one (𝕜:=ℂ) (unit (f i))
    · simp [vec,u.inner_map_map,inner_smul_left,inner_smul_right,a.raw_inner,h i j e,e]
  let v : Grid (Fin n) := fun i j => vec (label i j)
  have good : Valid v := ⟨fun i => basis _ (rows i),fun j => basis _ (cols j),
    fun i j => basis _ (blocks i j)⟩
  let ray (k : Fin c) := Projectivization.mk ℂ (vec k) (wn k)
  have hi : Function.Injective ray := by
    intro i j he
    obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
    change s • u _ = u _ at hs
    rw [← u.map_smul] at hs
    have huv := u.injective hs
    have ht := congrArg (fun w : Space (n*n) => (‖a.raw (r i)‖ : ℂ) • w) huv
    simp only [smul_smul] at ht
    rw [mul_inv_cancel₀ (by simp [nz i]),one_smul] at ht
    exact a.chart_injective chart hM distinct i j _ ht
  refine ⟨v,good,?_⟩
  have eq : gridRays good=Set.range ray := by
    ext q
    constructor
    · rintro ⟨⟨i,j⟩,rfl⟩
      exact ⟨label i j,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨i,j,rfl⟩ := cover k
      exact ⟨(i,j),rfl⟩
  rw [eq,Set.ncard_range_of_injective hi]
  simp

#print axioms of_certificate
end QuantumSudoku
