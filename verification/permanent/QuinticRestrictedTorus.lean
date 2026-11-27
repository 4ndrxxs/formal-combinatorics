import QuinticGramBasics
import QuinticRestricted

/-! Transport a rank bound for the Hessian on a subspace to the same
coordinate plane used for the ambient Hessian and gradient conditions. -/

noncomputable section
open Matrix Module MvPolynomial
namespace QuinticPencil
variable {K I : Type*} [Field K] [DecidableEq I] [Fintype I] [Infinite K]

theorem restricted_rank_at_support {p : MvPolynomial I K}
    (L : Submodule K (I → K)) (w : I → ℕ) (S : Finset I)
    (paths : PermanentDegeneration.HasCoordinatePaths L w S)
    (sym : ∀ t : K, t ≠ 0 → ∃ a : K, twist (fun i ↦ t^(w i)) p = C a * p)
    (r : ℕ) (small : ∀ y : I → K, finrank K ((hessian p y).toBilin'.restrict L).range ≤ r)
    (y : I → K) : ((hessian p y).submatrix ((↑) : S → I) ((↑) : S → I)).rank ≤ r := by
  classical
  have supported (i : S) (j : I) (hj : j ∉ S) : (Pi.single i.val 1 : I → K) j = 0 := by
    have ne : j ≠ i.val := fun h ↦ hj (h ▸ i.property)
    simp [ne]
  choose q origin away using fun i : S ↦ paths (Pi.single i.val 1) (supported i)
  let H := hessian p y
  let A : Matrix S S (Polynomial K) := Matrix.of fun i j ↦
    (Polynomial.C.mapMatrix H).toBilin' (q i) (q j)
  have evalA (t : K) (i j : S) : ((Polynomial.evalRingHom t).mapMatrix A) i j =
      H.toBilin' (fun x ↦ (q i x).eval t) (fun x ↦ (q j x).eval t) := by
    change (Polynomial.evalRingHom t) ((Polynomial.C.mapMatrix H).toBilin' (q i) (q j)) = _
    simp [Matrix.toBilin'_apply]
  have zero : (Polynomial.evalRingHom 0).mapMatrix A =
      H.submatrix ((↑) : S → I) ((↑) : S → I) := by
    ext i j
    rw [evalA]
    simp only [origin]
    exact H.toBilin'_single i.val j.val
  rw [← zero]
  apply rank_at_zero A r
  intro t nt
  choose x hx values using fun i : S ↦ away i t nt
  let u : S → L := fun i ↦ ⟨x i,hx i⟩
  let v : I → K := fun i ↦ t^(w i)
  let centre : I → K := fun i ↦ y i / v i
  have scaled : (fun i ↦ v i*centre i) = y := by
    funext i
    dsimp [centre,v]
    field_simp
  obtain ⟨a,law⟩ := sym t nt
  let B := (hessian p centre).toBilin'.restrict L
  let G : Matrix S S K := Matrix.of fun i j ↦ B (u i) (u j)
  have eq : (Polynomial.evalRingHom t).mapMatrix A = a • G := by
    ext i j
    rw [evalA]
    simp only [values]
    change (hessian p y).toBilin' (fun l ↦ v l * x i l) (fun l ↦ v l * x j l) =
      a * (hessian p centre).toBilin' (x i) (x j)
    have scale := scaled_hessian_bilin law centre (x i) (x j)
    change (hessian p (fun l ↦ v l*centre l)).toBilin' _ _ = _ at scale
    rwa [scaled] at scale
  rw [eq,Matrix.smul_eq_diagonal_mul]
  exact (Matrix.rank_mul_le_right _ G).trans ((gram_rank_le B u).trans (small centre))

#print axioms restricted_rank_at_support
end QuinticPencil
