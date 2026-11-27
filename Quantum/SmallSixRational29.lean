module
public import Quantum.Pivots

/-! A 29-ray order-six square with integral representatives of height at most 16.
The reflected array is its transpose after applying the same involution to both
indices. The finite arithmetic verifies the bound, symmetry and complete square.
The incidence pattern is drawn from Das and Kumar, arXiv:2608.12607. -/
@[expose] public section
namespace SmallSixRational29

open QuantumCertificate Matrix
open scoped BigOperators Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rays : Fin 29 → Fin 6 → ℤ :=
  ![![1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, 7, -6, -7, -2, 3],
    ![0, 1, 0, -1, -2, -6],
    ![0, 0, 3, 0, -6, 2],
    ![0, 1, 0, 1, 0, 0],
    ![0, 1, 2, -1, 1, 0],
    ![0, 0, 3, -3, 3, 1],
    ![0, 0, 9, 5, -5, 3],
    ![0, 0, 1, 0, 0, -3],
    ![0, 0, 0, 1, 1, 0],
    ![0, 0, 3, -5, -5, -9],
    ![0, 0, 1, 3, 3, -3],
    ![0, 1, 0, -1, 1, 0],
    ![0, 0, 3, 0, 0, 1],
    ![0, 2, 0, 1, -1, 0],
    ![0, 14, 6, 7, 2, -3],
    ![0, 0, 6, -7, 2, -3],
    ![0, 1, 0, -1, -2, 1],
    ![0, 0, 2, 0, 3, 6],
    ![0, 2, -3, -2, 2, 0],
    ![0, 0, 11, 0, -15, 12],
    ![0, 0, 3, 0, 15, 16],
    ![0, 0, 6, 0, 2, -3],
    ![0, 1, 0, -1, 0, 0]]

def labels : Fin 6 → Fin 6 → Fin 29 :=
  ![![0, 1, 2, 3, 4, 5],
    ![6, 0, 7, 8, 9, 10],
    ![11, 12, 0, 1, 13, 14],
    ![15, 16, 17, 0, 18, 19],
    ![20, 21, 22, 23, 0, 24],
    ![25, 26, 9, 27, 28, 0]]

def perm : Fin 6 → Fin 6 := ![3, 2, 1, 0, 5, 4]

/-- Seven times the orthogonal reflection in the normal (0,0,2,0,3,−1). -/
def reflected : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![7, 0, 0, 0, 0, 0],
    ![0, 7, 0, 0, 0, 0],
    ![0, 0, 3, 0, -6, 2],
    ![0, 0, 0, 7, 0, 0],
    ![0, 0, -6, 0, -2, 3],
    ![0, 0, 2, 0, 3, 6]]

theorem height : ∀ a k, |rays a k| ≤ 16 := by decide +kernel

theorem height_attained : ∃ a k, |rays a k| = 16 := by decide +kernel

theorem perm_involutive : ∀ i, perm (perm i) = i := by decide +kernel

theorem reflection_symmetric : reflected.transpose = reflected := by decide +kernel

theorem reflection_square : reflected * reflected = 49 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide +kernel

/-- Vanishing minors compare actual integer images to the designated transpose entries. -/
theorem reflection_symmetry : ∀ i j k l,
    let v := reflected.mulVec (rays (labels i j))
    let w := rays (labels (perm j) (perm i))
    v k * w l = v l * w k := by decide +kernel

theorem cover : ∀ a, ∃ p : Cell 6, labels p.1 p.2 = a := by decide +kernel
theorem nonzero : ∀ a, ∃ k, rays a k ≠ 0 := by decide +kernel

/-- The factors compare primitive, unnormalized representatives under seven times the reflection. -/
def reflectionFactor : Fin 6 → Fin 6 → ℤ :=
  ![![7,7,1,7,-1,1],![49,7,7,49,7,7],![-7,7,7,7,-1,-1],
    ![7,-7,1,7,1,1],![49,-49,7,49,7,7],![49,-49,7,-49,7,7]]

theorem reflection_int_scalar : ∀ i j, reflectionFactor i j≠0 ∧
    reflected.mulVec (rays (labels i j)) =
      reflectionFactor i j • rays (labels (perm j) (perm i)) := by decide +kernel

/-- The rational Householder matrix acts on all vectors as an involutive isometry. -/
def reflectionQ : Matrix (Fin 6) (Fin 6) ℚ :=
  (7 : ℚ)⁻¹ • reflected.map (Int.castRingHom ℚ)

theorem reflectionQ_symmetric : reflectionQ.transpose=reflectionQ := by decide +kernel
theorem reflectionQ_squared : reflectionQ*reflectionQ=1 := by decide +kernel
theorem reflectionQ_orthogonal : reflectionQ.transpose*reflectionQ=1 := by
  rw [reflectionQ_symmetric,reflectionQ_squared]

noncomputable def reflectionOn (v : Space 6) : Space 6 :=
  WithLp.toLp 2 (fun k => (7 : ℂ)⁻¹ * ∑ l, (reflected k l : ℂ)*v l)

theorem reflectionOn_involutive : Function.Involutive reflectionOn := by
  intro v
  ext k
  fin_cases k <;> norm_num [reflectionOn,reflected,Fin.sum_univ_succ] <;> ring_nf <;> rfl

theorem reflectionOn_raw (v : Fin 6 → ℤ) :
    reflectionOn (integerModel.raw v) = (7 : ℂ)⁻¹ • integerModel.raw (reflected.mulVec v) := by
  ext k
  change (7 : ℂ)⁻¹ * (∑ l, (reflected k l : ℂ)*(v l : ℂ)) =
    7⁻¹ * ((∑ l, reflected k l*v l : ℤ) : ℂ)
  push_cast
  rfl

theorem reflection_ray_scalar (i j : Fin 6) :
    ∃ z : ℂ, z≠0 ∧ reflectionOn (integerModel.raw (rays (labels i j))) =
      z • integerModel.raw (rays (labels (perm j) (perm i))) := by
  obtain ⟨hne,he⟩ := reflection_int_scalar i j
  refine ⟨(7 : ℂ)⁻¹*(reflectionFactor i j : ℂ),mul_ne_zero (by norm_num) (by exact_mod_cast hne),?_⟩
  rw [reflectionOn_raw,he]
  ext k
  change (7 : ℂ)⁻¹ * ((reflectionFactor i j * rays (labels (perm j) (perm i)) k : ℤ) : ℂ) = _
  push_cast
  change 7⁻¹*((reflectionFactor i j : ℂ)*(rays (labels (perm j) (perm i)) k : ℂ)) = _
  rw [← mul_assoc]
  rfl

theorem raw_ray_nz (a : Fin 29) : integerModel.raw (rays a)≠0 := by
  obtain ⟨k,hk⟩ := nonzero a
  intro he
  have h : ((rays a k : ℤ) : ℂ)=0 := congrArg (fun v : Space 6 => v k) he
  exact hk (by exact_mod_cast h)

theorem reflected_ray_nz (i j : Fin 6) :
    reflectionOn (integerModel.raw (rays (labels i j)))≠0 := by
  obtain ⟨z,hz,h⟩ := reflection_ray_scalar i j
  rw [h]
  exact smul_ne_zero hz (raw_ray_nz _)

/-- The complex projective action of the genuine Householder reflection. -/
theorem reflection_projective (i j : Fin 6) :
    Projectivization.mk ℂ (reflectionOn (integerModel.raw (rays (labels i j))))
      (reflected_ray_nz i j) =
    Projectivization.mk ℂ (integerModel.raw (rays (labels (perm j) (perm i))))
      (raw_ray_nz _) := by
  obtain ⟨z,_,he⟩ := reflection_ray_scalar i j
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨z,he.symm⟩

theorem separate : integerModel.DistinctLines rays := by
  apply integerModel.distinct_of_pivots ![0, 1, 2, 3, 4, 5, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1]
  decide +kernel
theorem rows : ∀ i, integerModel.Orthogonal (fun j => rays (labels i j)) := by decide +kernel
theorem cols : ∀ j, integerModel.Orthogonal (fun i => rays (labels i j)) := by decide +kernel

theorem realized : Realized 6 29 :=
  integerModel.certify rays (fun p => labels p.1 p.2) cover nonzero separate rows cols

#print axioms realized
#print axioms reflection_symmetry
#print axioms reflection_projective
#print axioms reflectionOn_involutive
#print axioms reflectionQ_orthogonal
end SmallSixRational29
