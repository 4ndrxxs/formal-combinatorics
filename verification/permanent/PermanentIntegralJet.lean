import PermanentJetFrame

/-! Integer row and column operations give short certificates for a simple
zero of a principal Hessian. All field-specific conclusions
follow by mapping one integral first-order calculation. -/

noncomputable section
open Matrix Module Polynomial QuinticPencil TrivSqZeroExt
namespace PermanentFive
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

private def pack (A B : Matrix I I R) : Matrix I I (DualNumber R) :=
  Matrix.of fun i j ↦ ⟨A i j,B i j⟩

private theorem pack_left (L A B : Matrix I I R) :
    (inlHom R R).mapMatrix L * pack A B = pack (L*A) (L*B) := by
  ext1 i j
  apply TrivSqZeroExt.ext <;> simp [pack,Matrix.mul_apply,fst_sum,snd_sum] <;> rfl

private theorem pack_right (A B L : Matrix I I R) :
    pack A B * (inlHom R R).mapMatrix L = pack (A*L) (B*L) := by
  ext1 i j
  apply TrivSqZeroExt.ext <;> simp [pack,Matrix.mul_apply,fst_sum,snd_sum] <;> rfl

private theorem transformed_jet {n : ℕ} (r : Fin n) (A B L V : Matrix (Fin n) (Fin n) ℤ) (d : ℤ) (nd : d ≠ 0)
    (straight : ∀ i j, (L*A*V) i j = if i=j ∧ i≠r then d else 0)
    (slope : (L*B*V) r r ≠ 0) :
    (pack A B).det.fst = 0 ∧ (pack A B).det.snd ≠ 0 := by
  let M := pack (L*A*V) (L*B*V)
  have off (i j : Fin n) (ne : i ≠ j) : (M i j).fst = 0 := by
    change (L*A*V) i j = 0
    simp [straight,ne]
  have f0 : (M r r).fst = 0 := by change (L*A*V) r r = 0; simp [straight]
  have diag (i : Fin n) (hi : i ≠ r) : (M i i).fst = d := by
    change (L*A*V) i i = d
    simp [straight,hi]
  let rest := ∏ i ∈ Finset.univ.erase (r : Fin n), M i i
  have nonzero : rest.fst ≠ 0 := by
    change (TrivSqZeroExt.fstHom ℤ ℤ ℤ) rest ≠ 0
    dsimp only [rest]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    change (M i i).fst ≠ 0
    rw [diag i (Finset.mem_erase.mp hi).1]
    exact nd
  have MD : M.det = M r r * rest := by
    rw [diagonal_jet_det M off]
    exact (Finset.mul_prod_erase Finset.univ (fun i ↦ M i i) (Finset.mem_univ (r : Fin n))).symm
  have nz : M.det.snd ≠ 0 := by
    rw [MD,DualNumber.snd_mul,f0,zero_mul,zero_add]
    exact mul_ne_zero slope nonzero
  have mz : M.det.fst = 0 := by rw [MD,TrivSqZeroExt.fst_mul,f0,zero_mul]
  have fact : (inlHom ℤ ℤ).mapMatrix L * pack A B * (inlHom ℤ ℤ).mapMatrix V = M := by
    rw [pack_left,pack_right]
  have eq := congrArg Matrix.det fact
  rw [Matrix.det_mul,Matrix.det_mul,← RingHom.map_det,← RingHom.map_det] at eq
  have e0 : L.det * (pack A B).det.fst * V.det = 0 := by
    simpa using (congrArg TrivSqZeroExt.fst eq).trans mz
  have e1 : L.det * (pack A B).det.snd * V.det ≠ 0 := by
    have h := (congrArg TrivSqZeroExt.snd eq)
    rw [← h] at nz
    simpa [DualNumber.snd_mul] using nz
  have n := mul_ne_zero_iff.mp e1
  exact ⟨((mul_eq_zero.mp ((mul_eq_zero.mp e0).resolve_right n.2)).resolve_left
    (mul_ne_zero_iff.mp n.1).1),(mul_ne_zero_iff.mp n.1).2⟩

theorem simple_zero_of_integers {n : ℕ} (r : Fin n) {K : Type*} [Field K] [CharZero K]
    (S : Finset Cell) (v : Fin n → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j)
    (y : Cell → DualNumber ℤ) (A B L V : Matrix (Fin n) (Fin n) ℤ)
    (entries : ∀ i j, secondAt y (v i) (v j) = (⟨A i j,B i j⟩ : DualNumber ℤ))
    (d : ℤ) (nd : d ≠ 0) (straight : ∀ i j, (L*A*V) i j = if i=j ∧ i≠r then d else 0)
    (slope : (L*B*V) r r ≠ 0) : HasSimpleZeroBlock K n S := by
  let f := jetMap (Int.castRingHom K)
  refine ⟨v,f ∘ y,cover,?_⟩
  have eq : (hessian (per (DualNumber K) Idx) (f ∘ y)).submatrix v v = f.mapMatrix (pack A B) := by
    ext1 i j
    change hessian _ _ (v i) (v j) = f (pack A B i j)
    rw [second_formula,second_map,entries]
    rfl
  rw [eq,← RingHom.map_det]
  obtain ⟨zero,nz⟩ := transformed_jet r A B L V d nd straight slope
  change ((pack A B).det.fst : K) = 0 ∧ ((pack A B).det.snd : K) ≠ 0
  exact ⟨by exact_mod_cast zero,by exact_mod_cast nz⟩

theorem odd_block_of_integers {K : Type*} [Field K] [CharZero K]
    (S : Finset Cell) (v : Fin 12 → Cell) (cover : ∀ j ∈ S, ∃ i, v i = j)
    (y : Cell → DualNumber ℤ) (A B L V : Matrix (Fin 12) (Fin 12) ℤ)
    (entries : ∀ i j, secondAt y (v i) (v j) = (⟨A i j,B i j⟩ : DualNumber ℤ))
    (d : ℤ) (nd : d ≠ 0) (straight : ∀ i j, (L*A*V) i j = if i=j ∧ i≠11 then d else 0)
    (slope : (L*B*V) 11 11 ≠ 0) : HasOddBlock K S :=
  simple_zero_of_integers 11 S v cover y A B L V entries d nd straight slope

#print axioms odd_block_of_integers
end PermanentFive
