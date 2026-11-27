import PermanentRankCertificate

/-! Fraction-free integer column-span and inverse certificates for ranks in characteristic zero. -/
noncomputable section
open Matrix
namespace PermanentBorder
variable {K I : Type*} [Field K] [CharZero K] [Fintype I]

omit [CharZero K] in
private theorem cast_integer_smul {J L : Type*} (c : ℤ) (M : Matrix J L ℤ) :
    (c • M).map (Int.castRingHom K)=(c:K) • M.map (Int.castRingHom K) := by
  ext i j
  simp [Matrix.smul_apply]

omit [CharZero K] in
theorem rank_certificate_scalars {k : ℕ} (A : Matrix I I ℤ) (pick : Fin k → I)
    (V : Matrix (Fin k) I ℤ) (W : Matrix (Fin k) (Fin k) ℤ) (d e : ℤ)
    (full : e • A=A.submatrix id pick*V) (minor : W*A.submatrix pick pick=d • 1)
    (de : (d:K)≠0) (ee : (e:K)≠0) : (A.map (Int.castRingHom K)).rank=k := by
  let f := Int.castRingHom K
  let B := A.map f
  have cols : (e:K) • B=B.submatrix id pick*V.map f := by
    change (e:K) • A.map f=(A.submatrix id pick).map f*V.map f
    rw [←cast_integer_smul,←Matrix.map_mul,full]
  have leftInv : W.map f*B.submatrix pick pick=(d:K) • 1 := by
    change W.map f*(A.submatrix pick pick).map f=(d:K) • 1
    rw [←Matrix.map_mul,minor,cast_integer_smul]
    simp
  have lo := (Matrix.rank_mul_le_right (W.map f) (B.submatrix pick pick)).trans
    (Matrix.rank_submatrix_le B pick pick)
  rw [leftInv,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero de),
    Matrix.rank_one,Fintype.card_fin] at lo
  have hi := (Matrix.rank_mul_le_left (B.submatrix id pick) (V.map f)).trans
    (Matrix.rank_le_card_width _)
  rw [←cols,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ee),
    Fintype.card_fin] at hi
  exact le_antisymm hi lo

theorem rank_certificate_scaled {k : ℕ} (A : Matrix I I ℤ) (pick : Fin k → I)
    (V : Matrix (Fin k) I ℤ) (W : Matrix (Fin k) (Fin k) ℤ) (d e : ℤ)
    (full : e • A=A.submatrix id pick*V) (minor : W*A.submatrix pick pick=d • 1)
    (hd : d≠0) (he : e≠0) : (A.map (Int.castRingHom K)).rank=k :=
  rank_certificate_scalars A pick V W d e full minor (by exact_mod_cast hd) (by exact_mod_cast he)

#print axioms rank_certificate_scalars
end PermanentBorder
