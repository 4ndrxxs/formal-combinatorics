module
public import Quantum.Diagonal
/-! Diagonal quantum Latin squares with an arbitrary number of complex rays. -/
@[expose] public section
noncomputable section
namespace QuantumCertificate

structure DiagonalArray (n : ℕ) where
  entry : Cell n → Space n
  nz : ∀ p, entry p≠0
  rows : ∀ i, IsBasisLine entry (fun j => (i,j))
  cols : ∀ j, IsBasisLine entry (fun i => (i,j))
  main : IsBasisLine entry (mainDiag n)
  anti : IsBasisLine entry (antiDiag n)

def DiagonalArray.ray {n} (a : DiagonalArray n) (p : Cell n) :=
  Projectivization.mk ℂ (a.entry p) (a.nz p)

def DiagonalRealized (n c : ℕ) : Prop :=
  ∃ a : DiagonalArray n, (Set.range a.ray).ncard=c

theorem diagonal_certificate {n c d M : ℕ} [NeZero n] (hd : 0<d) (hM : 0<M)
    (r : Fin c → Fin n → IQ) (label : Cell n → Fin c)
    (cover : ∀ k, ∃ p, label p=k) (sep : Separated d r)
    (rows : ∀ i, GramTest d M (fun j => r (label (i,j))))
    (cols : ∀ j, GramTest d M (fun i => r (label (i,j))))
    (main : GramTest d M (fun i => r (label (mainDiag n i))))
    (anti : GramTest d M (fun i => r (label (antiDiag n i)))) : DiagonalRealized n c := by
  classical
  let entry (p : Cell n) := vector d M (r (label p))
  have rb (i) : IsBasisLine entry (fun j => (i,j)) := basis_of_test hM _ (rows i)
  have nz (p : Cell n) : entry p≠0 := by
    obtain ⟨B,e⟩ := rb p.1
    have h := B.orthonormal
    rw [e] at h
    exact h.ne_zero p.2
  let a : DiagonalArray n := ⟨entry,nz,rb,fun j => basis_of_test hM _ (cols j),
    basis_of_test hM _ main,basis_of_test hM _ anti⟩
  have nz' (k : Fin c) : vector d M (r k)≠0 := by
    obtain ⟨p,rfl⟩ := cover k
    exact nz p
  let ray (k : Fin c) := Projectivization.mk ℂ (vector d M (r k)) (nz' k)
  have inj : Function.Injective ray := by
    intro i j h
    by_contra hne
    obtain ⟨x,y,ne⟩ := sep i j hne
    obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have scalar : (Real.sqrt (M:ℝ):ℂ)⁻¹ ≠ 0 := by
      apply inv_ne_zero; exact_mod_cast (show Real.sqrt (M:ℝ)≠0 by positivity)
    have atCoord (x : Fin n) : s*embed d (r j x)=embed d (r i x) := by
      have u := congrArg (fun v : Space n => v x) hs
      change s*(_*embed d (r j x))=_*embed d (r i x) at u
      apply mul_left_cancel₀ scalar
      linear_combination u
    apply ne (embed_injective hd ?_)
    rw [embed_times,embed_times,← atCoord x,← atCoord y]
    ring
  refine ⟨a,?_⟩
  change (Set.range (ray ∘ label)).ncard=c
  rw [Function.Surjective.range_comp cover,Set.ncard_range_of_injective inj]
  simp
end QuantumCertificate
