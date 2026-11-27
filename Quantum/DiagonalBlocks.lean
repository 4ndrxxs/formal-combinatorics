module

public import Quantum.EvenSpectrum

/-! A finite diagonal-block certificate may be reused in the opposite corners. -/
@[expose] public section
namespace QuantumCertificate

def evenMask (m : ℕ) (p : Cell (m+m)) : Bool :=
  decide (p.1.val < m) == decide (p.2.val < m)

def swapHalf (m : ℕ) : Fin (m+m) ≃ Fin (m+m) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin m) (Fin m)).trans finSumFinEquiv)

theorem diagonal_pair {m x y : ℕ} [NeZero (m+m)]
    (flip : ∀ p : Cell (m+m), evenMask m (p.1,swapHalf m p.2) = !(evenMask m p))
    (ha : Nonempty (PartialArray (m+m) m x (evenMask m)))
    (hb : Nonempty (PartialArray (m+m) m y (evenMask m))) : Realized (m+m) (x+y) := by
  obtain ⟨a⟩ := ha
  obtain ⟨b⟩ := hb
  let part := (IndexedArray.ofPartial b).reindex (Equiv.refl _) (swapHalf m)
  have mask : (fun p : Cell (m+m) => evenMask m ((Equiv.refl _) p.1,swapHalf m p.2)) =
      (fun p => !(evenMask m p)) := funext flip
  have h := IndexedArray.join (IndexedArray.ofPartial a) (part.changeMask mask) (Equiv.refl _)
  simpa only [part,IndexedArray.rays_changeMask,IndexedArray.rays_reindex,
    IndexedArray.rays_ofPartial,show a.rays.ncard = x from a.count,
    show b.rays.ncard = y from b.count] using h

end QuantumCertificate
