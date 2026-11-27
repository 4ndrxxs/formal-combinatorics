module

public import Quantum.AbelianDiagonal

/-! Finite witness over the product of cyclic groups of orders 2, 2, 3.
    All finite equations below are checked by kernel reduction. -/
@[expose] public section
namespace QuantumCertificate.DiagonalOrders.N12
open AbelianDiagonal
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private abbrev G := ZMod 2 × (ZMod 2 × (ZMod 3))
private def rank (x : G) : ℕ := x.1.val * 6 + x.2.1.val * 3 + x.2.2.val * 1
private def decode (i : ℕ) : G := (((i / 6 : ℕ) : ZMod 2),((i / 3 : ℕ) : ZMod 2),((i / 1 : ℕ) : ZMod 3))
private def coord : Fin 12 ≃ G where
  toFun i := decode i.val
  invFun x := ⟨rank x % 12, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axis : Fin 12 ≃ G where
  toFun i := decode ((#[0,1,2,6,7,8,11,10,9,5,4,3] : Array ℕ)[i.val]!)
  invFun x := ⟨(#[0,1,2,11,10,9,3,4,5,8,7,6] : Array ℕ)[rank x]! % 12, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def f (x : G) : G := decode ((#[0,5,9,7,11,3,2,10,8,4,6,1] : Array ℕ)[rank x]!)

private def fInv (x : G) : G := decode ((#[0,11,6,5,9,1,10,3,8,2,7,4] : Array ℕ)[rank x]!)
private theorem fBij : Function.Bijective f :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse fInv f by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse fInv f by decide +kernel)⟩

private def plusInv (x : G) : G := decode ((#[0,8,5,1,10,7,4,9,6,11,3,2] : Array ℕ)[rank x]!)
private theorem plusBij : Function.Bijective (fun x : G => x + f x) :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse plusInv (fun x : G => x + f x) by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse plusInv (fun x : G => x + f x) by decide +kernel)⟩

private def w (x : G) : ℕ × ℕ × ℕ × ℕ :=
  (#[(4,9,2,2),(4,9,2,6),(4,9,4,9),(4,9,1,3),(4,9,0,0),(4,9,1,11),(4,9,1,1),(4,9,3,9),(4,9,1,8),(4,9,1,5),(4,9,1,6),(4,9,1,2)] : Array (ℕ × ℕ × ℕ × ℕ))[rank x]!

private theorem spans : Spans f := by
  have h : ∀ x : G, defect f (decode (w x).1) (decode (w x).2.1) +
      defect f (decode (w x).2.2.1) (decode (w x).2.2.2) = x := by decide +kernel
  intro x
  exact ⟨_,_,_,_,h x⟩

theorem existence : MaximalDiagonal 12 := by
  apply construct (productPairing (cyclic 2) (productPairing (cyclic 2) (cyclic 3))) axis coord (by decide +kernel) f
    (by decide +kernel) fBij plusBij spans
  exact Or.inl ⟨decode 3, by decide +kernel⟩

end QuantumCertificate.DiagonalOrders.N12
