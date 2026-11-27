module

public import Quantum.AbelianDiagonal

/-! Finite witness over the product of cyclic groups of orders 2, 2, 2, 3.
    All finite equations below are checked by kernel reduction. -/
@[expose] public section
namespace QuantumCertificate.DiagonalOrders.N24
open AbelianDiagonal
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private abbrev G := ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 3)))
private def rank (x : G) : ℕ := x.1.val * 12 + x.2.1.val * 6 + x.2.2.1.val * 3 + x.2.2.2.val * 1
private def decode (i : ℕ) : G := (((i / 12 : ℕ) : ZMod 2),((i / 6 : ℕ) : ZMod 2),((i / 3 : ℕ) : ZMod 2),((i / 1 : ℕ) : ZMod 3))
private def coord : Fin 24 ≃ G where
  toFun i := decode i.val
  invFun x := ⟨rank x % 24, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axis : Fin 24 ≃ G where
  toFun i := decode ((#[0,1,2,6,7,8,12,13,14,18,19,20,23,22,21,17,16,15,11,10,9,5,4,3] : Array ℕ)[i.val]!)
  invFun x := ⟨(#[0,1,2,23,22,21,3,4,5,20,19,18,6,7,8,17,16,15,9,10,11,14,13,12] : Array ℕ)[rank x]! % 24, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def f (x : G) : G := decode ((#[0,14,12,21,20,6,22,9,17,5,7,2,8,23,19,16,1,15,13,4,10,18,3,11] : Array ℕ)[rank x]!)

private def fInv (x : G) : G := decode ((#[0,16,11,22,19,9,5,10,12,7,20,23,2,18,1,17,15,8,21,14,4,3,6,13] : Array ℕ)[rank x]!)
private theorem fBij : Function.Bijective f :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse fInv f by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse fInv f by decide +kernel)⟩

private def plusInv (x : G) : G := decode ((#[0,15,17,21,7,10,14,18,9,13,11,5,1,23,2,20,6,16,3,22,12,4,8,19] : Array ℕ)[rank x]!)
private theorem plusBij : Function.Bijective (fun x : G => x + f x) :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse plusInv (fun x : G => x + f x) by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse plusInv (fun x : G => x + f x) by decide +kernel)⟩

private def w (x : G) : ℕ × ℕ × ℕ × ℕ :=
  (#[(7,10,1,20),(7,10,7,10),(7,10,2,18),(7,10,2,8),(7,10,6,14),(7,10,1,7),(7,10,1,5),(7,10,1,23),(7,10,1,16),(7,10,1,2),(7,10,1,4),(7,10,0,0),(7,10,2,10),(7,10,3,19),(7,10,1,9),(7,10,1,19),(7,10,1,10),(7,10,1,8),(7,10,1,11),(7,10,3,18),(7,10,1,3),(7,10,3,17),(7,10,1,1),(7,10,4,12)] : Array (ℕ × ℕ × ℕ × ℕ))[rank x]!

private theorem spans : Spans f := by
  have h : ∀ x : G, defect f (decode (w x).1) (decode (w x).2.1) +
      defect f (decode (w x).2.2.1) (decode (w x).2.2.2) = x := by decide +kernel
  intro x
  exact ⟨_,_,_,_,h x⟩

theorem existence : MaximalDiagonal 24 := by
  apply construct (productPairing (cyclic 2) (productPairing (cyclic 2) (productPairing (cyclic 2) (cyclic 3)))) axis coord (by decide +kernel) f
    (by decide +kernel) fBij plusBij spans
  exact Or.inl ⟨decode 3, by decide +kernel⟩

end QuantumCertificate.DiagonalOrders.N24
