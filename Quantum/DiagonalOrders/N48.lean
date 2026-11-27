module

public import Quantum.AbelianDiagonal

/-! Finite witness over the product of cyclic groups of orders 2, 2, 2, 2, 3.
    All finite equations below are checked by kernel reduction. -/
@[expose] public section
namespace QuantumCertificate.DiagonalOrders.N48
open AbelianDiagonal
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private abbrev G := ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 2 × (ZMod 3))))
private def rank (x : G) : ℕ := x.1.val * 24 + x.2.1.val * 12 + x.2.2.1.val * 6 + x.2.2.2.1.val * 3 + x.2.2.2.2.val * 1
private def decode (i : ℕ) : G := (((i / 24 : ℕ) : ZMod 2),((i / 12 : ℕ) : ZMod 2),((i / 6 : ℕ) : ZMod 2),((i / 3 : ℕ) : ZMod 2),((i / 1 : ℕ) : ZMod 3))
private def coord : Fin 48 ≃ G where
  toFun i := decode i.val
  invFun x := ⟨rank x % 48, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def axis : Fin 48 ≃ G where
  toFun i := decode ((#[0,1,2,6,7,8,12,13,14,18,19,20,24,25,26,30,31,32,36,37,38,42,43,44,47,46,45,41,40,39,35,34,33,29,28,27,23,22,21,17,16,15,11,10,9,5,4,3] : Array ℕ)[i.val]!)
  invFun x := ⟨(#[0,1,2,47,46,45,3,4,5,44,43,42,6,7,8,41,40,39,9,10,11,38,37,36,12,13,14,35,34,33,15,16,17,32,31,30,18,19,20,29,28,27,21,22,23,26,25,24] : Array ℕ)[rank x]! % 48, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def f (x : G) : G := decode ((#[0,35,13,28,8,41,30,4,9,18,42,15,16,45,12,10,7,31,44,14,25,38,27,40,23,39,3,34,37,20,33,19,21,36,6,5,26,24,1,43,46,32,2,11,22,17,29,47] : Array ℕ)[rank x]!)

private def fInv (x : G) : G := decode ((#[0,38,42,26,7,35,34,16,4,8,15,43,14,2,19,11,12,45,9,31,29,32,44,24,37,20,36,22,3,46,6,17,41,30,27,1,33,28,21,25,23,5,10,39,18,13,40,47] : Array ℕ)[rank x]!)
private theorem fBij : Function.Bijective f :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse fInv f by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse fInv f by decide +kernel)⟩

private def plusInv (x : G) : G := decode ((#[0,47,14,30,12,8,19,27,40,4,39,7,2,37,36,9,25,28,46,15,11,33,41,16,6,3,18,44,34,26,23,35,45,1,13,21,38,5,31,43,10,32,20,22,42,17,29,24] : Array ℕ)[rank x]!)
private theorem plusBij : Function.Bijective (fun x : G => x + f x) :=
  ⟨Function.LeftInverse.injective (show Function.LeftInverse plusInv (fun x : G => x + f x) by decide +kernel),
   Function.RightInverse.surjective (show Function.RightInverse plusInv (fun x : G => x + f x) by decide +kernel)⟩

private def w (x : G) : ℕ × ℕ × ℕ × ℕ :=
  (#[(5,23,1,4),(5,23,5,23),(5,23,1,1),(5,23,1,33),(5,23,2,16),(5,23,2,32),(5,23,3,7),(5,23,1,30),(5,23,1,29),(5,23,1,25),(5,23,2,9),(5,23,1,19),(5,23,1,10),(5,23,1,3),(5,23,0,0),(5,23,1,18),(5,23,1,24),(5,23,1,12),(5,23,1,8),(5,23,2,47),(5,23,2,24),(5,23,1,9),(5,23,1,37),(5,23,3,38),(5,23,1,27),(5,23,1,44),(5,23,4,46),(5,23,1,46),(5,23,1,20),(5,23,1,26),(5,23,2,25),(5,23,1,21),(5,23,2,13),(5,23,2,4),(5,23,1,22),(5,23,1,2),(5,23,1,11),(5,23,2,26),(5,23,1,34),(5,23,2,31),(5,23,5,11),(5,23,1,7),(5,23,1,15),(5,23,1,14),(5,23,1,31),(5,23,4,30),(5,23,1,36),(5,23,2,2)] : Array (ℕ × ℕ × ℕ × ℕ))[rank x]!

private theorem spans : Spans f := by
  have h : ∀ x : G, defect f (decode (w x).1) (decode (w x).2.1) +
      defect f (decode (w x).2.2.1) (decode (w x).2.2.2) = x := by decide +kernel
  intro x
  exact ⟨_,_,_,_,h x⟩

theorem existence : MaximalDiagonal 48 := by
  apply construct (productPairing (cyclic 2) (productPairing (cyclic 2) (productPairing (cyclic 2) (productPairing (cyclic 2) (cyclic 3))))) axis coord (by decide +kernel) f
    (by decide +kernel) fBij plusBij spans
  exact Or.inl ⟨decode 3, by decide +kernel⟩

end QuantumCertificate.DiagonalOrders.N48
