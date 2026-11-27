module

public import Quantum.PartialCertificates

/-! The thirty projectively different ordered quotients of rows of Tao's
order-six Butson matrix, expressed in the orthogonal complement of the
constant row. Coefficients (a,b) denote a + b i sqrt(3). -/

@[expose] public section
namespace UniversalPuncture
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def sixReps : Array (Array IQ) := #[
  #[(2, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
  #[(0, 0), (2, 0), (0, 0), (0, 0), (0, 0)],
  #[(0, 0), (0, 0), (2, 0), (0, 0), (0, 0)],
  #[(0, 0), (0, 0), (0, 0), (2, 0), (0, 0)],
  #[(0, 0), (0, 0), (0, 0), (0, 0), (2, 0)],
  #[(0, 0), (2, 0), (2, 0), (-1, -1), (-1, -1)],
  #[(2, 0), (0, 0), (1, 1), (-2, 0), (1, 1)],
  #[(2, 0), (1, 1), (0, 0), (1, 1), (-2, 0)],
  #[(2, 0), (1, -1), (-2, 0), (0, 0), (1, -1)],
  #[(2, 0), (-2, 0), (1, -1), (1, -1), (0, 0)],
  #[(2, 0), (0, 0), (-1, -1), (2, 0), (-1, -1)],
  #[(0, 0), (2, 0), (-2, 0), (1, 1), (1, 1)],
  #[(2, 0), (1, 1), (0, 0), (-1, -1), (2, 0)],
  #[(2, 0), (1, -1), (2, 0), (0, 0), (-1, 1)],
  #[(2, 0), (-2, 0), (-1, 1), (-1, 1), (0, 0)],
  #[(2, 0), (-1, -1), (0, 0), (-1, -1), (2, 0)],
  #[(0, 0), (2, 0), (-2, 0), (-1, -1), (-1, -1)],
  #[(2, 0), (0, 0), (1, 1), (2, 0), (-1, -1)],
  #[(2, 0), (-1, 1), (-2, 0), (0, 0), (-1, 1)],
  #[(2, 0), (2, 0), (1, -1), (-1, 1), (0, 0)],
  #[(2, 0), (-1, 1), (2, 0), (0, 0), (-1, 1)],
  #[(0, 0), (2, 0), (2, 0), (1, 1), (-1, -1)],
  #[(2, 0), (0, 0), (-1, -1), (-2, 0), (-1, -1)],
  #[(2, 0), (-1, -1), (0, 0), (1, 1), (2, 0)],
  #[(2, 0), (2, 0), (-1, 1), (1, -1), (0, 0)],
  #[(2, 0), (2, 0), (-1, 1), (-1, 1), (0, 0)],
  #[(0, 0), (2, 0), (2, 0), (-1, -1), (1, 1)],
  #[(2, 0), (0, 0), (-1, -1), (2, 0), (1, 1)],
  #[(2, 0), (-1, -1), (0, 0), (-1, -1), (-2, 0)],
  #[(2, 0), (-1, 1), (2, 0), (0, 0), (1, -1)]]

private def sixRep (i : Fin 30) (x : Fin 5) : IQ := (sixReps[i.val]!)[x.val]!
private def sixLabel (p : Cell 6) : Fin 30 :=
  (#[0, 0, 1, 2, 3, 4, 5, 0, 6, 7, 8, 9, 10, 11, 0, 12, 13, 14, 15, 16, 17, 0, 18, 19, 20, 21, 22, 23, 0, 24, 25, 26, 27, 28, 29, 0] : Array (Fin 30))[p.1.val * 6 + p.2.val]!
private def sixPivot (i : Fin 30) : Fin 5 :=
  (#[0, 1, 2, 3, 4, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0] : Array (Fin 5))[i.val]!
private def sixWitness (i : Fin 30) : Cell 6 :=
  let n := (#[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34] : Array ℕ)[i.val]!
  (Fin.ofNat 6 (n/6),Fin.ofNat 6 (n%6))

theorem puncture_six : Nonempty (PartialArray 6 5 30 (fun p => p.1 != p.2)) := by
  apply (imaginaryModel 3 (by decide)).partialArray _ sixRep sixLabel sixPivot (2,0) (by decide)
  · decide +kernel
  · change ∀ ⦃i j : Fin 30⦄, sixRep i = sixRep j → i = j
    decide +kernel
  · have h : ∀ i : Fin 30, ((sixWitness i).1 != (sixWitness i).2) = true ∧
        sixLabel (sixWitness i) = i := by decide +kernel
    exact fun i => ⟨sixWitness i,h i⟩
  all_goals decide +kernel

#print axioms puncture_six
end UniversalPuncture
