import PaleyField29
import PaleyField37
import PaleyField41
import PaleyField49
import PaleyField53
import PaleyField61
import PaleyField73
import PaleyField81
import PaleyField89
import PaleyField97
import PaleyField101

noncomputable section
open Finset Matrix
namespace Hadamard.ProjectiveSigning

private theorem smallOrders : ∀q : Fin 109, 29≤q.val → q.val%4=1 → IsPrimePow q.val →
    q.val=29 ∨ q.val=37 ∨ q.val=41 ∨ q.val=49 ∨ q.val=53 ∨ q.val=61 ∨ q.val=73 ∨ q.val=81 ∨ q.val=89 ∨ q.val=97 ∨ q.val=101 := by decide +kernel

private theorem smallCertified (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (lo : 29≤Fintype.card F) (hi : Fintype.card F<109) (q4 : Fintype.card F%4=1) :
    CertifiedPatterns F := by
  have h := smallOrders ⟨Fintype.card F,hi⟩ lo q4 (FiniteField.isPrimePow_card F)
  obtain h|h|h|h|h|h|h|h|h|h|h := h
  · exact certified_of_card (h.trans PaleyField29.card.symm) PaleyField29.canonical
  · exact certified_of_card (h.trans PaleyField37.card.symm) PaleyField37.canonical
  · exact certified_of_card (h.trans PaleyField41.card.symm) PaleyField41.canonical
  · exact certified_of_card (h.trans PaleyField49.card.symm) PaleyField49.canonical
  · exact certified_of_card (h.trans PaleyField53.card.symm) PaleyField53.canonical
  · exact certified_of_card (h.trans PaleyField61.card.symm) PaleyField61.canonical
  · exact certified_of_card (h.trans PaleyField73.card.symm) PaleyField73.canonical
  · exact certified_of_card (h.trans PaleyField81.card.symm) PaleyField81.canonical
  · exact certified_of_card (h.trans PaleyField89.card.symm) PaleyField89.canonical
  · exact certified_of_card (h.trans PaleyField97.card.symm) PaleyField97.canonical
  · exact certified_of_card (h.trans PaleyField101.card.symm) PaleyField101.canonical

/-- The four-fifths bound for the actual real Paley matrix and every
nonsingular quadratic signing at every eligible order starting at 30. -/
theorem quadratic_paley_four_fifths_all {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (a b c : F) (disc : b^2-4*a*c≠0) (s : Option F→Bool) (w : ℤ) (unit : w^2=1)
    (agree : ∀i, quadraticValue a b c i≠0 →
      (if s i then (1:ℤ) else -1)=w*quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i, if quadraticValue a b c i=0 then (if s i then (1:ℤ) else -1) else 0)=0) :
    let q := Fintype.card F
    (4/5:ℝ)*(2*(q:ℝ))*((q:ℝ)-1)^(q/2) ≤
      |(realPaley+diagonal (fun i ↦ if s i then (1:ℝ) else -1)).det| := by
  have hc : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  by_cases large : 109≤Fintype.card F
  · exact quadratic_paley_four_fifths_109 hc q4 large a b c disc s w agree ties
  have m := smallCertified F lo (by omega) q4
  have bound := quadratic_of_certified m hc q4 a b c disc s w unit agree ties
  simpa [fourFifths,signedDet,signOf,Int.cast_ite,mul_assoc] using bound

#print axioms quadratic_paley_four_fifths_all
end Hadamard.ProjectiveSigning
