import PaleyAllOrders
import Quantum.Hadamard.ProjectiveSplitComparison

/-! The four-fifths determinant bound for every near-Hadamard constant sign
border of a two-circulant layout of one set from each column of Theorem 4.1
of Momihara, Suda and Xiang. -/

noncomputable section
open Matrix Finset
open Hadamard.NearBorder Hadamard.ProjectiveSigning
namespace Hadamard.MSXCore

theorem source_borders_four_fifths {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {m : ℕ} [NeZero m] (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (w : F) (hw : quadraticChar F w= -1) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val)
    (i j : Bool) (u : CyclicLayout m) (T L H : Matrix Bool Bool ℝ)
    (ht : Signs T) (hl : Signs L) (hh : Signs H)
    (p : Partition (bordered (u.core (sourcePair w i j e)) T L H*
      (bordered (u.core (sourcePair w i j e)) T L H).transpose)) :
    (4/5:ℝ)*(2*(Fintype.card F:ℝ))*((Fintype.card F:ℝ)-1)^(Fintype.card F/2) ≤
      |(bordered (u.core (sourcePair w i j e)) T L H).det| := by
  have hc : ringChar F≠2 := by
    intro eq
    have h:=FiniteField.even_card_of_char_two eq
    omega
  have size : m=(Fintype.card F-1)/2 := by
    simpa only [Fintype.card_fin,square_index_card w hw] using Fintype.card_congr e
  rw [compare_source_layout hc q4 (by omega) w hw e cyc i j u T L H ht hl hh p]
  have h := split_resolves (F:=F) i
  have lower := quadratic_paley_four_fifths_all q4 lo (0:F) 1 0 (by simp) (splitSign i)
    (-cosetSign i) (by cases i <;> norm_num [cosetSign]) h.1 h.2
  simpa only [reference,signInt,Int.cast_ite,Int.cast_neg,Int.cast_one] using lower

#print axioms source_borders_four_fifths

end Hadamard.MSXCore
