module
public import Quantum.EvenSpectrum
public import Quantum.SmallSevenLow7
public import Quantum.SmallSevenLow17
public import Quantum.SmallSevenPhases
public import Quantum.SmallSevenGuo.Cardinality24
public import Quantum.SmallSevenGuo.Cardinality25
public import Quantum.SmallSevenGuo.Cardinality26
public import Quantum.SmallSevenGuo.Cardinality27
public import Quantum.SmallSevenGuo.Cardinality28
public import Quantum.SmallSevenGuo.Cardinality29
public import Quantum.SmallSevenGuo.Cardinality30
public import Quantum.SmallSevenGuo.Cardinality31
public import Quantum.SmallSevenGuo.Cardinality32
public import Quantum.SmallSevenGuo.Cardinality33
public import Quantum.SmallSevenGuo.Cardinality34
public import Quantum.SmallSevenGuo.Cardinality35
public import Quantum.SmallSevenGuo.Cardinality36
public import Quantum.SmallSevenGuo.Cardinality37
public import Quantum.SmallSevenGuo.Cardinality38
public import Quantum.SmallSevenGuo.Cardinality39
public import Quantum.SmallSevenGuo.Cardinality40
public import Quantum.SmallSevenGuo.Cardinality42

/-! The full positive order-seven spectrum. Yuankai Guo's published Lean
certificates provide 24–40 (and 42); explicit rational and imaginary quadratic
certificates provide the remaining positive cardinalities. -/
@[expose] public section
namespace SmallSeven

open QuantumCertificate

theorem of_guo {n c : ℕ} [NeZero n] (h : ∃ q : QLS7.QuantumLatinSquare n, q.cardinality = c) :
    Realized n c := by
  classical
  obtain ⟨q,hq⟩ := h
  have mk (w : Fin n → Space n) (hw : Orthonormal ℂ w) :
      ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = w :=
    ⟨OrthonormalBasis.mk hw (hw.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge,
      OrthonormalBasis.coe_mk _ _⟩
  refine ⟨q.entry,q.entry_ne_zero,fun i => mk _ (q.row_orthonormal i),
    fun j => mk _ (q.column_orthonormal j), ?_⟩
  change (Set.range q.ray).ncard = c
  convert hq using 1
  change (Set.range q.ray).ncard = (Finset.univ.image q.ray).card
  rw [← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem good : Good 7 := by
  intro c lo hi hole
  have upper : c ≤ 49 := by omega
  interval_cases c <;> first
    | exact card7
    | exact card9
    | exact card10
    | exact card11
    | exact card12
    | exact card13
    | exact card14
    | exact card15
    | exact card16
    | exact card17
    | exact card18
    | exact card19
    | exact card20
    | exact card21
    | exact card22
    | exact card23
    | exact of_guo QLS7.Cardinality24.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality25.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality26.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality27.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality28.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality29.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality30.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality31.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality32.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality33.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality34.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality35.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality36.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality37.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality38.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality39.exists_quantumLatinSquare
    | exact of_guo QLS7.Cardinality40.exists_quantumLatinSquare
    | exact card41
    | exact of_guo QLS7.Cardinality42.exists_quantumLatinSquare
    | exact card43
    | exact card44
    | exact card45
    | exact card46
    | exact card47
    | exact card48
    | exact card49
    | omega

#print axioms good
end SmallSeven

