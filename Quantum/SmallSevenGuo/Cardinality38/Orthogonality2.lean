/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality38.Quotients2

/-!
# Orthogonality checks 98–146 for cardinality 38
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality38

theorem orth_98 : ∀ m : Fin 8, data.dotMask 27 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot98[m.val]?.getD [])) := by
  decide +kernel

theorem orth_99 : ∀ m : Fin 8, data.dotMask 28 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot99[m.val]?.getD [])) := by
  decide +kernel

theorem orth_100 : ∀ m : Fin 8, data.dotMask 28 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot100[m.val]?.getD [])) := by
  decide +kernel

theorem orth_101 : ∀ m : Fin 8, data.dotMask 28 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot101[m.val]?.getD [])) := by
  decide +kernel

theorem orth_102 : ∀ m : Fin 8, data.dotMask 29 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot102[m.val]?.getD [])) := by
  decide +kernel

theorem orth_103 : ∀ m : Fin 8, data.dotMask 29 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot103[m.val]?.getD [])) := by
  decide +kernel

theorem orth_104 : ∀ m : Fin 8, data.dotMask 30 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot104[m.val]?.getD [])) := by
  decide +kernel

theorem orth_105 : ∀ m : Fin 8, data.dotMask 31 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot105[m.val]?.getD [])) := by
  decide +kernel

theorem orth_106 : ∀ m : Fin 8, data.dotMask 31 33 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot106[m.val]?.getD [])) := by
  decide +kernel

theorem orth_107 : ∀ m : Fin 8, data.dotMask 31 34 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot107[m.val]?.getD [])) := by
  decide +kernel

theorem orth_108 : ∀ m : Fin 8, data.dotMask 31 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot108[m.val]?.getD [])) := by
  decide +kernel

theorem orth_109 : ∀ m : Fin 8, data.dotMask 31 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot109[m.val]?.getD [])) := by
  decide +kernel

theorem orth_110 : ∀ m : Fin 8, data.dotMask 31 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot110[m.val]?.getD [])) := by
  decide +kernel

theorem orth_111 : ∀ m : Fin 8, data.dotMask 32 33 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot111[m.val]?.getD [])) := by
  decide +kernel

theorem orth_112 : ∀ m : Fin 8, data.dotMask 32 34 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot112[m.val]?.getD [])) := by
  decide +kernel

theorem orth_113 : ∀ m : Fin 8, data.dotMask 32 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot113[m.val]?.getD [])) := by
  decide +kernel

theorem orth_114 : ∀ m : Fin 8, data.dotMask 32 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot114[m.val]?.getD [])) := by
  decide +kernel

theorem orth_115 : ∀ m : Fin 8, data.dotMask 32 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot115[m.val]?.getD [])) := by
  decide +kernel

theorem orth_116 : ∀ m : Fin 8, data.dotMask 33 34 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot116[m.val]?.getD [])) := by
  decide +kernel

theorem orth_117 : ∀ m : Fin 8, data.dotMask 33 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot117[m.val]?.getD [])) := by
  decide +kernel

theorem orth_118 : ∀ m : Fin 8, data.dotMask 33 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot118[m.val]?.getD [])) := by
  decide +kernel

theorem orth_119 : ∀ m : Fin 8, data.dotMask 33 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot119[m.val]?.getD [])) := by
  decide +kernel

theorem orth_120 : ∀ m : Fin 8, data.dotMask 34 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot120[m.val]?.getD [])) := by
  decide +kernel

theorem orth_121 : ∀ m : Fin 8, data.dotMask 34 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot121[m.val]?.getD [])) := by
  decide +kernel

theorem orth_122 : ∀ m : Fin 8, data.dotMask 34 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot122[m.val]?.getD [])) := by
  decide +kernel

theorem orth_123 : ∀ m : Fin 8, data.dotMask 35 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot123[m.val]?.getD [])) := by
  decide +kernel

theorem orth_124 : ∀ m : Fin 8, data.dotMask 35 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot124[m.val]?.getD [])) := by
  decide +kernel

theorem orth_125 : ∀ m : Fin 8, data.dotMask 0 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot125[m.val]?.getD [])) := by
  decide +kernel

theorem orth_126 : ∀ m : Fin 8, data.dotMask 6 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot126[m.val]?.getD [])) := by
  decide +kernel

theorem orth_127 : ∀ m : Fin 8, data.dotMask 6 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot127[m.val]?.getD [])) := by
  decide +kernel

theorem orth_128 : ∀ m : Fin 8, data.dotMask 6 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot128[m.val]?.getD [])) := by
  decide +kernel

theorem orth_129 : ∀ m : Fin 8, data.dotMask 6 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot129[m.val]?.getD [])) := by
  decide +kernel

theorem orth_130 : ∀ m : Fin 8, data.dotMask 6 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot130[m.val]?.getD [])) := by
  decide +kernel

theorem orth_131 : ∀ m : Fin 8, data.dotMask 6 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot131[m.val]?.getD [])) := by
  decide +kernel

theorem orth_132 : ∀ m : Fin 8, data.dotMask 12 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot132[m.val]?.getD [])) := by
  decide +kernel

theorem orth_133 : ∀ m : Fin 8, data.dotMask 12 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot133[m.val]?.getD [])) := by
  decide +kernel

theorem orth_134 : ∀ m : Fin 8, data.dotMask 12 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot134[m.val]?.getD [])) := by
  decide +kernel

theorem orth_135 : ∀ m : Fin 8, data.dotMask 12 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot135[m.val]?.getD [])) := by
  decide +kernel

theorem orth_136 : ∀ m : Fin 8, data.dotMask 12 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot136[m.val]?.getD [])) := by
  decide +kernel

theorem orth_137 : ∀ m : Fin 8, data.dotMask 18 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot137[m.val]?.getD [])) := by
  decide +kernel

theorem orth_138 : ∀ m : Fin 8, data.dotMask 18 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot138[m.val]?.getD [])) := by
  decide +kernel

theorem orth_139 : ∀ m : Fin 8, data.dotMask 18 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot139[m.val]?.getD [])) := by
  decide +kernel

theorem orth_140 : ∀ m : Fin 8, data.dotMask 18 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot140[m.val]?.getD [])) := by
  decide +kernel

theorem orth_141 : ∀ m : Fin 8, data.dotMask 24 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot141[m.val]?.getD [])) := by
  decide +kernel

theorem orth_142 : ∀ m : Fin 8, data.dotMask 24 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot142[m.val]?.getD [])) := by
  decide +kernel

theorem orth_143 : ∀ m : Fin 8, data.dotMask 24 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot143[m.val]?.getD [])) := by
  decide +kernel

theorem orth_144 : ∀ m : Fin 8, data.dotMask 0 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot144[m.val]?.getD [])) := by
  decide +kernel

theorem orth_145 : ∀ m : Fin 8, data.dotMask 0 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot145[m.val]?.getD [])) := by
  decide +kernel

theorem orth_146 : ∀ m : Fin 8, data.dotMask 36 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot146[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality38
