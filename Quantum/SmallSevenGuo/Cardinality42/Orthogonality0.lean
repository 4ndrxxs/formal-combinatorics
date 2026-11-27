/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality42.Quotients0

/-!
# Orthogonality checks 0–48 for cardinality 42
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality42

theorem orth_0 : ∀ m : Fin 32, data.dotMask 0 1 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot0[m.val]?.getD [])) := by
  decide +kernel

theorem orth_1 : ∀ m : Fin 32, data.dotMask 0 2 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot1[m.val]?.getD [])) := by
  decide +kernel

theorem orth_2 : ∀ m : Fin 32, data.dotMask 0 3 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot2[m.val]?.getD [])) := by
  decide +kernel

theorem orth_3 : ∀ m : Fin 32, data.dotMask 0 4 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot3[m.val]?.getD [])) := by
  decide +kernel

theorem orth_4 : ∀ m : Fin 32, data.dotMask 0 5 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot4[m.val]?.getD [])) := by
  decide +kernel

theorem orth_5 : ∀ m : Fin 32, data.dotMask 0 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot5[m.val]?.getD [])) := by
  decide +kernel

theorem orth_6 : ∀ m : Fin 32, data.dotMask 1 2 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot6[m.val]?.getD [])) := by
  decide +kernel

theorem orth_7 : ∀ m : Fin 32, data.dotMask 1 3 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot7[m.val]?.getD [])) := by
  decide +kernel

theorem orth_8 : ∀ m : Fin 32, data.dotMask 1 4 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot8[m.val]?.getD [])) := by
  decide +kernel

theorem orth_9 : ∀ m : Fin 32, data.dotMask 1 5 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot9[m.val]?.getD [])) := by
  decide +kernel

theorem orth_10 : ∀ m : Fin 32, data.dotMask 1 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot10[m.val]?.getD [])) := by
  decide +kernel

theorem orth_11 : ∀ m : Fin 32, data.dotMask 2 3 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot11[m.val]?.getD [])) := by
  decide +kernel

theorem orth_12 : ∀ m : Fin 32, data.dotMask 2 4 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot12[m.val]?.getD [])) := by
  decide +kernel

theorem orth_13 : ∀ m : Fin 32, data.dotMask 2 5 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot13[m.val]?.getD [])) := by
  decide +kernel

theorem orth_14 : ∀ m : Fin 32, data.dotMask 2 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot14[m.val]?.getD [])) := by
  decide +kernel

theorem orth_15 : ∀ m : Fin 32, data.dotMask 3 4 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot15[m.val]?.getD [])) := by
  decide +kernel

theorem orth_16 : ∀ m : Fin 32, data.dotMask 3 5 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot16[m.val]?.getD [])) := by
  decide +kernel

theorem orth_17 : ∀ m : Fin 32, data.dotMask 3 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot17[m.val]?.getD [])) := by
  decide +kernel

theorem orth_18 : ∀ m : Fin 32, data.dotMask 4 5 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot18[m.val]?.getD [])) := by
  decide +kernel

theorem orth_19 : ∀ m : Fin 32, data.dotMask 4 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot19[m.val]?.getD [])) := by
  decide +kernel

theorem orth_20 : ∀ m : Fin 32, data.dotMask 5 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot20[m.val]?.getD [])) := by
  decide +kernel

theorem orth_21 : ∀ m : Fin 32, data.dotMask 7 8 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot21[m.val]?.getD [])) := by
  decide +kernel

theorem orth_22 : ∀ m : Fin 32, data.dotMask 7 9 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot22[m.val]?.getD [])) := by
  decide +kernel

theorem orth_23 : ∀ m : Fin 32, data.dotMask 7 10 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot23[m.val]?.getD [])) := by
  decide +kernel

theorem orth_24 : ∀ m : Fin 32, data.dotMask 7 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot24[m.val]?.getD [])) := by
  decide +kernel

theorem orth_25 : ∀ m : Fin 32, data.dotMask 7 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot25[m.val]?.getD [])) := by
  decide +kernel

theorem orth_26 : ∀ m : Fin 32, data.dotMask 7 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot26[m.val]?.getD [])) := by
  decide +kernel

theorem orth_27 : ∀ m : Fin 32, data.dotMask 8 9 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot27[m.val]?.getD [])) := by
  decide +kernel

theorem orth_28 : ∀ m : Fin 32, data.dotMask 8 10 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot28[m.val]?.getD [])) := by
  decide +kernel

theorem orth_29 : ∀ m : Fin 32, data.dotMask 8 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot29[m.val]?.getD [])) := by
  decide +kernel

theorem orth_30 : ∀ m : Fin 32, data.dotMask 8 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot30[m.val]?.getD [])) := by
  decide +kernel

theorem orth_31 : ∀ m : Fin 32, data.dotMask 8 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot31[m.val]?.getD [])) := by
  decide +kernel

theorem orth_32 : ∀ m : Fin 32, data.dotMask 9 10 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot32[m.val]?.getD [])) := by
  decide +kernel

theorem orth_33 : ∀ m : Fin 32, data.dotMask 9 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot33[m.val]?.getD [])) := by
  decide +kernel

theorem orth_34 : ∀ m : Fin 32, data.dotMask 9 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot34[m.val]?.getD [])) := by
  decide +kernel

theorem orth_35 : ∀ m : Fin 32, data.dotMask 9 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot35[m.val]?.getD [])) := by
  decide +kernel

theorem orth_36 : ∀ m : Fin 32, data.dotMask 10 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot36[m.val]?.getD [])) := by
  decide +kernel

theorem orth_37 : ∀ m : Fin 32, data.dotMask 10 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot37[m.val]?.getD [])) := by
  decide +kernel

theorem orth_38 : ∀ m : Fin 32, data.dotMask 10 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot38[m.val]?.getD [])) := by
  decide +kernel

theorem orth_39 : ∀ m : Fin 32, data.dotMask 11 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot39[m.val]?.getD [])) := by
  decide +kernel

theorem orth_40 : ∀ m : Fin 32, data.dotMask 11 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot40[m.val]?.getD [])) := by
  decide +kernel

theorem orth_41 : ∀ m : Fin 32, data.dotMask 12 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot41[m.val]?.getD [])) := by
  decide +kernel

theorem orth_42 : ∀ m : Fin 32, data.dotMask 14 15 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot42[m.val]?.getD [])) := by
  decide +kernel

theorem orth_43 : ∀ m : Fin 32, data.dotMask 14 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot43[m.val]?.getD [])) := by
  decide +kernel

theorem orth_44 : ∀ m : Fin 32, data.dotMask 14 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot44[m.val]?.getD [])) := by
  decide +kernel

theorem orth_45 : ∀ m : Fin 32, data.dotMask 14 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot45[m.val]?.getD [])) := by
  decide +kernel

theorem orth_46 : ∀ m : Fin 32, data.dotMask 14 19 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot46[m.val]?.getD [])) := by
  decide +kernel

theorem orth_47 : ∀ m : Fin 32, data.dotMask 14 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot47[m.val]?.getD [])) := by
  decide +kernel

theorem orth_48 : ∀ m : Fin 32, data.dotMask 15 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot48[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality42
