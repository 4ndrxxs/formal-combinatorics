/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality38.Quotients1

/-!
# Orthogonality checks 49–97 for cardinality 38
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality38

theorem orth_49 : ∀ m : Fin 8, data.dotMask 14 15 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot49[m.val]?.getD [])) := by
  decide +kernel

theorem orth_50 : ∀ m : Fin 8, data.dotMask 14 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot50[m.val]?.getD [])) := by
  decide +kernel

theorem orth_51 : ∀ m : Fin 8, data.dotMask 14 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot51[m.val]?.getD [])) := by
  decide +kernel

theorem orth_52 : ∀ m : Fin 8, data.dotMask 14 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot52[m.val]?.getD [])) := by
  decide +kernel

theorem orth_53 : ∀ m : Fin 8, data.dotMask 0 15 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot53[m.val]?.getD [])) := by
  decide +kernel

theorem orth_54 : ∀ m : Fin 8, data.dotMask 0 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot54[m.val]?.getD [])) := by
  decide +kernel

theorem orth_55 : ∀ m : Fin 8, data.dotMask 0 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot55[m.val]?.getD [])) := by
  decide +kernel

theorem orth_56 : ∀ m : Fin 8, data.dotMask 0 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot56[m.val]?.getD [])) := by
  decide +kernel

theorem orth_57 : ∀ m : Fin 8, data.dotMask 15 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot57[m.val]?.getD [])) := by
  decide +kernel

theorem orth_58 : ∀ m : Fin 8, data.dotMask 15 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot58[m.val]?.getD [])) := by
  decide +kernel

theorem orth_59 : ∀ m : Fin 8, data.dotMask 15 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot59[m.val]?.getD [])) := by
  decide +kernel

theorem orth_60 : ∀ m : Fin 8, data.dotMask 16 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot60[m.val]?.getD [])) := by
  decide +kernel

theorem orth_61 : ∀ m : Fin 8, data.dotMask 16 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot61[m.val]?.getD [])) := by
  decide +kernel

theorem orth_62 : ∀ m : Fin 8, data.dotMask 17 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot62[m.val]?.getD [])) := by
  decide +kernel

theorem orth_63 : ∀ m : Fin 8, data.dotMask 19 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot63[m.val]?.getD [])) := by
  decide +kernel

theorem orth_64 : ∀ m : Fin 8, data.dotMask 19 21 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot64[m.val]?.getD [])) := by
  decide +kernel

theorem orth_65 : ∀ m : Fin 8, data.dotMask 19 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot65[m.val]?.getD [])) := by
  decide +kernel

theorem orth_66 : ∀ m : Fin 8, data.dotMask 19 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot66[m.val]?.getD [])) := by
  decide +kernel

theorem orth_67 : ∀ m : Fin 8, data.dotMask 19 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot67[m.val]?.getD [])) := by
  decide +kernel

theorem orth_68 : ∀ m : Fin 8, data.dotMask 19 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot68[m.val]?.getD [])) := by
  decide +kernel

theorem orth_69 : ∀ m : Fin 8, data.dotMask 20 21 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot69[m.val]?.getD [])) := by
  decide +kernel

theorem orth_70 : ∀ m : Fin 8, data.dotMask 20 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot70[m.val]?.getD [])) := by
  decide +kernel

theorem orth_71 : ∀ m : Fin 8, data.dotMask 20 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot71[m.val]?.getD [])) := by
  decide +kernel

theorem orth_72 : ∀ m : Fin 8, data.dotMask 20 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot72[m.val]?.getD [])) := by
  decide +kernel

theorem orth_73 : ∀ m : Fin 8, data.dotMask 20 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot73[m.val]?.getD [])) := by
  decide +kernel

theorem orth_74 : ∀ m : Fin 8, data.dotMask 21 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot74[m.val]?.getD [])) := by
  decide +kernel

theorem orth_75 : ∀ m : Fin 8, data.dotMask 21 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot75[m.val]?.getD [])) := by
  decide +kernel

theorem orth_76 : ∀ m : Fin 8, data.dotMask 21 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot76[m.val]?.getD [])) := by
  decide +kernel

theorem orth_77 : ∀ m : Fin 8, data.dotMask 21 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot77[m.val]?.getD [])) := by
  decide +kernel

theorem orth_78 : ∀ m : Fin 8, data.dotMask 0 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot78[m.val]?.getD [])) := by
  decide +kernel

theorem orth_79 : ∀ m : Fin 8, data.dotMask 0 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot79[m.val]?.getD [])) := by
  decide +kernel

theorem orth_80 : ∀ m : Fin 8, data.dotMask 0 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot80[m.val]?.getD [])) := by
  decide +kernel

theorem orth_81 : ∀ m : Fin 8, data.dotMask 22 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot81[m.val]?.getD [])) := by
  decide +kernel

theorem orth_82 : ∀ m : Fin 8, data.dotMask 22 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot82[m.val]?.getD [])) := by
  decide +kernel

theorem orth_83 : ∀ m : Fin 8, data.dotMask 23 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot83[m.val]?.getD [])) := by
  decide +kernel

theorem orth_84 : ∀ m : Fin 8, data.dotMask 25 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot84[m.val]?.getD [])) := by
  decide +kernel

theorem orth_85 : ∀ m : Fin 8, data.dotMask 25 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot85[m.val]?.getD [])) := by
  decide +kernel

theorem orth_86 : ∀ m : Fin 8, data.dotMask 25 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot86[m.val]?.getD [])) := by
  decide +kernel

theorem orth_87 : ∀ m : Fin 8, data.dotMask 25 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot87[m.val]?.getD [])) := by
  decide +kernel

theorem orth_88 : ∀ m : Fin 8, data.dotMask 25 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot88[m.val]?.getD [])) := by
  decide +kernel

theorem orth_89 : ∀ m : Fin 8, data.dotMask 25 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot89[m.val]?.getD [])) := by
  decide +kernel

theorem orth_90 : ∀ m : Fin 8, data.dotMask 26 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot90[m.val]?.getD [])) := by
  decide +kernel

theorem orth_91 : ∀ m : Fin 8, data.dotMask 26 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot91[m.val]?.getD [])) := by
  decide +kernel

theorem orth_92 : ∀ m : Fin 8, data.dotMask 26 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot92[m.val]?.getD [])) := by
  decide +kernel

theorem orth_93 : ∀ m : Fin 8, data.dotMask 26 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot93[m.val]?.getD [])) := by
  decide +kernel

theorem orth_94 : ∀ m : Fin 8, data.dotMask 26 0 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot94[m.val]?.getD [])) := by
  decide +kernel

theorem orth_95 : ∀ m : Fin 8, data.dotMask 27 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot95[m.val]?.getD [])) := by
  decide +kernel

theorem orth_96 : ∀ m : Fin 8, data.dotMask 27 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot96[m.val]?.getD [])) := by
  decide +kernel

theorem orth_97 : ∀ m : Fin 8, data.dotMask 27 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot97[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality38
