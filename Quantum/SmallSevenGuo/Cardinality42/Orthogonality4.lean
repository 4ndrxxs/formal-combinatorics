/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality42.Quotients4

/-!
# Orthogonality checks 196–244 for cardinality 42
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality42

theorem orth_196 : ∀ m : Fin 32, data.dotMask 9 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot196[m.val]?.getD [])) := by
  decide +kernel

theorem orth_197 : ∀ m : Fin 32, data.dotMask 9 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot197[m.val]?.getD [])) := by
  decide +kernel

theorem orth_198 : ∀ m : Fin 32, data.dotMask 9 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot198[m.val]?.getD [])) := by
  decide +kernel

theorem orth_199 : ∀ m : Fin 32, data.dotMask 9 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot199[m.val]?.getD [])) := by
  decide +kernel

theorem orth_200 : ∀ m : Fin 32, data.dotMask 16 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot200[m.val]?.getD [])) := by
  decide +kernel

theorem orth_201 : ∀ m : Fin 32, data.dotMask 16 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot201[m.val]?.getD [])) := by
  decide +kernel

theorem orth_202 : ∀ m : Fin 32, data.dotMask 16 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot202[m.val]?.getD [])) := by
  decide +kernel

theorem orth_203 : ∀ m : Fin 32, data.dotMask 16 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot203[m.val]?.getD [])) := by
  decide +kernel

theorem orth_204 : ∀ m : Fin 32, data.dotMask 23 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot204[m.val]?.getD [])) := by
  decide +kernel

theorem orth_205 : ∀ m : Fin 32, data.dotMask 23 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot205[m.val]?.getD [])) := by
  decide +kernel

theorem orth_206 : ∀ m : Fin 32, data.dotMask 23 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot206[m.val]?.getD [])) := by
  decide +kernel

theorem orth_207 : ∀ m : Fin 32, data.dotMask 30 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot207[m.val]?.getD [])) := by
  decide +kernel

theorem orth_208 : ∀ m : Fin 32, data.dotMask 30 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot208[m.val]?.getD [])) := by
  decide +kernel

theorem orth_209 : ∀ m : Fin 32, data.dotMask 37 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot209[m.val]?.getD [])) := by
  decide +kernel

theorem orth_210 : ∀ m : Fin 32, data.dotMask 3 10 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot210[m.val]?.getD [])) := by
  decide +kernel

theorem orth_211 : ∀ m : Fin 32, data.dotMask 3 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot211[m.val]?.getD [])) := by
  decide +kernel

theorem orth_212 : ∀ m : Fin 32, data.dotMask 3 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot212[m.val]?.getD [])) := by
  decide +kernel

theorem orth_213 : ∀ m : Fin 32, data.dotMask 3 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot213[m.val]?.getD [])) := by
  decide +kernel

theorem orth_214 : ∀ m : Fin 32, data.dotMask 3 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot214[m.val]?.getD [])) := by
  decide +kernel

theorem orth_215 : ∀ m : Fin 32, data.dotMask 3 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot215[m.val]?.getD [])) := by
  decide +kernel

theorem orth_216 : ∀ m : Fin 32, data.dotMask 10 17 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot216[m.val]?.getD [])) := by
  decide +kernel

theorem orth_217 : ∀ m : Fin 32, data.dotMask 10 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot217[m.val]?.getD [])) := by
  decide +kernel

theorem orth_218 : ∀ m : Fin 32, data.dotMask 10 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot218[m.val]?.getD [])) := by
  decide +kernel

theorem orth_219 : ∀ m : Fin 32, data.dotMask 10 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot219[m.val]?.getD [])) := by
  decide +kernel

theorem orth_220 : ∀ m : Fin 32, data.dotMask 10 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot220[m.val]?.getD [])) := by
  decide +kernel

theorem orth_221 : ∀ m : Fin 32, data.dotMask 17 24 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot221[m.val]?.getD [])) := by
  decide +kernel

theorem orth_222 : ∀ m : Fin 32, data.dotMask 17 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot222[m.val]?.getD [])) := by
  decide +kernel

theorem orth_223 : ∀ m : Fin 32, data.dotMask 17 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot223[m.val]?.getD [])) := by
  decide +kernel

theorem orth_224 : ∀ m : Fin 32, data.dotMask 17 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot224[m.val]?.getD [])) := by
  decide +kernel

theorem orth_225 : ∀ m : Fin 32, data.dotMask 24 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot225[m.val]?.getD [])) := by
  decide +kernel

theorem orth_226 : ∀ m : Fin 32, data.dotMask 24 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot226[m.val]?.getD [])) := by
  decide +kernel

theorem orth_227 : ∀ m : Fin 32, data.dotMask 24 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot227[m.val]?.getD [])) := by
  decide +kernel

theorem orth_228 : ∀ m : Fin 32, data.dotMask 31 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot228[m.val]?.getD [])) := by
  decide +kernel

theorem orth_229 : ∀ m : Fin 32, data.dotMask 31 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot229[m.val]?.getD [])) := by
  decide +kernel

theorem orth_230 : ∀ m : Fin 32, data.dotMask 26 27 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot230[m.val]?.getD [])) := by
  decide +kernel

theorem orth_231 : ∀ m : Fin 32, data.dotMask 4 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot231[m.val]?.getD [])) := by
  decide +kernel

theorem orth_232 : ∀ m : Fin 32, data.dotMask 4 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot232[m.val]?.getD [])) := by
  decide +kernel

theorem orth_233 : ∀ m : Fin 32, data.dotMask 4 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot233[m.val]?.getD [])) := by
  decide +kernel

theorem orth_234 : ∀ m : Fin 32, data.dotMask 4 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot234[m.val]?.getD [])) := by
  decide +kernel

theorem orth_235 : ∀ m : Fin 32, data.dotMask 4 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot235[m.val]?.getD [])) := by
  decide +kernel

theorem orth_236 : ∀ m : Fin 32, data.dotMask 4 34 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot236[m.val]?.getD [])) := by
  decide +kernel

theorem orth_237 : ∀ m : Fin 32, data.dotMask 11 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot237[m.val]?.getD [])) := by
  decide +kernel

theorem orth_238 : ∀ m : Fin 32, data.dotMask 11 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot238[m.val]?.getD [])) := by
  decide +kernel

theorem orth_239 : ∀ m : Fin 32, data.dotMask 11 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot239[m.val]?.getD [])) := by
  decide +kernel

theorem orth_240 : ∀ m : Fin 32, data.dotMask 11 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot240[m.val]?.getD [])) := by
  decide +kernel

theorem orth_241 : ∀ m : Fin 32, data.dotMask 11 34 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot241[m.val]?.getD [])) := by
  decide +kernel

theorem orth_242 : ∀ m : Fin 32, data.dotMask 18 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot242[m.val]?.getD [])) := by
  decide +kernel

theorem orth_243 : ∀ m : Fin 32, data.dotMask 18 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot243[m.val]?.getD [])) := by
  decide +kernel

theorem orth_244 : ∀ m : Fin 32, data.dotMask 18 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot244[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality42
