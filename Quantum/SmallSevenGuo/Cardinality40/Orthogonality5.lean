/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality40.Quotients5

/-!
# Orthogonality checks 245–293 for cardinality 40
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality40

theorem orth_245 : ∀ m : Fin 8, data.dotMask 17 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot245[m.val]?.getD [])) := by
  decide +kernel

theorem orth_246 : ∀ m : Fin 8, data.dotMask 24 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot246[m.val]?.getD [])) := by
  decide +kernel

theorem orth_247 : ∀ m : Fin 8, data.dotMask 24 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot247[m.val]?.getD [])) := by
  decide +kernel

theorem orth_248 : ∀ m : Fin 8, data.dotMask 24 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot248[m.val]?.getD [])) := by
  decide +kernel

theorem orth_249 : ∀ m : Fin 8, data.dotMask 30 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot249[m.val]?.getD [])) := by
  decide +kernel

theorem orth_250 : ∀ m : Fin 8, data.dotMask 30 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot250[m.val]?.getD [])) := by
  decide +kernel

theorem orth_251 : ∀ m : Fin 8, data.dotMask 36 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot251[m.val]?.getD [])) := by
  decide +kernel

theorem orth_252 : ∀ m : Fin 8, data.dotMask 5 11 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot252[m.val]?.getD [])) := by
  decide +kernel

theorem orth_253 : ∀ m : Fin 8, data.dotMask 5 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot253[m.val]?.getD [])) := by
  decide +kernel

theorem orth_254 : ∀ m : Fin 8, data.dotMask 5 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot254[m.val]?.getD [])) := by
  decide +kernel

theorem orth_255 : ∀ m : Fin 8, data.dotMask 5 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot255[m.val]?.getD [])) := by
  decide +kernel

theorem orth_256 : ∀ m : Fin 8, data.dotMask 5 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot256[m.val]?.getD [])) := by
  decide +kernel

theorem orth_257 : ∀ m : Fin 8, data.dotMask 5 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot257[m.val]?.getD [])) := by
  decide +kernel

theorem orth_258 : ∀ m : Fin 8, data.dotMask 11 18 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot258[m.val]?.getD [])) := by
  decide +kernel

theorem orth_259 : ∀ m : Fin 8, data.dotMask 11 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot259[m.val]?.getD [])) := by
  decide +kernel

theorem orth_260 : ∀ m : Fin 8, data.dotMask 11 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot260[m.val]?.getD [])) := by
  decide +kernel

theorem orth_261 : ∀ m : Fin 8, data.dotMask 11 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot261[m.val]?.getD [])) := by
  decide +kernel

theorem orth_262 : ∀ m : Fin 8, data.dotMask 11 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot262[m.val]?.getD [])) := by
  decide +kernel

theorem orth_263 : ∀ m : Fin 8, data.dotMask 18 25 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot263[m.val]?.getD [])) := by
  decide +kernel

theorem orth_264 : ∀ m : Fin 8, data.dotMask 18 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot264[m.val]?.getD [])) := by
  decide +kernel

theorem orth_265 : ∀ m : Fin 8, data.dotMask 18 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot265[m.val]?.getD [])) := by
  decide +kernel

theorem orth_266 : ∀ m : Fin 8, data.dotMask 18 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot266[m.val]?.getD [])) := by
  decide +kernel

theorem orth_267 : ∀ m : Fin 8, data.dotMask 25 31 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot267[m.val]?.getD [])) := by
  decide +kernel

theorem orth_268 : ∀ m : Fin 8, data.dotMask 25 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot268[m.val]?.getD [])) := by
  decide +kernel

theorem orth_269 : ∀ m : Fin 8, data.dotMask 25 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot269[m.val]?.getD [])) := by
  decide +kernel

theorem orth_270 : ∀ m : Fin 8, data.dotMask 31 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot270[m.val]?.getD [])) := by
  decide +kernel

theorem orth_271 : ∀ m : Fin 8, data.dotMask 31 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot271[m.val]?.getD [])) := by
  decide +kernel

theorem orth_272 : ∀ m : Fin 8, data.dotMask 37 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot272[m.val]?.getD [])) := by
  decide +kernel

theorem orth_273 : ∀ m : Fin 8, data.dotMask 6 12 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot273[m.val]?.getD [])) := by
  decide +kernel

theorem orth_274 : ∀ m : Fin 8, data.dotMask 6 19 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot274[m.val]?.getD [])) := by
  decide +kernel

theorem orth_275 : ∀ m : Fin 8, data.dotMask 6 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot275[m.val]?.getD [])) := by
  decide +kernel

theorem orth_276 : ∀ m : Fin 8, data.dotMask 6 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot276[m.val]?.getD [])) := by
  decide +kernel

theorem orth_277 : ∀ m : Fin 8, data.dotMask 6 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot277[m.val]?.getD [])) := by
  decide +kernel

theorem orth_278 : ∀ m : Fin 8, data.dotMask 6 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot278[m.val]?.getD [])) := by
  decide +kernel

theorem orth_279 : ∀ m : Fin 8, data.dotMask 12 19 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot279[m.val]?.getD [])) := by
  decide +kernel

theorem orth_280 : ∀ m : Fin 8, data.dotMask 12 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot280[m.val]?.getD [])) := by
  decide +kernel

theorem orth_281 : ∀ m : Fin 8, data.dotMask 12 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot281[m.val]?.getD [])) := by
  decide +kernel

theorem orth_282 : ∀ m : Fin 8, data.dotMask 12 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot282[m.val]?.getD [])) := by
  decide +kernel

theorem orth_283 : ∀ m : Fin 8, data.dotMask 12 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot283[m.val]?.getD [])) := by
  decide +kernel

theorem orth_284 : ∀ m : Fin 8, data.dotMask 19 26 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot284[m.val]?.getD [])) := by
  decide +kernel

theorem orth_285 : ∀ m : Fin 8, data.dotMask 19 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot285[m.val]?.getD [])) := by
  decide +kernel

theorem orth_286 : ∀ m : Fin 8, data.dotMask 19 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot286[m.val]?.getD [])) := by
  decide +kernel

theorem orth_287 : ∀ m : Fin 8, data.dotMask 19 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot287[m.val]?.getD [])) := by
  decide +kernel

theorem orth_288 : ∀ m : Fin 8, data.dotMask 26 32 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot288[m.val]?.getD [])) := by
  decide +kernel

theorem orth_289 : ∀ m : Fin 8, data.dotMask 26 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot289[m.val]?.getD [])) := by
  decide +kernel

theorem orth_290 : ∀ m : Fin 8, data.dotMask 26 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot290[m.val]?.getD [])) := by
  decide +kernel

theorem orth_291 : ∀ m : Fin 8, data.dotMask 32 38 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot291[m.val]?.getD [])) := by
  decide +kernel

theorem orth_292 : ∀ m : Fin 8, data.dotMask 32 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot292[m.val]?.getD [])) := by
  decide +kernel

theorem orth_293 : ∀ m : Fin 8, data.dotMask 38 39 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot293[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality40
