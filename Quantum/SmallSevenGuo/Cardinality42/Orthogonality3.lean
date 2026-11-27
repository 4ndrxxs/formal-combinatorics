/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality42.Quotients3

/-!
# Orthogonality checks 147–195 for cardinality 42
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality42

theorem orth_147 : ∀ m : Fin 32, data.dotMask 0 7 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot147[m.val]?.getD [])) := by
  decide +kernel

theorem orth_148 : ∀ m : Fin 32, data.dotMask 0 14 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot148[m.val]?.getD [])) := by
  decide +kernel

theorem orth_149 : ∀ m : Fin 32, data.dotMask 0 21 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot149[m.val]?.getD [])) := by
  decide +kernel

theorem orth_150 : ∀ m : Fin 32, data.dotMask 0 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot150[m.val]?.getD [])) := by
  decide +kernel

theorem orth_151 : ∀ m : Fin 32, data.dotMask 0 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot151[m.val]?.getD [])) := by
  decide +kernel

theorem orth_152 : ∀ m : Fin 32, data.dotMask 0 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot152[m.val]?.getD [])) := by
  decide +kernel

theorem orth_153 : ∀ m : Fin 32, data.dotMask 7 14 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot153[m.val]?.getD [])) := by
  decide +kernel

theorem orth_154 : ∀ m : Fin 32, data.dotMask 7 21 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot154[m.val]?.getD [])) := by
  decide +kernel

theorem orth_155 : ∀ m : Fin 32, data.dotMask 7 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot155[m.val]?.getD [])) := by
  decide +kernel

theorem orth_156 : ∀ m : Fin 32, data.dotMask 7 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot156[m.val]?.getD [])) := by
  decide +kernel

theorem orth_157 : ∀ m : Fin 32, data.dotMask 7 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot157[m.val]?.getD [])) := by
  decide +kernel

theorem orth_158 : ∀ m : Fin 32, data.dotMask 14 21 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot158[m.val]?.getD [])) := by
  decide +kernel

theorem orth_159 : ∀ m : Fin 32, data.dotMask 14 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot159[m.val]?.getD [])) := by
  decide +kernel

theorem orth_160 : ∀ m : Fin 32, data.dotMask 14 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot160[m.val]?.getD [])) := by
  decide +kernel

theorem orth_161 : ∀ m : Fin 32, data.dotMask 14 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot161[m.val]?.getD [])) := by
  decide +kernel

theorem orth_162 : ∀ m : Fin 32, data.dotMask 21 28 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot162[m.val]?.getD [])) := by
  decide +kernel

theorem orth_163 : ∀ m : Fin 32, data.dotMask 21 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot163[m.val]?.getD [])) := by
  decide +kernel

theorem orth_164 : ∀ m : Fin 32, data.dotMask 21 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot164[m.val]?.getD [])) := by
  decide +kernel

theorem orth_165 : ∀ m : Fin 32, data.dotMask 28 35 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot165[m.val]?.getD [])) := by
  decide +kernel

theorem orth_166 : ∀ m : Fin 32, data.dotMask 28 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot166[m.val]?.getD [])) := by
  decide +kernel

theorem orth_167 : ∀ m : Fin 32, data.dotMask 35 6 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot167[m.val]?.getD [])) := by
  decide +kernel

theorem orth_168 : ∀ m : Fin 32, data.dotMask 1 8 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot168[m.val]?.getD [])) := by
  decide +kernel

theorem orth_169 : ∀ m : Fin 32, data.dotMask 1 15 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot169[m.val]?.getD [])) := by
  decide +kernel

theorem orth_170 : ∀ m : Fin 32, data.dotMask 1 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot170[m.val]?.getD [])) := by
  decide +kernel

theorem orth_171 : ∀ m : Fin 32, data.dotMask 1 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot171[m.val]?.getD [])) := by
  decide +kernel

theorem orth_172 : ∀ m : Fin 32, data.dotMask 1 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot172[m.val]?.getD [])) := by
  decide +kernel

theorem orth_173 : ∀ m : Fin 32, data.dotMask 1 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot173[m.val]?.getD [])) := by
  decide +kernel

theorem orth_174 : ∀ m : Fin 32, data.dotMask 8 15 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot174[m.val]?.getD [])) := by
  decide +kernel

theorem orth_175 : ∀ m : Fin 32, data.dotMask 8 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot175[m.val]?.getD [])) := by
  decide +kernel

theorem orth_176 : ∀ m : Fin 32, data.dotMask 8 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot176[m.val]?.getD [])) := by
  decide +kernel

theorem orth_177 : ∀ m : Fin 32, data.dotMask 8 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot177[m.val]?.getD [])) := by
  decide +kernel

theorem orth_178 : ∀ m : Fin 32, data.dotMask 8 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot178[m.val]?.getD [])) := by
  decide +kernel

theorem orth_179 : ∀ m : Fin 32, data.dotMask 15 22 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot179[m.val]?.getD [])) := by
  decide +kernel

theorem orth_180 : ∀ m : Fin 32, data.dotMask 15 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot180[m.val]?.getD [])) := by
  decide +kernel

theorem orth_181 : ∀ m : Fin 32, data.dotMask 15 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot181[m.val]?.getD [])) := by
  decide +kernel

theorem orth_182 : ∀ m : Fin 32, data.dotMask 15 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot182[m.val]?.getD [])) := by
  decide +kernel

theorem orth_183 : ∀ m : Fin 32, data.dotMask 22 29 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot183[m.val]?.getD [])) := by
  decide +kernel

theorem orth_184 : ∀ m : Fin 32, data.dotMask 22 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot184[m.val]?.getD [])) := by
  decide +kernel

theorem orth_185 : ∀ m : Fin 32, data.dotMask 22 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot185[m.val]?.getD [])) := by
  decide +kernel

theorem orth_186 : ∀ m : Fin 32, data.dotMask 29 36 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot186[m.val]?.getD [])) := by
  decide +kernel

theorem orth_187 : ∀ m : Fin 32, data.dotMask 29 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot187[m.val]?.getD [])) := by
  decide +kernel

theorem orth_188 : ∀ m : Fin 32, data.dotMask 36 13 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot188[m.val]?.getD [])) := by
  decide +kernel

theorem orth_189 : ∀ m : Fin 32, data.dotMask 2 9 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot189[m.val]?.getD [])) := by
  decide +kernel

theorem orth_190 : ∀ m : Fin 32, data.dotMask 2 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot190[m.val]?.getD [])) := by
  decide +kernel

theorem orth_191 : ∀ m : Fin 32, data.dotMask 2 23 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot191[m.val]?.getD [])) := by
  decide +kernel

theorem orth_192 : ∀ m : Fin 32, data.dotMask 2 30 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot192[m.val]?.getD [])) := by
  decide +kernel

theorem orth_193 : ∀ m : Fin 32, data.dotMask 2 37 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot193[m.val]?.getD [])) := by
  decide +kernel

theorem orth_194 : ∀ m : Fin 32, data.dotMask 2 20 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot194[m.val]?.getD [])) := by
  decide +kernel

theorem orth_195 : ∀ m : Fin 32, data.dotMask 9 16 m.val =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial (quot195[m.val]?.getD [])) := by
  decide +kernel

end QLS7.Cardinality42
