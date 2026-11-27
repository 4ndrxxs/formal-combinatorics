/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality0
public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality1
public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality2
public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality3
public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality4
public import Quantum.SmallSevenGuo.Cardinality40.Orthogonality5
public import Quantum.SmallSevenGuo.Certificate.PolynomialSoundness

/-!
# Orthogonality identities for cardinality 40
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality40

def quotients : List (List IntPolynomial) :=
  [quot0, quot1, quot2, quot3, quot4, quot5, quot6, quot7, quot8, quot9,
   quot10, quot11, quot12, quot13, quot14, quot15, quot16, quot17, quot18, quot19,
   quot20, quot21, quot22, quot23, quot24, quot25, quot26, quot27, quot28, quot29,
   quot30, quot31, quot32, quot33, quot34, quot35, quot36, quot37, quot38, quot39,
   quot40, quot41, quot42, quot43, quot44, quot45, quot46, quot47, quot48, quot49,
   quot50, quot51, quot52, quot53, quot54, quot55, quot56, quot57, quot58, quot59,
   quot60, quot61, quot62, quot63, quot64, quot65, quot66, quot67, quot68, quot69,
   quot70, quot71, quot72, quot73, quot74, quot75, quot76, quot77, quot78, quot79,
   quot80, quot81, quot82, quot83, quot84, quot85, quot86, quot87, quot88, quot89,
   quot90, quot91, quot92, quot93, quot94, quot95, quot96, quot97, quot98, quot99,
   quot100, quot101, quot102, quot103, quot104, quot105, quot106, quot107, quot108, quot109,
   quot110, quot111, quot112, quot113, quot114, quot115, quot116, quot117, quot118, quot119,
   quot120, quot121, quot122, quot123, quot124, quot125, quot126, quot127, quot128, quot129,
   quot130, quot131, quot132, quot133, quot134, quot135, quot136, quot137, quot138, quot139,
   quot140, quot141, quot142, quot143, quot144, quot145, quot146, quot147, quot148, quot149,
   quot150, quot151, quot152, quot153, quot154, quot155, quot156, quot157, quot158, quot159,
   quot160, quot161, quot162, quot163, quot164, quot165, quot166, quot167, quot168, quot169,
   quot170, quot171, quot172, quot173, quot174, quot175, quot176, quot177, quot178, quot179,
   quot180, quot181, quot182, quot183, quot184, quot185, quot186, quot187, quot188, quot189,
   quot190, quot191, quot192, quot193, quot194, quot195, quot196, quot197, quot198, quot199,
   quot200, quot201, quot202, quot203, quot204, quot205, quot206, quot207, quot208, quot209,
   quot210, quot211, quot212, quot213, quot214, quot215, quot216, quot217, quot218, quot219,
   quot220, quot221, quot222, quot223, quot224, quot225, quot226, quot227, quot228, quot229,
   quot230, quot231, quot232, quot233, quot234, quot235, quot236, quot237, quot238, quot239,
   quot240, quot241, quot242, quot243, quot244, quot245, quot246, quot247, quot248, quot249,
   quot250, quot251, quot252, quot253, quot254, quot255, quot256, quot257, quot258, quot259,
   quot260, quot261, quot262, quot263, quot264, quot265, quot266, quot267, quot268, quot269,
   quot270, quot271, quot272, quot273, quot274, quot275, quot276, quot277, quot278, quot279,
   quot280, quot281, quot282, quot283, quot284, quot285, quot286, quot287, quot288, quot289,
   quot290, quot291, quot292, quot293]

theorem orthogonal_pair (t : Fin 294) (m : Fin 8) :
    data.dotMask (certifiedPairs[t.val]?.getD (0, 0)).1
      (certifiedPairs[t.val]?.getD (0, 0)).2 m =
    IntPolynomial.trim (IntPolynomial.mul basePolynomial
      ((quotients[t.val]?.getD [])[m.val]?.getD [])) := by
  fin_cases t
  · exact orth_0 m
  · exact orth_1 m
  · exact orth_2 m
  · exact orth_3 m
  · exact orth_4 m
  · exact orth_5 m
  · exact orth_6 m
  · exact orth_7 m
  · exact orth_8 m
  · exact orth_9 m
  · exact orth_10 m
  · exact orth_11 m
  · exact orth_12 m
  · exact orth_13 m
  · exact orth_14 m
  · exact orth_15 m
  · exact orth_16 m
  · exact orth_17 m
  · exact orth_18 m
  · exact orth_19 m
  · exact orth_20 m
  · exact orth_21 m
  · exact orth_22 m
  · exact orth_23 m
  · exact orth_24 m
  · exact orth_25 m
  · exact orth_26 m
  · exact orth_27 m
  · exact orth_28 m
  · exact orth_29 m
  · exact orth_30 m
  · exact orth_31 m
  · exact orth_32 m
  · exact orth_33 m
  · exact orth_34 m
  · exact orth_35 m
  · exact orth_36 m
  · exact orth_37 m
  · exact orth_38 m
  · exact orth_39 m
  · exact orth_40 m
  · exact orth_41 m
  · exact orth_42 m
  · exact orth_43 m
  · exact orth_44 m
  · exact orth_45 m
  · exact orth_46 m
  · exact orth_47 m
  · exact orth_48 m
  · exact orth_49 m
  · exact orth_50 m
  · exact orth_51 m
  · exact orth_52 m
  · exact orth_53 m
  · exact orth_54 m
  · exact orth_55 m
  · exact orth_56 m
  · exact orth_57 m
  · exact orth_58 m
  · exact orth_59 m
  · exact orth_60 m
  · exact orth_61 m
  · exact orth_62 m
  · exact orth_63 m
  · exact orth_64 m
  · exact orth_65 m
  · exact orth_66 m
  · exact orth_67 m
  · exact orth_68 m
  · exact orth_69 m
  · exact orth_70 m
  · exact orth_71 m
  · exact orth_72 m
  · exact orth_73 m
  · exact orth_74 m
  · exact orth_75 m
  · exact orth_76 m
  · exact orth_77 m
  · exact orth_78 m
  · exact orth_79 m
  · exact orth_80 m
  · exact orth_81 m
  · exact orth_82 m
  · exact orth_83 m
  · exact orth_84 m
  · exact orth_85 m
  · exact orth_86 m
  · exact orth_87 m
  · exact orth_88 m
  · exact orth_89 m
  · exact orth_90 m
  · exact orth_91 m
  · exact orth_92 m
  · exact orth_93 m
  · exact orth_94 m
  · exact orth_95 m
  · exact orth_96 m
  · exact orth_97 m
  · exact orth_98 m
  · exact orth_99 m
  · exact orth_100 m
  · exact orth_101 m
  · exact orth_102 m
  · exact orth_103 m
  · exact orth_104 m
  · exact orth_105 m
  · exact orth_106 m
  · exact orth_107 m
  · exact orth_108 m
  · exact orth_109 m
  · exact orth_110 m
  · exact orth_111 m
  · exact orth_112 m
  · exact orth_113 m
  · exact orth_114 m
  · exact orth_115 m
  · exact orth_116 m
  · exact orth_117 m
  · exact orth_118 m
  · exact orth_119 m
  · exact orth_120 m
  · exact orth_121 m
  · exact orth_122 m
  · exact orth_123 m
  · exact orth_124 m
  · exact orth_125 m
  · exact orth_126 m
  · exact orth_127 m
  · exact orth_128 m
  · exact orth_129 m
  · exact orth_130 m
  · exact orth_131 m
  · exact orth_132 m
  · exact orth_133 m
  · exact orth_134 m
  · exact orth_135 m
  · exact orth_136 m
  · exact orth_137 m
  · exact orth_138 m
  · exact orth_139 m
  · exact orth_140 m
  · exact orth_141 m
  · exact orth_142 m
  · exact orth_143 m
  · exact orth_144 m
  · exact orth_145 m
  · exact orth_146 m
  · exact orth_147 m
  · exact orth_148 m
  · exact orth_149 m
  · exact orth_150 m
  · exact orth_151 m
  · exact orth_152 m
  · exact orth_153 m
  · exact orth_154 m
  · exact orth_155 m
  · exact orth_156 m
  · exact orth_157 m
  · exact orth_158 m
  · exact orth_159 m
  · exact orth_160 m
  · exact orth_161 m
  · exact orth_162 m
  · exact orth_163 m
  · exact orth_164 m
  · exact orth_165 m
  · exact orth_166 m
  · exact orth_167 m
  · exact orth_168 m
  · exact orth_169 m
  · exact orth_170 m
  · exact orth_171 m
  · exact orth_172 m
  · exact orth_173 m
  · exact orth_174 m
  · exact orth_175 m
  · exact orth_176 m
  · exact orth_177 m
  · exact orth_178 m
  · exact orth_179 m
  · exact orth_180 m
  · exact orth_181 m
  · exact orth_182 m
  · exact orth_183 m
  · exact orth_184 m
  · exact orth_185 m
  · exact orth_186 m
  · exact orth_187 m
  · exact orth_188 m
  · exact orth_189 m
  · exact orth_190 m
  · exact orth_191 m
  · exact orth_192 m
  · exact orth_193 m
  · exact orth_194 m
  · exact orth_195 m
  · exact orth_196 m
  · exact orth_197 m
  · exact orth_198 m
  · exact orth_199 m
  · exact orth_200 m
  · exact orth_201 m
  · exact orth_202 m
  · exact orth_203 m
  · exact orth_204 m
  · exact orth_205 m
  · exact orth_206 m
  · exact orth_207 m
  · exact orth_208 m
  · exact orth_209 m
  · exact orth_210 m
  · exact orth_211 m
  · exact orth_212 m
  · exact orth_213 m
  · exact orth_214 m
  · exact orth_215 m
  · exact orth_216 m
  · exact orth_217 m
  · exact orth_218 m
  · exact orth_219 m
  · exact orth_220 m
  · exact orth_221 m
  · exact orth_222 m
  · exact orth_223 m
  · exact orth_224 m
  · exact orth_225 m
  · exact orth_226 m
  · exact orth_227 m
  · exact orth_228 m
  · exact orth_229 m
  · exact orth_230 m
  · exact orth_231 m
  · exact orth_232 m
  · exact orth_233 m
  · exact orth_234 m
  · exact orth_235 m
  · exact orth_236 m
  · exact orth_237 m
  · exact orth_238 m
  · exact orth_239 m
  · exact orth_240 m
  · exact orth_241 m
  · exact orth_242 m
  · exact orth_243 m
  · exact orth_244 m
  · exact orth_245 m
  · exact orth_246 m
  · exact orth_247 m
  · exact orth_248 m
  · exact orth_249 m
  · exact orth_250 m
  · exact orth_251 m
  · exact orth_252 m
  · exact orth_253 m
  · exact orth_254 m
  · exact orth_255 m
  · exact orth_256 m
  · exact orth_257 m
  · exact orth_258 m
  · exact orth_259 m
  · exact orth_260 m
  · exact orth_261 m
  · exact orth_262 m
  · exact orth_263 m
  · exact orth_264 m
  · exact orth_265 m
  · exact orth_266 m
  · exact orth_267 m
  · exact orth_268 m
  · exact orth_269 m
  · exact orth_270 m
  · exact orth_271 m
  · exact orth_272 m
  · exact orth_273 m
  · exact orth_274 m
  · exact orth_275 m
  · exact orth_276 m
  · exact orth_277 m
  · exact orth_278 m
  · exact orth_279 m
  · exact orth_280 m
  · exact orth_281 m
  · exact orth_282 m
  · exact orth_283 m
  · exact orth_284 m
  · exact orth_285 m
  · exact orth_286 m
  · exact orth_287 m
  · exact orth_288 m
  · exact orth_289 m
  · exact orth_290 m
  · exact orth_291 m
  · exact orth_292 m
  · exact orth_293 m

theorem eval_dotMask_pair (x : ℝ) (hx : IntPolynomial.eval basePolynomial x = 0)
    (t : Fin 294) (m : Fin 8) :
    IntPolynomial.eval (data.dotMask (certifiedPairs[t.val]?.getD (0, 0)).1
      (certifiedPairs[t.val]?.getD (0, 0)).2 m) x = 0 := by
  rw [orthogonal_pair, IntPolynomial.eval_trim, IntPolynomial.eval_mul, hx, zero_mul]

def pairIndex (i j k : ℕ) : ℕ := 21 * i + j * (13 - j) / 2 + (k - j - 1)

theorem row_pair_index : ∀ i j k : Fin 7, j < k →
    pairIndex i j k < 294 ∧
    certifiedPairs[pairIndex i j k]?.getD (0, 0) = (data.label i j, data.label i k) := by
  decide +kernel

theorem column_pair_index : ∀ j i k : Fin 7, i < k →
    147 + pairIndex j i k < 294 ∧
    certifiedPairs[147 + pairIndex j i k]?.getD (0, 0) = (data.label i j, data.label k j) := by
  decide +kernel

theorem row_dot_zero (x : ℝ) (hx : IntPolynomial.eval basePolynomial x = 0)
    (i j k : Fin 7) (hjk : j < k) (m : Fin 8) :
    IntPolynomial.eval (data.dotMask (data.label i j) (data.label i k) m) x = 0 := by
  obtain ⟨ht, hp⟩ := row_pair_index i j k hjk
  have h := eval_dotMask_pair x hx ⟨pairIndex i j k, ht⟩ m
  simpa only [hp] using h

theorem column_dot_zero (x : ℝ) (hx : IntPolynomial.eval basePolynomial x = 0)
    (j i k : Fin 7) (hik : i < k) (m : Fin 8) :
    IntPolynomial.eval (data.dotMask (data.label i j) (data.label k j) m) x = 0 := by
  obtain ⟨ht, hp⟩ := column_pair_index j i k hik
  have h := eval_dotMask_pair x hx ⟨147 + pairIndex j i k, ht⟩ m
  simpa only [hp] using h

end QLS7.Cardinality40
