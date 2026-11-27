/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Cardinality40.Data

/-!
# Orthogonality quotients 49–97 for cardinality 40
-/

@[expose] public section
set_option maxHeartbeats 0

namespace QLS7.Cardinality40

def quot49 : List IntPolynomial :=
  [[-612, 3528, -5952, -4344, 4896, 1248, -1224, -96, 96], [], [], [], [], [], [], []]

def quot50 : List IntPolynomial :=
  [[144, 54, -36], [], [], [], [], [], [], []]

def quot51 : List IntPolynomial :=
  [[252, -288, -3588, 840, 2616, -288, -624, 24, 48], [], [], [], [], [], [], []]

def quot52 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot53 : List IntPolynomial :=
  [[108, 1620, 216, -432], [], [], [], [], [], [], []]

def quot54 : List IntPolynomial :=
  [[108], [], [], [], [], [], [], []]

def quot55 : List IntPolynomial :=
  [[108, 324, -108, -108], [], [], [], [], [], [], []]

def quot56 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot57 : List IntPolynomial :=
  [[288, -738, -702, 486, 144, -72], [], [], [], [], [], [], []]

def quot58 : List IntPolynomial :=
  [[-1332, 11088, -8100, -4752, 6552, 468, -1692, 0, 144], [], [], [], [], [], [], []]

def quot59 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot60 : List IntPolynomial :=
  [[180, 540, -54, -306, -18, 36], [], [], [], [], [], [], []]

def quot61 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot62 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot63 : List IntPolynomial :=
  [[], [-108, 1476, 252, -684, -36, 72], [], [], [], [], [], []]

def quot64 : List IntPolynomial :=
  [[], [1296, -2628, -720, 1116, 144, -144], [], [], [], [], [], []]

def quot65 : List IntPolynomial :=
  [[], [-2160, 3996, 1620, -1728, -324, 216], [], [], [], [], [], []]

def quot66 : List IntPolynomial :=
  [[], [-54, -180, 18, 36], [], [], [], [], [], []]

def quot67 : List IntPolynomial :=
  [[], [-432, 4788, 270, -2358, -36, 288], [], [], [], [], [], []]

def quot68 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot69 : List IntPolynomial :=
  [[3348, -17496, 8280, 9540, -7344, -1872, 1836, 144, -144], [], [], [], [], [], [], []]

def quot70 : List IntPolynomial :=
  [[-3348, 25704, -15444, -16308, 11880, 3780, -2808, -324, 216], [], [], [], [], [], [], []]

def quot71 : List IntPolynomial :=
  [[-270, 540, 900, -198, -360, 18, 36], [], [], [], [], [], [], []]

def quot72 : List IntPolynomial :=
  [[2160, -1944, -23238, 1080, 16254, 18, -3798, -36, 288], [], [], [], [], [], [], []]

def quot73 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot74 : List IntPolynomial :=
  [[-6372, 7344, 5184, 26028, -12204, -10692, 4644, 864, -432], [], [], [], [], [], [], []]

def quot75 : List IntPolynomial :=
  [[-72, 1224, -1350, -306, 630, 0, -72], [], [], [], [], [], [], []]

def quot76 : List IntPolynomial :=
  [[3348, -13896, 26658, 19116, -24336, -5454, 6696, 360, -576], [], [], [], [], [], [], []]

def quot77 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot78 : List IntPolynomial :=
  [[540, -3132, 2268, 1026, -1026, -54, 108], [], [], [], [], [], [], []]

def quot79 : List IntPolynomial :=
  [[-5292, 24192, -43902, -38502, 38934, 12204, -10422, -972, 864], [], [], [], [], [], [], []]

def quot80 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot81 : List IntPolynomial :=
  [[-270, 558, 2529, -612, -1197, 126, 144], [], [], [], [], [], [], []]

def quot82 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot83 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot84 : List IntPolynomial :=
  [[], [], [], [-324, -1080, 54, 396, 0, -36], [], [], [], []]

def quot85 : List IntPolynomial :=
  [[], [-144, -54, 36], [], [], [], [], [], []]

def quot86 : List IntPolynomial :=
  [[], [-36, 360, 600, -132, -240, 12, 24], [], [], [], [], [], []]

def quot87 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot88 : List IntPolynomial :=
  [[], [-144, 108, -2400, -900, 1560, 360, -336, -36, 24], [], [], [], [], [], []]

def quot89 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot90 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot91 : List IntPolynomial :=
  [[], [], [162, 162, -27, -27], [], [], [], [], []]

def quot92 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot93 : List IntPolynomial :=
  [[], [], [-162, -810, -135, 297, 27, -27], [], [], [], [], []]

def quot94 : List IntPolynomial :=
  [[], [], [], [], [], [], [], []]

def quot95 : List IntPolynomial :=
  [[126, 99, 9, -18], [], [], [], [], [], [], []]

def quot96 : List IntPolynomial :=
  [[108], [], [], [], [], [], [], []]

def quot97 : List IntPolynomial :=
  [[126, 387, 189, -135, -45, 18], [], [], [], [], [], [], []]

end QLS7.Cardinality40
