/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.Polynomial
public import Quantum.SmallSevenGuo.Real
public import Mathlib.Data.List.DropRight
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Evaluation of polynomial certificates
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7.IntPolynomial

def eval (p : IntPolynomial) (x : ℝ) : ℝ :=
  p.foldr (fun a y => a + x * y) 0

@[simp] theorem eval_nil (x : ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : ℤ) (p : IntPolynomial) (x : ℝ) :
    eval (a :: p) x = a + x * eval p x := rfl

theorem eval_add (p q : IntPolynomial) (x : ℝ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih, Int.cast_add]; ring

theorem eval_scale (a : ℤ) (p : IntPolynomial) (x : ℝ) :
    eval (scale a p) x = a * eval p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change eval (a * b :: scale a p) x = a * (b + x * eval p x)
    rw [eval_cons, ih, Int.cast_mul]
    ring

theorem eval_mul (p q : IntPolynomial) (x : ℝ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, eval_add, eval_scale, ih]; ring

theorem eval_append (p q : IntPolynomial) (x : ℝ) :
    eval (p ++ q) x = eval p x + x ^ p.length * eval q x := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih, pow_succ]; ring

theorem eval_trim (p : IntPolynomial) (x : ℝ) : eval (trim p) x = eval p x := by
  change eval (p.rdropWhile (· == 0)) x = eval p x
  induction p using List.reverseRecOn with
  | nil => simp
  | append_singleton p a ih =>
    rw [List.rdropWhile_concat]
    by_cases ha : a = 0
    · simp [ha, ih, eval_append]
    · simp [ha]

theorem continuous_eval (p : IntPolynomial) : Continuous (eval p) := by
  induction p with
  | nil => exact continuous_const
  | cons a p ih => exact continuous_const.add (continuous_id.mul ih)

end QLS7.IntPolynomial
