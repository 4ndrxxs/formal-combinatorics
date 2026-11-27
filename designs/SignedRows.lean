import SignedBasic

/-! Projection, bit-vector representation and finite counting for cyclic words of length 39. -/

namespace Signed39

open Finset

abbrev A := Fin 13
abbrev B := Fin 3
abbrev AB := A × B

def projection (f : AB → ℤ) (i : A) : ℤ := ∑ j : B, f (i,j)

theorem projection_corr (f : AB → ℤ) (t : A) :
    corr (projection f) t = ∑ b : B, corr f (t,b) := by
  simp only [corr, projection, Fintype.sum_prod_type, Prod.mk_add_mk]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_mul, Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  congr 1
  simpa [add_comm] using (sum_translate (fun b : B => f (i+t,b)) j).symm

def bits {n : ℕ} (p : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn p)).cast (by simp)

@[simp] theorem bits_get {n : ℕ} (p : Fin n → Bool) (i : Fin n) :
    (bits p).getLsbD i = p i := by
  simp only [bits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

def bitInt {n : ℕ} (m : BitVec n) (i : Fin n) : ℤ := if m.getLsbD i then 1 else 0

def rowMask (f : AB → ℤ) (i : A) : BitVec 3 :=
  bits (fun j : Fin 3 => decide (f (i,j) = 1))

abbrev C := Fin 39

def residues : C ≃+ AB where
  toFun n := (Fin.ofNat 13 n.val, Fin.ofNat 3 n.val)
  invFun x := Fin.ofNat 39 (27*x.1.val + 13*x.2.val)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel

def cyclicIndex : ZMod 39 ≃+ C where
  toFun x := ⟨x.val,x.val_lt⟩
  invFun x := x.val
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel

def tableCount (x : BitVec 6) : ℤ :=
  (((0xd6cb23b238dab238da8da691b238da8da6918da691691448 : ℕ) >>> (3*x.toNat)) &&& 7 : ℕ)

private theorem table_spec : ∀ x : BitVec 6, tableCount x = ∑ i : Fin 6, bitInt x i := by decide +kernel

def count (x : BitVec 39) : ℤ := ∑ j : Fin 7, tableCount ((x >>> (6*j.val)).setWidth 6)

theorem count_spec (x : BitVec 39) : count x = ∑ i : C, bitInt x i := by
  unfold count
  simp_rw [table_spec]
  simp only [bitInt, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    add_zero, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  norm_num [BitVec.getLsbD_of_ge]
  abel

theorem rotated_bit (s : BitVec 39) (i t : C) :
    (s.rotateRight t.val).getLsbD i.val = s.getLsbD (i+t).val := by
  have idx : ∀ i t : C, (if i.val < 39 - t.val % 39 then t.val % 39 + i.val
      else i.val - (39 - t.val % 39)) = (i+t).val := by decide +kernel
  have hi := idx i t
  rw [BitVec.getLsbD_rotateRight]
  by_cases h : i.val < 39 - t.val % 39
  · simp only [h, ite_true] at hi ⊢
    rw [hi]
  · simp only [h, ite_false, decide_eq_true i.isLt, Bool.true_and] at hi ⊢
    rw [hi]

def chunk (i : A) (b : BitVec 3) : BitVec 39 :=
  bits (fun x : C => decide ((residues x).1 = i) && b.getLsbD (residues x).2.val)

def pack (rows : A → BitVec 3) (todo : List A) (s : BitVec 39) : BitVec 39 :=
  todo.foldl (fun v i => v ||| chunk i (rows i)) s

theorem packed_bit (rows : A → BitVec 3) (todo : List A) (s : BitVec 39) (x : C) :
    (pack rows todo s).getLsbD x.val =
      (s.getLsbD x.val || (decide ((residues x).1 ∈ todo) && (rows (residues x).1).getLsbD (residues x).2.val)) := by
  induction todo generalizing s with
  | nil => simp [pack]
  | cons i todo ih =>
    change (pack rows todo (s ||| chunk i (rows i))).getLsbD x.val = _
    rw [ih,BitVec.getLsbD_or]
    simp only [chunk, bits_get, List.mem_cons]
    by_cases hi : (residues x).1 = i
    · subst i
      by_cases hm : (residues x).1 ∈ todo <;> simp [hm]
    · simp [hi]

def rawTableCount (n : ℕ) : ℕ :=
  ((0xd6cb23b238dab238da8da691b238da8da6918da691691448 : ℕ) >>> (3*(n % 64))) &&& 7

def rawCount (n : ℕ) : ℕ :=
  rawTableCount n + rawTableCount (n >>> 6) + rawTableCount (n >>> 12) +
  rawTableCount (n >>> 18) + rawTableCount (n >>> 24) + rawTableCount (n >>> 30) +
  rawTableCount (n >>> 36)

theorem count_raw (s : BitVec 39) : count s = (rawCount s.toNat : ℤ) := by
  simp [count, tableCount, rawCount, rawTableCount, Fin.sum_univ_succ, BitVec.toNat_setWidth]
  abel

theorem any_on {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

end Signed39
