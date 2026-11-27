import KimberlingCore

namespace KimberlingMoses

/-- General form of the paper's positive complementary sequences. -/
structure Complementary (a b : ℕ → ℕ) : Prop where
  strictA : StrictMono a
  strictB : StrictMono b
  positiveA : ∀ n, 0 < a n
  positiveB : ∀ n, 0 < b n
  disjoint : ∀ n m, a n ≠ b m
  covers : ∀ t, 0 < t → (∃ n, a n = t) ∨ (∃ m, b m = t)

/-- The equation `a(n) = b(u*n) + b(v*n) + c`, with `b(0) = 1`. -/
structure OffsetSolution (u v c : ℕ) (a b : ℕ → ℕ) : Prop extends Complementary a b where
  initial : b 0 = 1
  equation : ∀ n, a n = b (u*n) + b (v*n) + c

private theorem no_first_less_offset {u v c : ℕ} {a b a' b' : ℕ → ℕ}
    (h : OffsetSolution u v c a b) (h' : OffsetSolution u v c a' b')
    (j : ℕ) (agree : ∀ i < j, b i = b' i) : ¬b j < b' j := by
  intro less
  rcases h'.covers (b j) (h.positiveB j) with ⟨m,hm⟩ | ⟨i,hi⟩
  · have hsum := h'.equation m
    have hp := h'.positiveB (u*m); have hq := h'.positiveB (v*m)
    have h1 : u*m < j := h'.strictB.lt_iff_lt.mp (by omega)
    have h2 : v*m < j := h'.strictB.lt_iff_lt.mp (by omega)
    apply h.disjoint m j
    rw [h.equation m, agree _ h1, agree _ h2]; omega
  · have hij : i < j := h'.strictB.lt_iff_lt.mp (by omega)
    have ht := h.strictB hij
    rw [agree i hij] at ht; omega

theorem offset_unique {u v c : ℕ} {a b a' b' : ℕ → ℕ}
    (h : OffsetSolution u v c a b) (h' : OffsetSolution u v c a' b') : a = a' ∧ b = b' := by
  have hb : ∀ j, b j = b' j := by
    intro j; induction j using Nat.strong_induction_on with
    | ind j ih =>
      have hab := no_first_less_offset h h' j ih
      have hba := no_first_less_offset h' h j (fun i hij => (ih i hij).symm)
      omega
  exact ⟨funext fun n => by rw [h.equation,h'.equation,hb,hb], funext hb⟩

/-- In each block of `H+1` consecutive positive integers, choose position `pos q`. -/
def blockA (H : ℕ) (pos : ℕ → ℕ) (q : ℕ) : ℕ := (H+1)*q + pos q

/-- In a block with one omitted position, return its `r`-th remaining location. -/
def skip (t r : ℕ) : ℕ := r + 1 + if t ≤ r+1 then 1 else 0

def blockB (H : ℕ) (pos : ℕ → ℕ) (n : ℕ) : ℕ :=
  (H+1)*(n/H) + skip (pos (n/H)) (n%H)

theorem blockB_at (H : ℕ) (hH : 0 < H) (pos : ℕ → ℕ) (q r : ℕ) (hr : r < H) :
    blockB H pos (H*q+r) = (H+1)*q + skip (pos q) r := by
  simp [blockB, Nat.mul_add_div hH, Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr]

private theorem skip_limits {H r : ℕ} (hr : r < H) (t : ℕ) : 1 ≤ skip t r ∧ skip t r ≤ H+1 := by
  unfold skip; split_ifs <;> omega

private theorem skip_avoids (t r : ℕ) : skip t r ≠ t := by unfold skip; split_ifs <;> omega

private theorem ordered_blocks {H q q' v v' : ℕ} (h : q < q') (hv : v ≤ H+1) (hv' : 0 < v') :
    (H+1)*q+v < (H+1)*q'+v' := by
  have step := Nat.mul_le_mul_left (H+1) (show q+1 ≤ q' by omega)
  rw [Nat.mul_add, Nat.mul_one] at step; omega

theorem block_complementary (H : ℕ) (hH : 0 < H) (pos : ℕ → ℕ)
    (hp : ∀ q, 1 ≤ pos q ∧ pos q ≤ H+1) : Complementary (blockA H pos) (blockB H pos) := by
  have hb (n : ℕ) := skip_limits (Nat.mod_lt n hH) (pos (n/H))
  constructor
  · intro i j hij; exact ordered_blocks hij (hp i).2 (hp j).1
  · intro i j hij; unfold blockB
    have divle : i/H ≤ j/H := Nat.div_le_div_right hij.le
    rcases eq_or_lt_of_le divle with eq | lt
    · have ei := Nat.div_add_mod i H; have ej := Nat.div_add_mod j H
      rw [eq] at ei ⊢; have rm : i%H < j%H := by omega
      unfold skip; split_ifs <;> omega
    · exact ordered_blocks lt (hb i).2 (hb j).1
  · intro i; unfold blockA; have := hp i; omega
  · intro i; unfold blockB; have := hb i; omega
  · intro i j; rcases lt_trichotomy i (j/H) with lt | eq | gt
    · exact ne_of_lt (ordered_blocks lt (hp i).2 (hb j).1)
    · unfold blockA blockB; rw [eq]; have ht := skip_avoids (pos (j/H)) (j%H); omega
    · exact ne_of_gt (ordered_blocks gt (hb j).2 (hp i).1)
  · intro x hx
    let q := (x-1)/(H+1); let v := (x-1)%(H+1)+1
    have block : x = (H+1)*q+v := by
      dsimp [q,v]; have := Nat.div_add_mod (x-1) (H+1); omega
    have hv : 1 ≤ v ∧ v ≤ H+1 := by dsimp [v]; have := Nat.mod_lt (x-1) (by omega : 0 < H+1); omega
    rcases lt_trichotomy v (pos q) with lo | eq | hi
    · have hr : v-1 < H := by have := hp q; omega
      refine Or.inr ⟨H*q+(v-1), ?_⟩; rw [blockB_at H hH pos q _ hr]
      unfold skip; split_ifs <;> omega
    · exact Or.inl ⟨q, by unfold blockA; rw [← eq,← block]⟩
    · have hr : v-2 < H := by omega
      refine Or.inr ⟨H*q+(v-2), ?_⟩; rw [blockB_at H hH pos q _ hr]
      unfold skip; have := hp q; split_ifs <;> omega

end KimberlingMoses
