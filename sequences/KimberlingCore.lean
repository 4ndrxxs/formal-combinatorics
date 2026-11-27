import Mathlib

/-! Complementary equations with advanced subscripts, Kimberling–Moses (2021), §5. -/

namespace KimberlingMoses

/-- The literal complementary equation in the paper. The two increasing sequences
have disjoint ranges whose union consists of all positive integers. -/
structure Solution (a b : ℕ → ℕ) : Prop where
  strictA : StrictMono a
  strictB : StrictMono b
  positiveA : ∀ i, 0 < a i
  positiveB : ∀ i, 0 < b i
  disjoint : ∀ i j, a i ≠ b j
  covers : ∀ x, 0 < x → (∃ i, a i = x) ∨ (∃ j, b j = x)
  initial : b 0 = 1
  equation : ∀ n, a n = b n + b (2*n)

/-- A one records the choice `b (3*i+1) = 4*i+2`. -/
def bit (n : ℕ) : Bool :=
  if n % 3 = 0 then false
  else if n % 3 = 1 then !(bit (n / 3))
  else !(bit (2 * (n / 3) + 1))
termination_by n
decreasing_by all_goals omega

@[simp] theorem bit_zero (i : ℕ) : bit (3*i) = false := by
  rw [bit]; simp

@[simp] theorem bit_one (i : ℕ) : bit (3*i+1) = !(bit i) := by
  rw [bit]; simp [Nat.mul_add_div (by decide : 0 < 3)]

@[simp] theorem bit_two (i : ℕ) : bit (3*i+2) = !(bit (2*i+1)) := by
  rw [bit]; simp [Nat.mul_add_div (by decide : 0 < 3)]

def seqA (i : ℕ) : ℕ := 4*i + if bit i then 3 else 2

def seqB (n : ℕ) : ℕ :=
  4*(n/3) + if n%3 = 0 then 1 else if n%3 = 1 then (if bit (n/3) then 2 else 3) else 4

@[simp] theorem seqB_zero (i : ℕ) : seqB (3*i) = 4*i+1 := by simp [seqB]

@[simp] theorem seqB_one (i : ℕ) : seqB (3*i+1) = 4*i + (if bit i then 2 else 3) := by
  simp [seqB, Nat.mul_add_div (by decide : 0 < 3)]

@[simp] theorem seqB_two (i : ℕ) : seqB (3*i+2) = 4*i+4 := by
  simp [seqB, Nat.mul_add_div (by decide : 0 < 3)]

theorem three_cases (n : ℕ) : ∃ q, n = 3*q ∨ n = 3*q+1 ∨ n = 3*q+2 := by
  exact ⟨n/3, by omega⟩

theorem seqA_sides (i : ℕ) : 4*i+2 ≤ seqA i ∧ seqA i ≤ 4*i+3 := by
  unfold seqA; cases bit i <;> simp

theorem seqB_sides (n : ℕ) : 4*(n/3)+1 ≤ seqB n ∧ seqB n ≤ 4*(n/3)+4 := by
  unfold seqB; split_ifs <;> omega

theorem seqA_strict : StrictMono seqA := by
  intro i j hij
  have := seqA_sides i; have := seqA_sides j; omega

theorem seqB_strict : StrictMono seqB := by
  apply strictMono_nat_of_lt_succ; intro n
  obtain ⟨q,h|h|h⟩ := three_cases n
  · subst n; rw [seqB_zero, seqB_one]; split_ifs <;> omega
  · subst n; rw [seqB_one, show 3*q+1+1 = 3*q+2 by omega, seqB_two]; split_ifs <;> omega
  · subst n; rw [seqB_two, show 3*q+2+1 = 3*(q+1) by omega, seqB_zero]; omega

theorem seq_disjoint (i n : ℕ) : seqA i ≠ seqB n := by
  obtain ⟨q,h|h|h⟩ := three_cases n <;> subst n
  · rw [seqB_zero]; have := seqA_sides i; omega
  · rw [seqB_one]; by_cases h : i = q
    · subst q; unfold seqA; cases bit i <;> simp
    · have := seqA_sides i; split_ifs <;> omega
  · rw [seqB_two]; have := seqA_sides i; omega

theorem seq_covers (x : ℕ) (hx : 0 < x) : (∃ i, seqA i = x) ∨ ∃ j, seqB j = x := by
  let q := (x-1)/4
  have h : x = 4*q+1 ∨ x = 4*q+2 ∨ x = 4*q+3 ∨ x = 4*q+4 := by dsimp [q]; omega
  rcases h with h|h|h|h
  · exact Or.inr ⟨3*q, by rw [seqB_zero,h]⟩
  · cases he : bit q
    · exact Or.inl ⟨q, by simp [seqA,he,h]⟩
    · exact Or.inr ⟨3*q+1, by rw [seqB_one,h]; simp [he]⟩
  · cases he : bit q
    · exact Or.inr ⟨3*q+1, by rw [seqB_one,h]; simp [he]⟩
    · exact Or.inl ⟨q, by simp [seqA,he,h]⟩
  · exact Or.inr ⟨3*q+2, by rw [seqB_two,h]⟩

theorem seq_equation (n : ℕ) : seqA n = seqB n + seqB (2*n) := by
  obtain ⟨q,h|h|h⟩ := three_cases n <;> subst n <;> unfold seqA
  · rw [bit_zero, seqB_zero, show 2*(3*q) = 3*(2*q) by omega, seqB_zero]; simp; omega
  · rw [bit_one, seqB_one, show 2*(3*q+1) = 3*(2*q)+2 by omega, seqB_two]; cases bit q <;> simp <;> omega
  · rw [bit_two, seqB_two, show 2*(3*q+2) = 3*(2*q+1)+1 by omega, seqB_one]; cases bit (2*q+1) <;> simp <;> omega

theorem explicit_solution : Solution seqA seqB where
  strictA := seqA_strict
  strictB := seqB_strict
  positiveA i := by have := seqA_sides i; omega
  positiveB i := by have := seqB_sides i; omega
  disjoint := seq_disjoint
  covers := seq_covers
  initial := by rfl
  equation := seq_equation

private theorem no_first_less {a b a' b' : ℕ → ℕ} (h : Solution a b) (h' : Solution a' b')
    (j : ℕ) (agree : ∀ i < j, b i = b' i) : ¬b j < b' j := by
  intro less
  rcases h'.covers (b j) (h.positiveB j) with ⟨m,hm⟩ | ⟨i,hi⟩
  · have hsum := h'.equation m
    have hp := h'.positiveB m
    have hq := h'.positiveB (2*m)
    have h1 : m < j := h'.strictB.lt_iff_lt.mp (by omega)
    have h2 : 2*m < j := h'.strictB.lt_iff_lt.mp (by omega)
    apply h.disjoint m j
    rw [h.equation m, agree m h1, agree (2*m) h2]; omega
  · have hij : i < j := h'.strictB.lt_iff_lt.mp (by omega)
    have ht := h.strictB hij
    rw [agree i hij] at ht; omega

theorem solution_unique {a b a' b' : ℕ → ℕ} (h : Solution a b) (h' : Solution a' b') :
    a = a' ∧ b = b' := by
  have hb : ∀ j, b j = b' j := by
    intro j; induction j using Nat.strong_induction_on with
    | ind j ih =>
      have h1 := no_first_less h h' j ih
      have h2 := no_first_less h' h j (fun i hij => (ih i hij).symm)
      omega
  exact ⟨funext fun n => by rw [h.equation,h'.equation,hb,hb], funext hb⟩

/-- The index property that the paper counts, with the paper's zero-based equation. -/
def Good (b : ℕ → ℕ) (i : ℕ) : Prop := b (3*i+1) = 4*i+2

instance (b : ℕ → ℕ) (i : ℕ) : Decidable (Good b i) := inferInstanceAs (Decidable (_ = _))

theorem good_iff_bit {a b : ℕ → ℕ} (h : Solution a b) (i : ℕ) : Good b i ↔ bit i = true := by
  rw [(solution_unique h explicit_solution).2]; unfold Good; rw [seqB_one]; cases bit i <;> simp

end KimberlingMoses
