import Quantum.Hadamard.PaleyT271
import Quantum.Hadamard.Goethals

/-! Seberry and Yamada's product of a T-system and a Hadamard
matrix in sixteen circulant blocks. All dot products here are integral. -/
namespace Hadamard.PeriodicT
open Finset HadamardMod
noncomputable section

structure BlockSystem (s : ℕ) where
  row : Fin 4 → Fin 4 → Fin s → ℤ
  signs : ∀ i j y, HadamardMod.Sign (row i j y)
  gram : ∀ i k v, (∑ j, ∑ y, row i j y * row k j (y+v)) =
     if i=k ∧ v.val=0 then (4*s : ℤ) else 0

private theorem rearrange {t s : ℕ}
    (f : Fin 4 → Fin t → ℤ) (g : Fin 4 → Fin t → ℤ)
    (P Q : Fin 4 → Fin 4 → Fin s → ℤ) :
    (∑ c:Fin 4, ∑ x:Fin t, ∑ y:Fin s,
      (∑ i, f i x * P i c y) * (∑ k, g k x * Q k c y)) =
    ∑ x, ∑ i, ∑ k, (f i x*g k x)*(∑ c, ∑ y, P i c y * Q k c y) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [sum_mul, mul_sum]
  let h (c : Fin 4) (y : Fin s) (i k : Fin 4) :=
    f i x * P i c y * (g k x * Q k c y)
  change (∑ c, ∑ y, ∑ k, ∑ i, h c y i k) = _
  calc
    _ = ∑ c, ∑ y, ∑ i, ∑ k, h c y i k := by
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro y _; rw [Finset.sum_comm]
    _ = ∑ c, ∑ i, ∑ y, ∑ k, h c y i k := by
      apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ c, ∑ y, ∑ k, h c y i k := Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ k, ∑ y, h c y i k := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_comm]
    _ = ∑ i, ∑ k, ∑ c, ∑ y, h c y i k := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro y _
      dsimp [h]; ring

/-- A T-system of length t and sixteen sign circulants of size s whose
block rows are orthogonal give an ordinary Hadamard matrix of order 4ts. -/
theorem real_of_blocks {t s : ℕ} [NeZero t] [NeZero s] (T : System t)
    (N : BlockSystem s) : HadamardMod.AtOrder 0 (4*(t*s)) := by
  let V (c : Fin 4) (z : Fin t × Fin s) : ℤ := ∑ i, T.entry i z.1 * N.row i c z.2
  have sign (c : Fin 4) (z : Fin t × Fin s) : HadamardMod.Sign (V c z) := by
    obtain ⟨a,ha,uniq⟩ := T.partition z.1
    have va : V c z = T.entry a z.1*N.row a c z.2 := by
      apply Finset.sum_eq_single a
      · intro i _ ine
        have e : T.entry i z.1=0 := by
          by_contra h; exact ine (uniq i h)
        simp [e]
      · simp
    rw [va]
    apply HadamardMod.sign_mul _ (N.signs _ _ _)
    rcases T.ternary a z.1 with h|h|h
    · exact (ha h).elim
    · exact Or.inl h
    · exact Or.inr h
  have corr (u : Fin t) (v : Fin s) (hne : (u,v) ≠ 0) :
      (∑ c, ∑ z:Fin t × Fin s, V c z * V c (z+(u,v))) = 0 := by
    simp only [Fintype.sum_prod_type]
    change (∑ c, ∑ x, ∑ y, (∑ i, T.entry i x*N.row i c y) *
       (∑ k, T.entry k (x+u)*N.row k c (y+v)))=_
    rw [rearrange (f:=T.entry) (g:=fun k x => T.entry k (x+u))
        (P:=N.row) (Q:=fun k c y => N.row k c (y+v))]
    simp_rw [N.gram]
    by_cases hv : v.val=0
    · have hu : u.val≠0 := by
        intro he
        apply hne
        ext <;> assumption
      simp [hv, ← Finset.sum_mul]
      rw [Finset.sum_comm]
      have eq := T.correlation u
      simp [hu] at eq
      simp [eq]
    · simp [hv]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (HadamardMod.goethals_AtOrder (m:=0) (I:=Fin t × Fin s) V sign
      (fun z hz => corr z.1 z.2 hz))

#print axioms real_of_blocks
end
end Hadamard.PeriodicT

