import PencilMomentFlag

/-! Equality in the moment dimension count. When the last layer fills the
ambient space and all later moments vanish, the transfer has bounded index. -/

noncomputable section
open Module LinearMap
namespace PencilMoment
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem flag_le_of_layers (P : V →ₗ[K] W) (M : W →ₗ[K] W) (s : ℕ) (T : Submodule K W)
    (h : ∀ i ≤ s, (layer P M i).range ≤ T) : flag P M s ≤ T := by
  induction s with
  | zero =>
    rintro _ ⟨x,rfl⟩
    exact h 0 (Nat.le_refl _) ⟨x,by simp [layer]⟩
  | succ s ih => exact sup_le (ih (fun i hi ↦ h i (by omega))) (h _ (Nat.le_refl _))

/-- Once all endpoint layers span W, a zero tail of moments is a zero
power of the transfer itself. -/
theorem power_zero_of_full_flag (B : LinearMap.BilinForm K W) (nondeg : B.Nondegenerate)
    (P : V →ₗ[K] W) (M : W →ₗ[K] W) (adj : ∀ x y, B (M x) y = B x (M y))
    (s : ℕ) (full : flag P M s = ⊤)
    (tail : ∀ j, s < j → ∀ x y, B (P x) ((M^j) (P y)) = 0) : M^(s+1) = 0 := by
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← full]
  apply flag_le_of_layers
  intro i _ w hw
  obtain ⟨u,rfl⟩ := hw
  apply nondeg.1
  intro y
  have cut : flag P M s ≤ (B ((M^(s+1)) (layer P M i u))).ker := by
    apply flag_le_of_layers
    intro j _ q hq
    obtain ⟨v,rfl⟩ := hq
    change B ((M^(s+1)) ((M^i) (P u))) ((M^j) (P v)) = 0
    rw [slide B M adj,slide B M adj]
    exact tail _ (by omega) u v
  exact cut (show y ∈ flag P M s by rw [full]; trivial)

end PencilMoment
