import QuinticEndpoint

/-! Dimension growth of successive images of an endpoint map. A first
nonzero bilinear moment of rank r forces at least r new dimensions at
every layer before and including that moment. -/

noncomputable section
open Module LinearMap
namespace PencilMoment

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

def layer (P : V →ₗ[K] W) (M : W →ₗ[K] W) (i : ℕ) : V →ₗ[K] W := (M^i).comp P

def flag (P : V →ₗ[K] W) (M : W →ₗ[K] W) : ℕ → Submodule K W
  | 0 => P.range
  | i+1 => flag P M i ⊔ (layer P M (i+1)).range

private def test (B : LinearMap.BilinForm K W) (P : V →ₗ[K] W) (M : W →ₗ[K] W)
    (k : ℕ) : W →ₗ[K] Dual K V := (layer P M k).dualMap.comp B

omit [FiniteDimensional K W] in
theorem slide (B : LinearMap.BilinForm K W) (M : W →ₗ[K] W)
    (adj : ∀ x y, B (M x) y = B x (M y)) (x y : W) (i k : ℕ) :
    B ((M^i) x) ((M^k) y) = B x ((M^(i+k)) y) := by
  induction i generalizing k with
  | zero => simp
  | succ i ih =>
    rw [pow_succ' M i,mul_apply_eq_comp,adj]
    rw [show M ((M^k) y) = (M^(k+1)) y by rw [pow_succ']; rfl,ih]
    rw [show i+(k+1) = i+1+k by omega]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
private theorem small_flag (B : LinearMap.BilinForm K W) (P : V →ₗ[K] W) (M : W →ₗ[K] W)
    (adj : ∀ x y, B (M x) y = B x (M y)) (s : ℕ)
    (zero : ∀ j < s, ∀ x y, B (P x) ((M^j) (P y)) = 0) (i k : ℕ) (before : i+k < s) :
    flag P M i ≤ (test B P M k).ker := by
  induction i with
  | zero =>
    rintro _ ⟨x,rfl⟩
    apply LinearMap.ext
    intro y
    exact zero k (by omega) x y
  | succ i ih =>
    apply sup_le (ih (by omega))
    rintro _ ⟨x,rfl⟩
    apply LinearMap.ext
    intro y
    change B ((M^(i+1)) (P x)) ((M^k) (P y)) = 0
    rw [slide B M adj]
    exact zero _ before x y

/-- Testing the new layer by a map which kills the old subspace gives a
lower bound on the dimension gained on adjoining the new layer. -/
private theorem gain (U : Submodule K W) (Q : V →ₗ[K] W) (T : W →ₗ[K] Dual K V)
    (van : U ≤ T.ker) :
    finrank K U + finrank K (T.comp Q).range ≤ finrank K ↥(U ⊔ Q.range) := by
  let F := U ⊔ Q.range
  let f := T.comp F.subtype
  let inc : U →ₗ[K] F := Submodule.inclusion (show U ≤ F from le_sup_left)
  let incK := inc.codRestrict f.ker (fun x ↦ van x.property)
  have injective : Function.Injective incK :=
    fun x y h ↦ Subtype.ext (congrArg (fun z : f.ker ↦ z.val.val) h)
  let q := Q.codRestrict F (fun x ↦ (show Q.range ≤ F from le_sup_right) ⟨x,rfl⟩)
  have eq : T.comp Q = f.comp q := rfl
  have rankQ := Submodule.finrank_mono (LinearMap.range_comp_le_range q f)
  have rankU := LinearMap.finrank_le_finrank_of_injective injective
  have dim := f.finrank_range_add_finrank_ker
  change _ ≤ finrank K F
  rw [eq]
  omega

/-- Dimension growth up to the order of the first potentially nonzero moment. -/
theorem flag_dimension (B : LinearMap.BilinForm K W) (P : V →ₗ[K] W) (M : W →ₗ[K] W)
    (adj : ∀ x y, B (M x) y = B x (M y)) (s : ℕ) (H : V →ₗ[K] Dual K V)
    (zero : ∀ j < s, ∀ x y, B (P x) ((M^j) (P y)) = 0)
    (moment : ∀ x y, B (P x) ((M^s) (P y)) = H x y) (i : ℕ) (bound : i ≤ s) :
    finrank K P.range + i * finrank K H.range ≤ finrank K (flag P M i) := by
  induction i with
  | zero => simp only [flag,Nat.zero_mul,Nat.add_zero]; exact Nat.le_refl _
  | succ i ih =>
    let k := s-(i+1)
    have sum : i+1+k = s := by dsimp [k]; omega
    have van := small_flag B P M adj s zero i k (by omega)
    have eq : (test B P M k).comp (layer P M (i+1)) = H := by
      ext x y
      change B ((M^(i+1)) (P x)) ((M^k) (P y)) = H x y
      rw [slide B M adj,sum,moment]
    have add := gain (flag P M i) (layer P M (i+1)) (test B P M k) van
    rw [eq] at add
    have prev := ih (by omega)
    change _ ≤ finrank K ↥(flag P M i ⊔ (layer P M (i+1)).range)
    rw [Nat.succ_mul]
    omega

/-- The first s+1 layers are orthogonal to the endpoints if the first
potentially nonzero moment has order s+1. -/
theorem endpoint_dimension (B : LinearMap.BilinForm K W) (nondeg : B.Nondegenerate)
    (P : V →ₗ[K] W) (M : W →ₗ[K] W) (adj : ∀ x y, B (M x) y = B x (M y))
    (s : ℕ) (H : V →ₗ[K] Dual K V)
    (zero : ∀ j < s+1, ∀ x y, B (P x) ((M^j) (P y)) = 0)
    (moment : ∀ x y, B (P x) ((M^(s+1)) (P y)) = H x y) :
    2 * finrank K P.range + s * finrank K H.range ≤ finrank K W := by
  let F := flag P M s
  have vanish := small_flag B P M adj (s+1) zero s 0 (by omega)
  have orth : P.range ≤ B.orthogonal F := by
    rintro _ ⟨u,rfl⟩ y hy
    have yz := congrArg (fun f : Dual K V ↦ f u) (vanish hy)
    simpa [test,layer] using yz
  have dim := B.finrank_add_finrank_orthogonal' F
  rw [nondeg.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero] at dim
  have lo := flag_dimension B P M adj (s+1) H zero moment s (by omega)
  have le := Submodule.finrank_mono orth
  change _ ≤ finrank K F at lo
  omega

#print axioms flag_dimension
#print axioms endpoint_dimension
end PencilMoment
