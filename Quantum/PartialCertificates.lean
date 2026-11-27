module

public import Quantum.Pivots
public import Quantum.PartialArray

/-! Finite, exact certificates for a partial array. Representatives carry
a common first nonzero coordinate, making uniqueness checkable by a code. -/

@[expose] public section
namespace QuantumCertificate.Coefficients
open Finset

variable {T : Type} [AddCommMonoid T] (a : Coefficients T)

def Chart {c d : ℕ} (r : Fin c → Fin d → T) (p : Fin c → Fin d) (M : T) : Prop :=
  ∀ i, r i (p i) = M ∧ ∀ x, x < p i → r i x = 0

instance [DecidableEq T] {c d : ℕ} (r : Fin c → Fin d → T) (p : Fin c → Fin d) (M : T) :
    Decidable (Chart r p M) := inferInstanceAs (Decidable (∀ i : Fin c,
      r i (p i) = M ∧ ∀ x : Fin d, x < p i → r i x = 0))

theorem chart_injective {c d : ℕ} {r : Fin c → Fin d → T} {p : Fin c → Fin d} {M : T}
    (hc : Chart r p M) (hM : M ≠ 0) (hr : Function.Injective r) (i j : Fin c) (s : ℂ)
    (he : s • a.raw (r j) = a.raw (r i)) : i = j := by
  have eqc (x : Fin d) : s * a.eval (r j x) = a.eval (r i x) := congrArg (fun w : Space d => w x) he
  have hm : a.eval M ≠ 0 := fun h => hM (a.faithful (h.trans (map_zero a.eval).symm))
  have hs : s ≠ 0 := by
    intro hh
    have h := eqc (p i)
    rw [hh,zero_mul,(hc i).1] at h
    exact hm h.symm
  have hp : p i = p j := by
    rcases lt_trichotomy (p i) (p j) with h|h|h
    · have hh := eqc (p i)
      rw [(hc j).2 _ h, map_zero, mul_zero,(hc i).1] at hh
      exact False.elim (hm hh.symm)
    · exact h
    · have hh := eqc (p j)
      rw [(hc i).2 _ h,map_zero,(hc j).1] at hh
      exact False.elim (mul_ne_zero hs hm hh)
  have h1 : s = 1 := by
    have h := eqc (p i)
    rw [(hc i).1,hp,(hc j).1] at h
    exact mul_right_cancel₀ hm (h.trans (one_mul _).symm)
  apply hr
  funext x
  apply a.faithful
  simpa [h1] using (eqc x).symm

theorem injective_by_code {I V : Type*} (r : I → V) (encode : V → ℕ) (code : I → ℕ)
    (h : ∀ i, encode (r i) = code i) (hi : Function.Injective code) : Function.Injective r :=
  fun i j he => hi ((h i).symm.trans ((congrArg encode he).trans (h j)))

def MaskOrth {n d c : ℕ} (m : Cell n → Bool) (r : Fin c → Fin d → T)
    (l : Cell n → Fin c) : Prop :=
  ∀ i j k, m (i,j) = true → m (i,k) = true → j ≠ k → a.dot (r (l (i,j))) (r (l (i,k))) = 0

instance [DecidableEq T] {n d c : ℕ} (m : Cell n → Bool) (r : Fin c → Fin d → T)
    (l : Cell n → Fin c) : Decidable (a.MaskOrth m r l) :=
  inferInstanceAs (Decidable (∀ i j k : Fin n, m (i,j) = true → m (i,k) = true →
    j ≠ k → a.dot (r (l (i,j))) (r (l (i,k))) = 0))

theorem partialArray {n d c : ℕ} (m : Cell n → Bool) (r : Fin c → Fin d → T)
    (label : Cell n → Fin c) (p : Fin c → Fin d) (M : T) (hM : M ≠ 0)
    (hc : Chart r p M) (hr : Function.Injective r)
    (cover : ∀ k, ∃ x : Cell n, m x = true ∧ label x = k)
    (rows : a.MaskOrth m r label)
    (cols : a.MaskOrth (fun x => m x.swap) r (fun x => label x.swap)) :
    Nonempty (PartialArray n d c m) := by
  classical
  have nz (k : Fin c) : a.raw (r k) ≠ 0 := by
    intro hz
    have hx := congrArg (fun w : Space d => w (p k)) hz
    change a.eval (r k (p k)) = 0 at hx
    rw [(hc k).1] at hx
    exact hM (a.faithful (hx.trans (map_zero a.eval).symm))
  let w (i : Fin c) : Space d := (‖a.raw (r i)‖ : ℂ)⁻¹ • a.raw (r i)
  have unit (i : Fin c) : ‖w i‖ = 1 := by
    simp [w,norm_smul,Complex.norm_real,norm_ne_zero_iff.mpr (nz i)]
  have wn (i : Fin c) : w i ≠ 0 := by intro hz; simpa [hz] using unit i
  have ortho (i j : Fin c) (hg : a.dot (r i) (r j) = 0) : inner ℂ (w i) (w j) = 0 := by
    simp [w,inner_smul_left,inner_smul_right,a.raw_inner,hg]
  let proj (i : Fin c) := Projectivization.mk ℂ (a.raw (r i)) (nz i)
  have proj_inj : Function.Injective proj := by
    intro i j h
    obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    exact a.chart_injective hc hM hr i j s hs
  refine ⟨⟨fun x => w (label x),fun x => wn _,fun x => unit _,
    fun i j k hj hk h => ortho _ _ (rows i j k hj hk h),
    fun i j k hj hk h => ortho _ _ (cols i j k hj hk h), ?_⟩⟩
  let lab (x : Used m) := label x.val
  have onto : Function.Surjective lab := by
    intro k
    obtain ⟨x,hx,he⟩ := cover k
    exact ⟨⟨x,hx⟩,he⟩
  have eqr : rayRange (fun x : Used m => w (label x.val)) (fun x => wn _) =
      Set.range (proj ∘ lab) := by
    apply congrArg Set.range
    funext x
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨_,rfl⟩
  rw [eqr,Function.Surjective.range_comp onto,Set.ncard_range_of_injective proj_inj]
  simp

end QuantumCertificate.Coefficients
