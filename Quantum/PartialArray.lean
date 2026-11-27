module

public import Quantum.Exact
public import Mathlib.Data.Fin.Embedding

/-! Combining two partial orthonormal arrays in orthogonal summands. -/

@[expose] public section
namespace QuantumCertificate

abbrev Used {n : ℕ} (mask : Cell n → Bool) := {p : Cell n // mask p = true}

noncomputable def rayRange {I : Type*} {d : ℕ} (v : I → Space d) (h : ∀ i, v i ≠ 0) :
    Set (Projectivization ℂ (Space d)) :=
  Set.range (fun i => Projectivization.mk ℂ (v i) (h i))

structure PartialArray (n d c : ℕ) (mask : Cell n → Bool) where
  entry : Cell n → Space d
  nz : ∀ p : Used mask, entry p.val ≠ 0
  unit : ∀ p : Used mask, ‖entry p.val‖ = 1
  rows : ∀ i j k, mask (i,j) = true → mask (i,k) = true → j ≠ k →
    inner ℂ (entry (i,j)) (entry (i,k)) = 0
  cols : ∀ i j k, mask (j,i) = true → mask (k,i) = true → j ≠ k →
    inner ℂ (entry (j,i)) (entry (k,i)) = 0
  count : (rayRange (fun p : Used mask => entry p.val) nz).ncard = c

namespace PartialArray

noncomputable def rays {n d c : ℕ} {mask : Cell n → Bool} (a : PartialArray n d c mask) :=
  rayRange (fun p : Used mask => a.entry p.val) a.nz

theorem rays_finite {n d c : ℕ} {mask : Cell n → Bool} (a : PartialArray n d c mask) :
    a.rays.Finite := Set.finite_range _

private theorem ONB_of_unit_orthogonal {n : ℕ} [NeZero n] (v : Fin n → Space n)
    (h1 : ∀ i, ‖v i‖ = 1) (h2 : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = v := by
  classical
  have h : Orthonormal ℂ v := ⟨h1,fun i j hne => h2 i j hne⟩
  refine ⟨OrthonormalBasis.mk h ?_, OrthonormalBasis.coe_mk _ _⟩
  exact (h.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge

theorem joinWith {n u v cu cv : ℕ} [NeZero n] (mask : Cell n → Bool)
    (a : PartialArray n u cu mask) (b : PartialArray n v cv (fun p => !(mask p)))
    (L : Space u →ₗᵢ[ℂ] Space n) (R : Space v →ₗᵢ[ℂ] Space n)
    (orth : ∀ x y, inner ℂ (L x) (R y) = 0) : Realized n (cu+cv) := by
  classical
  let w (p : Cell n) := if mask p then L (a.entry p) else R (b.entry p)
  have hw (p : Cell n) : ‖w p‖ = 1 := by
    cases he : mask p with
    | false => simpa [w,he] using b.unit ⟨p,by simp [he]⟩
    | true => simpa [w,he] using a.unit ⟨p,he⟩
  have hn (p : Cell n) : w p ≠ 0 := by intro h; simpa [h] using hw p
  have hpair (p q : Cell n)
      (ha : mask p = true → mask q = true → inner ℂ (a.entry p) (a.entry q) = 0)
      (hb : (!mask p) = true → (!mask q) = true → inner ℂ (b.entry p) (b.entry q) = 0) :
      inner ℂ (w p) (w q) = 0 := by
    cases hp : mask p <;> cases hq : mask q
    · simpa [w,hp,hq] using hb (by simp [hp]) (by simp [hq])
    · simpa [w,hp,hq] using (inner_eq_zero_symm.mpr (orth (a.entry q) (b.entry p)))
    · simpa [w,hp,hq] using orth (a.entry p) (b.entry q)
    · simpa [w,hp,hq] using ha hp hq
  refine ⟨fun i j => w (i,j), fun i j => hn (i,j),
    fun i => ONB_of_unit_orthogonal _ (fun j => hw (i,j)) (fun j k h => ?_),
    fun j => ONB_of_unit_orthogonal _ (fun i => hw (i,j)) (fun i k h => ?_), ?_⟩
  · exact hpair (i,j) (i,k) (fun hj hk => a.rows i j k hj hk h)
      (fun hj hk => b.rows i j k hj hk h)
  · exact hpair (i,j) (k,j) (fun hi hk => a.cols j i k hi hk h)
      (fun hi hk => b.cols j i k hi hk h)
  let mL := Projectivization.map L.toLinearMap L.injective
  let mR := Projectivization.map R.toLinearMap R.injective
  let s := mL '' a.rays
  let t := mR '' b.rays
  have hset : rayRange w hn = s ∪ t := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩
      cases he : mask p with
      | false =>
        right
        refine ⟨_,⟨⟨p,by simp [he]⟩,rfl⟩,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨1,by simp [w,he]⟩
      | true =>
        left
        refine ⟨_,⟨⟨p,he⟩,rfl⟩,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨1,by simp [w,he]⟩
    · rintro (⟨_,⟨p,rfl⟩,rfl⟩|⟨_,⟨p,rfl⟩,rfl⟩)
      · refine ⟨p.val,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨1,by simp [w,p.property]⟩
      · refine ⟨p.val,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        have he : mask p.val = false := by simpa using p.property
        exact ⟨1,by simp [w,he]⟩
  have dis : Disjoint s t := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨_,⟨p,rfl⟩,rfl⟩ ⟨_,⟨q,rfl⟩,he⟩
    obtain ⟨z,hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
    have hh := congrArg (fun x => inner ℂ (R (b.entry q.val)) x) hz
    change inner ℂ (R (b.entry q.val)) (z • L (a.entry p.val)) =
      inner ℂ (R (b.entry q.val)) (R (b.entry q.val)) at hh
    have hrl : inner ℂ (R (b.entry q.val)) (L (a.entry p.val)) = 0 :=
      inner_eq_zero_symm.mpr (orth _ _)
    have hrr : inner ℂ (R (b.entry q.val)) (R (b.entry q.val)) = 1 :=
      inner_self_eq_one_of_norm_eq_one (by simp [b.unit q])
    simp only [inner_smul_right,hrl,hrr,mul_zero] at hh
    exact zero_ne_one hh
  change (rayRange w hn).ncard = _
  rw [hset, Set.ncard_union_eq dis (a.rays_finite.image _) (b.rays_finite.image _)]
  change (mL '' a.rays).ncard + (mR '' b.rays).ncard = _
  rw [Set.ncard_image_of_injective _ (Projectivization.map_injective _ L.injective),
    Set.ncard_image_of_injective _ (Projectivization.map_injective _ R.injective)]
  exact congrArg₂ (·+·) a.count b.count

/-- Place the two partial arrays in disjoint coordinate subspaces. -/
theorem join {u v cu cv : ℕ} [NeZero (u+v)] (mask : Cell (u+v) → Bool)
    (a : PartialArray (u+v) u cu mask) (b : PartialArray (u+v) v cv (fun p => !(mask p))) :
    Realized (u+v) (cu+cv) := by
  let L := LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.castAddEmb v (n:=u))
  let R := LinearIsometry.piLpExtendByZero 2 ℂ ℂ (Fin.natAddEmb u (m:=v))
  apply joinWith mask a b L R
  intro x y
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val < u
  · have hR : i ∉ Set.range (Fin.natAddEmb u (m:=v)) := by
      rintro ⟨j,rfl⟩
      change u + j.val < u at h
      omega
    have hz : R y i = 0 := LinearIsometry.piLpExtendByZero_apply_eq_zero hR y
    change R y i * (starRingEnd ℂ) (L x i) = 0
    rw [hz,zero_mul]
  · have hL : i ∉ Set.range (Fin.castAddEmb v (n:=u)) := by
      rintro ⟨j,rfl⟩
      exact h j.isLt
    have hz : L x i = 0 := LinearIsometry.piLpExtendByZero_apply_eq_zero hL x
    change R y i * (starRingEnd ℂ) (L x i) = 0
    simp [hz]

end PartialArray
end QuantumCertificate
