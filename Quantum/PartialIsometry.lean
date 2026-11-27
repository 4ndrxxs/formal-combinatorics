module

public import Quantum.PartialArray
public import Quantum.Disjoint

@[expose] public section
namespace QuantumCertificate

theorem Realized.toPartial {n c : ℕ} (h : Realized n c) :
    Nonempty (PartialArray n n c (fun _ => true)) := by
  classical
  obtain ⟨v,vnz,rows,cols,hc⟩ := h
  have unit (p : Cell n) : ‖v p.1 p.2‖ = 1 := by
    obtain ⟨b,hb⟩ := rows p.1
    rw [← hb]
    exact b.orthonormal.1 _
  refine ⟨⟨fun p => v p.1 p.2, fun p => vnz _ _, fun p => unit _,
    fun i j k _ _ hne => ?_, fun i j k _ _ hne => ?_, ?_⟩⟩
  · obtain ⟨b,hb⟩ := rows i
    simp [← hb, b.inner_eq_ite, hne]
  · obtain ⟨b,hb⟩ := cols i
    have hj := congrFun hb j
    have hk := congrFun hb k
    change inner ℂ (v j i) (v k i) = 0
    rw [← hj, ← hk]
    simp [b.inner_eq_ite,hne]
  rw [← hc]
  apply congrArg Set.ncard
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p.val,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨⟨p,rfl⟩,rfl⟩

namespace PartialArray

variable {n d d' c : ℕ} {mask : Cell n → Bool}

noncomputable def mapIsometry (a : PartialArray n d c mask) (f : Space d →ₗᵢ[ℂ] Space d') :
    PartialArray n d' c mask where
  entry p := f (a.entry p)
  nz p := fun h => a.nz p (f.injective (h.trans (map_zero _).symm))
  unit p := (f.norm_map _).trans (a.unit p)
  rows i j k hj hk h := (f.inner_map_map _ _).trans (a.rows i j k hj hk h)
  cols i j k hj hk h := (f.inner_map_map _ _).trans (a.cols i j k hj hk h)
  count := by
    have he : rayRange (fun p : Used mask => f (a.entry p.val))
        (fun p h => a.nz p (f.injective (h.trans (map_zero _).symm))) =
        Projectivization.map f.toLinearMap f.injective '' a.rays := by
      ext z
      constructor
      · rintro ⟨p,rfl⟩
        exact ⟨_,⟨p,rfl⟩,rfl⟩
      · rintro ⟨_,⟨p,rfl⟩,rfl⟩
        exact ⟨p,rfl⟩
    rw [he,Set.ncard_image_of_injective _ (Projectivization.map_injective _ f.injective)]
    exact a.count

theorem exists_disjoint_copy (a : PartialArray n d c mask) [Nonempty (Used mask)]
    (hd : 2 ≤ d) (s : Set (Projectivization ℂ (Space d))) (hs : s.Finite) :
    ∃ a' : PartialArray n d c mask, Disjoint a'.rays s := by
  obtain ⟨f,hf⟩ := exists_isometry_avoiding hd (fun p : Used mask => a.entry p.val) a.nz s hs
  refine ⟨a.mapIsometry f,Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨p,rfl⟩ hmem
  exact hf p hmem

end PartialArray
end QuantumCertificate
