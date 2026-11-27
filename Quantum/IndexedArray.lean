module

public import Quantum.PartialIsometry

/-! Partial arrays indexed by arbitrary finite sets. Sum-type index sets
make block placement and the proof of its row and column conditions explicit. -/
@[expose] public section
namespace QuantumCertificate

abbrev Sites {I : Type*} (mask : I × I → Bool) := {p : I × I // mask p = true}

structure IndexedArray {I : Type*} (d : ℕ) (mask : I × I → Bool) where
  entry : I × I → Space d
  nz : ∀ p : Sites mask, entry p.val ≠ 0
  unit : ∀ p : Sites mask, ‖entry p.val‖ = 1
  rows : ∀ i j k, mask (i,j) = true → mask (i,k) = true → j ≠ k →
    inner ℂ (entry (i,j)) (entry (i,k)) = 0
  cols : ∀ i j k, mask (j,i) = true → mask (k,i) = true → j ≠ k →
    inner ℂ (entry (j,i)) (entry (k,i)) = 0

namespace IndexedArray

variable {I J : Type*} {d c : ℕ} {mask : I × I → Bool}

noncomputable def rays (a : IndexedArray d mask) :=
  rayRange (fun p : Sites mask => a.entry p.val) a.nz

theorem rays_finite [Finite I] (a : IndexedArray d mask) : a.rays.Finite := Set.finite_range _

def changeMask {other : I × I → Bool} (a : IndexedArray d mask) (h : mask = other) :
    IndexedArray d other := h ▸ a

@[simp] theorem rays_changeMask {other : I × I → Bool} (a : IndexedArray d mask)
    (h : mask = other) : (a.changeMask h).rays = a.rays := by
  subst other
  rfl

def ofPartial {n : ℕ} {m : Cell n → Bool} (a : PartialArray n d c m) : IndexedArray d m :=
  ⟨a.entry,a.nz,a.unit,a.rows,a.cols⟩

@[simp] theorem rays_ofPartial {n : ℕ} {m : Cell n → Bool} (a : PartialArray n d c m) :
    (ofPartial a).rays = a.rays := rfl

def reindex (a : IndexedArray d mask) (e f : J ≃ I) :
    IndexedArray d (fun p : J × J => mask (e p.1,f p.2)) where
  entry p := a.entry (e p.1,f p.2)
  nz p := a.nz ⟨_,p.property⟩
  unit p := a.unit ⟨_,p.property⟩
  rows i j k hj hk hn := a.rows (e i) (f j) (f k) hj hk (f.injective.ne hn)
  cols i j k hj hk hn := a.cols (f i) (e j) (e k) hj hk (e.injective.ne hn)

@[simp] theorem rays_reindex (a : IndexedArray d mask) (e f : J ≃ I) :
    (a.reindex e f).rays = a.rays := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨⟨_,p.property⟩,rfl⟩
  · rintro ⟨⟨⟨i,j⟩,hp⟩,rfl⟩
    refine ⟨⟨(e.symm i,f.symm j),?_⟩,?_⟩
    · simpa using hp
    · apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      exact ⟨1, by simp [reindex]⟩

noncomputable def toPartial {n : ℕ} (a : IndexedArray d mask) (e : Fin n ≃ I) :
    PartialArray n d a.rays.ncard (fun p => mask (e p.1,e p.2)) where
  entry := (a.reindex e e).entry
  nz := (a.reindex e e).nz
  unit := (a.reindex e e).unit
  rows := (a.reindex e e).rows
  cols := (a.reindex e e).cols
  count := congrArg Set.ncard (a.rays_reindex e e)

def cornerMask (left : I × I → Bool) (right : J × J → Bool) : (I ⊕ J) × (I ⊕ J) → Bool
  | (.inl i,.inl j) => left (i,j)
  | (.inr i,.inr j) => right (i,j)
  | _ => false

def corners {left : I × I → Bool} {right : J × J → Bool}
    (a : IndexedArray d left) (b : IndexedArray d right) :
    IndexedArray d (cornerMask left right) where
  entry
    | (.inl i,.inl j) => a.entry (i,j)
    | (.inr i,.inr j) => b.entry (i,j)
    | _ => 0
  nz := by
    rintro ⟨⟨i,j⟩,h⟩
    cases i <;> cases j <;> first | exact a.nz ⟨_,h⟩ | exact b.nz ⟨_,h⟩ | contradiction
  unit := by
    rintro ⟨⟨i,j⟩,h⟩
    cases i <;> cases j <;> first | exact a.unit ⟨_,h⟩ | exact b.unit ⟨_,h⟩ | contradiction
  rows := by
    rintro (i|i) (j|j) (k|k) hj hk h <;>
      first | exact a.rows i j k hj hk (fun he => h (congrArg Sum.inl he))
            | exact b.rows i j k hj hk (fun he => h (congrArg Sum.inr he))
            | contradiction
  cols := by
    rintro (i|i) (j|j) (k|k) hj hk h <;>
      first | exact a.cols i j k hj hk (fun he => h (congrArg Sum.inl he))
            | exact b.cols i j k hj hk (fun he => h (congrArg Sum.inr he))
            | contradiction

theorem rays_corners {left : I × I → Bool} {right : J × J → Bool}
    (a : IndexedArray d left) (b : IndexedArray d right) :
    (a.corners b).rays = a.rays ∪ b.rays := by
  ext z
  constructor
  · rintro ⟨⟨⟨i,j⟩,h⟩,rfl⟩
    cases i <;> cases j
    · exact Or.inl ⟨⟨_,h⟩,rfl⟩
    · contradiction
    · contradiction
    · exact Or.inr ⟨⟨_,h⟩,rfl⟩
  · rintro (⟨⟨⟨i,j⟩,h⟩,rfl⟩|⟨⟨⟨i,j⟩,h⟩,rfl⟩)
    · exact ⟨⟨(.inl i,.inl j),h⟩,rfl⟩
    · exact ⟨⟨(.inr i,.inr j),h⟩,rfl⟩

theorem join {u v : ℕ} [NeZero (u+v)] (a : IndexedArray u mask)
    (b : IndexedArray v (fun p => !mask p)) (e : Fin (u+v) ≃ I) :
    Realized (u+v) (a.rays.ncard+b.rays.ncard) :=
  PartialArray.join _ (a.toPartial e) (b.toPartial e)

end IndexedArray
end QuantumCertificate
