module

public import Quantum.EvenSpectrum
public import Quantum.UniversalPuncture

/-! The two possible lower-dimensional components of the odd block construction. -/
@[expose] public section
namespace QuantumCertificate.Odd
open IndexedArray

abbrev Index (m : ℕ) := Fin m ⊕ Fin (m+1)
abbrev vMask (m : ℕ) : Index m × Index m → Bool :=
  cornerMask (fun _ => true) (fun p => p.1 != p.2)

private def label {m : ℕ} [NeZero m] (i j : Fin (m+1)) : Fin m :=
  if h : j = i then 0 else (j-i).pred (sub_ne_zero.mpr h)

private theorem label_succ {m : ℕ} [NeZero m] {i j : Fin (m+1)} (h : j ≠ i) :
    (label i j).succ = j-i := by simp [label,h]

private theorem row_inj {m : ℕ} [NeZero m] {i j k : Fin (m+1)}
    (hj : (i != j) = true) (hk : (i != k) = true) (hn : j ≠ k) :
    label i j ≠ label i k := by
  intro he
  have e := congrArg Fin.succ he
  rw [label_succ (by simpa [ne_comm] using hj),
    label_succ (by simpa [ne_comm] using hk)] at e
  exact hn (sub_left_inj.mp e)

private theorem col_inj {m : ℕ} [NeZero m] {i j k : Fin (m+1)}
    (hj : (j != i) = true) (hk : (k != i) = true) (hn : j ≠ k) :
    label j i ≠ label k i := by
  intro he
  have e := congrArg Fin.succ he
  rw [label_succ (by simpa [ne_comm] using hj),
    label_succ (by simpa [ne_comm] using hk)] at e
  exact hn (sub_right_inj.mp e)

private def repeatFirst {m : ℕ} [NeZero m] (a : Full m) :
    IndexedArray m (fun p : Cell (m+1) => p.1 != p.2) where
  entry p := a.entry (0,label p.1 p.2)
  nz _ := a.nz ⟨_,rfl⟩
  unit _ := a.unit ⟨_,rfl⟩
  rows _ _ _ hj hk hn := a.rows 0 _ _ rfl rfl (row_inj hj hk hn)
  cols _ _ _ hj hk hn := a.rows 0 _ _ rfl rfl (col_inj hj hk hn)

theorem lower_small {m c : ℕ} [NeZero m] (h : Realized m c) :
    ∃ v : IndexedArray m (vMask m), v.rays.ncard = c := by
  obtain ⟨top⟩ := h.toPartial
  let a : Full m := ofPartial top
  have hs : (repeatFirst a).rays ⊆ a.rays := by
    rintro _ ⟨p,rfl⟩
    exact ⟨⟨(0,label p.val.1 p.val.2),rfl⟩,rfl⟩
  refine ⟨a.corners (repeatFirst a),?_⟩
  rw [rays_corners,Set.union_eq_self_of_subset_right hs]
  exact top.count

theorem lower_large {m c : ℕ} (hm : 4 ≤ m) (h : Realized m c) :
    ∃ v : IndexedArray m (vMask m), v.rays.ncard = c+(m+1)*m := by
  obtain ⟨top⟩ := h.toPartial
  let i : Fin m := ⟨0,by omega⟩
  let : Nonempty (Used (fun _ : Cell m => true)) := ⟨⟨(i,i),rfl⟩⟩
  obtain ⟨bottom⟩ := UniversalPuncture.universal_puncture (m+1) (by omega)
  have bot : PartialArray (m+1) m ((m+1)*m) (fun p => p.1 != p.2) := bottom
  obtain ⟨a,hd⟩ := top.exists_disjoint_copy (by omega) bot.rays bot.rays_finite
  refine ⟨(ofPartial a).corners (ofPartial bot),?_⟩
  rw [rays_corners,rays_ofPartial,rays_ofPartial,
    Set.ncard_union_eq hd a.rays_finite bot.rays_finite,
    show a.rays.ncard = c from a.count,show bot.rays.ncard = (m+1)*m from bot.count]

end QuantumCertificate.Odd
