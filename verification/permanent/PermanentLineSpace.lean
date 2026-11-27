import PermanentFive
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.CharZero.Infinite

/-! A five-dimensional space of matrices on which every two-by-two permanent
vanishes is the space supported on a single complete row or column. -/

noncomputable section
open Finset Module
namespace PermanentFive
variable {K : Type*} [Field K] [CharZero K]

def AllTwoZero (z : Cell → K) : Prop :=
  ∀ r s i j : Idx, r ≠ s → i ≠ j → z (r,i)*z (s,j) + z (r,j)*z (s,i) = 0

private theorem third_zero (a b c d x y : K) (a0 : a ≠ 0) (b0 : b ≠ 0) (c0 : c ≠ 0)
    (ab : a*d+b*c=0) (ax : a*y+x*c=0) (bx : b*y+x*d=0) : x=0 ∧ y=0 := by
  have h : 2 * b * c * x = 0 := by linear_combination b*ax - a*bx + x*ab
  have ex : x = 0 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) b0) c0)
  rw [ex,zero_mul,add_zero] at ax
  exact ⟨ex,(mul_eq_zero.mp ax).resolve_left a0⟩

private theorem rectangle_support (z : Cell → K) (van : AllTwoZero z) (r s i j : Idx)
    (rs : r ≠ s) (ij : i ≠ j) (a : z (r,i) ≠ 0) (d : z (s,j) ≠ 0) :
    ∀ x : Cell, z x ≠ 0 → x ∈ ({(r,i),(r,j),(s,i),(s,j)} : Finset Cell) := by
  have eq := van r s i j rs ij
  have bc : z (r,j)*z (s,i) ≠ 0 := by
    intro zero
    rw [zero,add_zero] at eq
    exact mul_ne_zero a d eq
  have b := (mul_ne_zero_iff.mp bc).1
  have c := (mul_ne_zero_iff.mp bc).2
  have outsideCol (k : Idx) (ki : k ≠ i) (kj : k ≠ j) : z (r,k)=0 ∧ z (s,k)=0 :=
    third_zero _ _ _ _ _ _ a b c eq (van r s i k rs ki.symm) (van r s j k rs kj.symm)
  have outsideRow (t : Idx) (tr : t ≠ r) (ts : t ≠ s) : z (t,i)=0 ∧ z (t,j)=0 :=
    third_zero (z (r,i)) (z (s,i)) (z (r,j)) (z (s,j)) (z (t,i)) (z (t,j)) a c b
      (by linear_combination eq)
      (by linear_combination van r t i j tr.symm ij) (by linear_combination van s t i j ts.symm ij)
  rintro ⟨t,k⟩ nz
  by_cases tr : t = r
  · subst t
    by_cases ki : k = i
    · simp [ki]
    by_cases kj : k = j
    · simp [kj]
    exact (nz (outsideCol k ki kj).1).elim
  by_cases ts : t = s
  · subst t
    by_cases ki : k = i
    · simp [ki]
    by_cases kj : k = j
    · simp [kj]
    exact (nz (outsideCol k ki kj).2).elim
  by_cases ki : k = i
  · exact (nz (ki ▸ (outsideRow t tr ts).1)).elim
  by_cases kj : k = j
  · exact (nz (kj ▸ (outsideRow t tr ts).2)).elim
  have corner := van r t i k (Ne.symm tr) (Ne.symm ki)
  rw [(outsideCol k ki kj).1,zero_mul,add_zero] at corner
  exact (mul_ne_zero a nz corner).elim

private theorem large_matrix_on_line (z : Cell → K) (van : AllTwoZero z)
    (S : Finset Cell) (nz : ∀ x ∈ S, z x ≠ 0) (five : 5 ≤ S.card) :
    (∃ r : Idx, ∀ x ∈ S, x.1 = r) ∨ (∃ c : Idx, ∀ x ∈ S, x.2 = c) := by
  classical
  have meet (a b : Cell) (ha : a ∈ S) (hb : b ∈ S) : a.1=b.1 ∨ a.2=b.2 := by
    by_contra! dis
    let R : Finset Cell := {(a.1,a.2),(a.1,b.2),(b.1,a.2),(b.1,b.2)}
    have sub : S ⊆ R := fun x hx ↦ rectangle_support z van _ _ _ _ dis.1 dis.2
      (nz a ha) (nz b hb) x (nz x hx)
    have bound := Finset.card_le_card sub
    have size : R.card ≤ 4 := by
      dsimp only [R]
      calc
        _ ≤ _ := Finset.card_insert_le _ _
        _ ≤ 4 := by
          have h := Finset.card_insert_le (a.1,b.2) ({(b.1,a.2),(b.1,b.2)} : Finset Cell)
          have h' := Finset.card_insert_le (b.1,a.2) ({(b.1,b.2)} : Finset Cell)
          simp only [Finset.card_singleton] at h'
          omega
    omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  by_cases row : ∀ x ∈ S, x.1 = a.1
  · exact Or.inl ⟨_,row⟩
  push Not at row
  obtain ⟨b,hb,ne⟩ := row
  have same := (meet b a hb ha).resolve_left ne
  refine Or.inr ⟨a.2,fun x hx ↦ ?_⟩
  by_contra nc
  exact ne ((meet x b hx hb).resolve_right (fun h ↦ nc (h.trans same)) |>.symm.trans
    ((meet x a hx ha).resolve_right nc))

private theorem simultaneously_nonzero (L : Submodule K (Cell → K)) (S : Finset Cell)
    (each : ∀ j ∈ S, ∃ u ∈ L, u j ≠ 0) : ∃ v ∈ L, ∀ j ∈ S, v j ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,L.zero_mem,by simp⟩
  | insert a S ha ih =>
    obtain ⟨u,hu,au⟩ := each a (Finset.mem_insert_self _ _)
    obtain ⟨v,hv,hS⟩ := ih (fun j hj ↦ each j (Finset.mem_insert_of_mem hj))
    let bad := (insert a S).image (fun j ↦ -v j / u j)
    obtain ⟨t,out⟩ := Infinite.exists_notMem_finset bad
    refine ⟨v+t•u,L.add_mem hv (L.smul_mem t hu),?_⟩
    intro j hj
    change v j + t*u j ≠ 0
    by_cases uj : u j = 0
    · have hj' : j ∈ S := (Finset.mem_insert.mp hj).resolve_left (fun h ↦ au (h ▸ uj))
      simpa [uj] using hS j hj'
    · intro zero
      have eq : t = -v j / u j := (eq_div_iff uj).mpr (by linear_combination zero)
      exact out (eq ▸ Finset.mem_image_of_mem _ hj)

theorem large_space_on_one_line (L : Submodule K (Cell → K)) (five : 5 ≤ finrank K L)
    (van : ∀ z ∈ L, AllTwoZero z) :
    (∃ r : Idx, ∀ z ∈ L, ∀ j : Cell, j.1 ≠ r → z j = 0) ∨
    (∃ c : Idx, ∀ z ∈ L, ∀ j : Cell, j.2 ≠ c → z j = 0) := by
  classical
  let S := Finset.univ.filter (fun j : Cell ↦ ∃ z ∈ L, z j ≠ 0)
  have membership (j : Cell) : j ∈ S ↔ ∃ z ∈ L, z j ≠ 0 := by simp [S]
  let res : L →ₗ[K] (S → K) :=
    { toFun := fun v i ↦ v.val i.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have inj : Function.Injective res := by
    apply (LinearMap.ker_eq_bot.mp ?_)
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    funext j
    by_contra ne
    have hj := (membership j).2 ⟨v.val,v.property,ne⟩
    exact ne (congrFun hv ⟨j,hj⟩)
  have size := LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_pi] at size
  obtain ⟨v,hv,full⟩ := simultaneously_nonzero L S (fun j hj ↦ (membership j).1 hj)
  obtain h | h := large_matrix_on_line v (van v hv) S full (by simpa using five.trans size)
  · obtain ⟨r,rows⟩ := h
    exact Or.inl ⟨r,fun z hz j ne ↦ by
      by_contra nz
      exact ne (rows j ((membership j).2 ⟨z,hz,nz⟩))⟩
  · obtain ⟨c,cols⟩ := h
    exact Or.inr ⟨c,fun z hz j ne ↦ by
      by_contra nz
      exact ne (cols j ((membership j).2 ⟨z,hz,nz⟩))⟩

#print axioms large_space_on_one_line
end PermanentFive
