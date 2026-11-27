module

public import Quantum.OddUpperLayout
public import Quantum.BasedPairs

/-! Odd orders follow from the two neighboring approximately half-sized orders. -/
@[expose] public section
namespace QuantumCertificate

private def BasedSquare.asFull {n c : ℕ} [NeZero n] (b : BasedSquare n c) : Full n where
  entry p := b.entry p.1 p.2
  nz p := b.nz _ _
  unit p := by
    obtain ⟨v,hv⟩ := b.rows p.val.1
    rw [← hv]
    exact v.orthonormal.1 _
  rows i j k _ _ hn := by
    obtain ⟨v,hv⟩ := b.rows i
    simp [← hv,v.inner_eq_ite,hn]
  cols i j k _ _ hn := by
    obtain ⟨v,hv⟩ := b.cols i
    change inner ℂ (b.entry j i) (b.entry k i) = 0
    rw [← congrFun hv j,← congrFun hv k]
    simp [v.inner_eq_ite,hn]

private theorem BasedSquare.rays_asFull {n c : ℕ} [NeZero n] (b : BasedSquare n c) :
    b.asFull.rays = b.rays := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p.val,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨⟨p,rfl⟩,rfl⟩

namespace Odd

theorem upper_all {m : ℕ} (hm : 3 ≤ m) (good : Good (m+1)) (c : ℕ)
    (lo : m+1 ≤ c) (hi : c+(m+1) ≤ 2*((m+1)*(m+1))) (hole : c ≠ (m+1)+1) :
    ∃ u : IndexedArray (m+1) (uMask m), u.rays.ncard = c := by
  by_cases small : c ≤ (m+1)*(m+1)
  · obtain ⟨a⟩ := (good c lo small hole).based
    refine ⟨upper a.asFull a.asFull (fun _ => rfl),?_⟩
    rw [rays_upper,Set.union_self,a.rays_asFull,a.ncard_rays]
  have width : (m+1)+(m+1)+2 ≤ (m+1)*(m+1) := by nlinarith
  obtain ⟨x,y,lx,hx,ex,ly,hy,ey,hxy⟩ :=
    add_punctured_intervals (l:=m+1) (u:=(m+1)*(m+1)) (z:=c+(m+1))
      (by omega) (by omega) (by omega) (by omega)
  obtain ⟨a,b,hab⟩ := based_pair (by omega : 2 ≤ m+1) (good _ lx hx ex) (good _ ly hy ey)
  have h₀ (i : Fin (m+1)) : b.asFull.entry (0,i) = a.asFull.entry (0,i) :=
    (b.first i).trans (a.first i).symm
  refine ⟨upper a.asFull b.asFull h₀,?_⟩
  rw [rays_upper,a.rays_asFull,b.rays_asFull]
  have ha : a.rays.Finite := Set.finite_range _
  have hb : b.rays.Finite := Set.finite_range _
  have eq := Set.ncard_union_add_ncard_inter a.rays b.rays ha hb
  rw [hab,ncard_coordinateRays,a.ncard_rays,b.ncard_rays] at eq
  omega

theorem joint {m u v : ℕ} (hm : 1 ≤ m)
    (hu : ∃ a : IndexedArray (m+1) (uMask m), a.rays.ncard = u)
    (hv : ∃ b : IndexedArray m (vMask m), b.rays.ncard = v) : Realized ((m+1)+m) (u+v) := by
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := hv
  have mask : vMask m = fun p => !uMask m p := by funext p; simp [uMask]
  let : NeZero ((m+1)+m) := ⟨by omega⟩
  have h := IndexedArray.join a (b.changeMask mask) (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))
  simpa only [IndexedArray.rays_changeMask,ha,hb] using h

end Odd

theorem Good.odd {m : ℕ} (h : Good m) (hnext : Good (m+1)) (hm : 4 ≤ m) :
    Good ((m+1)+m) := by
  intro c lo hi hole
  let : NeZero m := ⟨by omega⟩
  have mSq : m+2 ≤ m*m := by nlinarith [Nat.mul_self_le_mul_self hm]
  have a₀ : Realized m m := h m (by omega) (by omega) (by omega)
  have a₁ : Realized m (m*m) := h (m*m) (by omega) le_rfl (by omega)
  have hmax : ((m+1)+m)*((m+1)+m) = 4*(m*m)+4*m+1 := by ring
  have hu : 2*((m+1)*(m+1)) = 2*(m*m)+4*m+2 := by ring
  have hv : m*m+(m+1)*m = 2*(m*m)+m := by ring
  by_cases low : c ≤ 2*(m*m)+4*m+1
  · have u := Odd.upper_all (by omega) hnext (c-m) (by omega) (by omega) (by omega)
    have joined := Odd.joint (by omega) u (Odd.lower_small a₀)
    rwa [show c-m+m=c by omega] at joined
  · let v := m*m+(m+1)*m
    have veq : v=2*(m*m)+m := hv
    have u := Odd.upper_all (by omega) hnext (c-v) (by omega) (by omega) (by omega)
    have joined := Odd.joint (by omega) u (Odd.lower_large hm a₁)
    change Realized ((m+1)+m) (c-v+v) at joined
    rwa [show c-v+v=c by omega] at joined

#print axioms Good.odd
end QuantumCertificate
