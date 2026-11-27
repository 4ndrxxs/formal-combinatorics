module
public import Quantum.FractionalLCSPGroup

/-! Exact modular solvability for translates of a prime-size seed on a p-group
times a group of order coprime to p. -/
@[expose] public section
noncomputable section
namespace TransitiveLCS
open Finset
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {P H : Type*} [Group P] [Fintype P] [Group H] [Fintype H]

def offsets (a : Fin p → P) : (P→ZMod p) →ₗ[ZMod p] (P→ZMod p) where
  toFun x g := ∑ i, x (g*a i)
  map_add' x y := by funext g; simp [Finset.sum_add_distrib]
  map_smul' u x := by funext g; simp [Finset.mul_sum]

theorem offsets_solvable (gp : IsPGroup p P) (a : Fin p→P) (h : ∃ i j, a i ≠ a j) :
    ∃ x : P→ZMod p, ∀ g, ∑ i, x (g*a i) = 1 := by
  classical
  obtain ⟨i,j,hij⟩ := h
  let L := offsets (p:=p) a
  let T := (univ : Finset (Fin p)).filter fun k => a k=a i
  have hi : i∈T := by simp [T]
  have hj : j∉T := by simpa [T] using hij.symm
  have hl : T.card < p := by
    have hsub : T ⊂ univ := Finset.ssubset_iff_of_subset (subset_univ _) |>.mpr ⟨j,mem_univ _,hj⟩
    simpa using Finset.card_lt_card hsub
  have hp0 : 0<T.card := card_pos.mpr ⟨_,hi⟩
  have hc : (T.card:ZMod p)≠0 := by
    intro h0
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp h0
    exact (not_le_of_gt hl) (Nat.le_of_dvd hp0 hd)
  let f (t : P) : ZMod p := if t=a i then 1 else 0
  have h1 : L f 1 = (T.card:ZMod p) := by
    change (∑ k, f (1*a k))=_
    simp [f,T,Finset.sum_boole]
  have nz : ∃ x ∈ LinearMap.range L, x ≠0 := by
    refine ⟨L f,⟨f,rfl⟩,fun h0 => hc ?_⟩
    rw [← h1,h0]
    rfl
  have st (g : P) (x : P→ZMod p) (hx : x∈LinearMap.range L) :
      pull g x∈LinearMap.range L := by
    obtain ⟨f,rfl⟩ := hx
    refine ⟨fun t => f (g⁻¹*t),?_⟩
    funext u
    change (∑ i, f (g⁻¹*(u*a i)))=∑ i,f ((g⁻¹*u)*a i)
    simp [mul_assoc]
  obtain ⟨x,hx⟩ := ones_mem_of_pgroup gp (LinearMap.range L) nz st
  exact ⟨x,fun g => congrFun hx g⟩

/-- If a prime-sized seed is translated through P × H with P a p-group and
p not dividing the order of H, then the binary-incidence summation equations
are inconsistent precisely when all its P-coordinates agree. Repetitions
in the seed are permitted and counted with their multiplicity. -/
theorem product_offsets_iff (gp : IsPGroup p P) (hc : (Fintype.card H:ZMod p)≠0)
    (a : Fin p → P) (b : Fin p → H) :
    (∃ x : P×H→ZMod p, ∀ g h, (∑ i, x (g*a i,h*b i))=1) ↔ ∃ i j, a i ≠ a j := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    by_contra! h
    have row (s : H) : (∑ i, x (a 0,s*b i)) = 1 := by
      simpa [h _ 0] using hx 1 s
    have col (i : Fin p) : (∑ s, x (a 0,s*b i)) = ∑ s, x (a 0,s) :=
      Equiv.sum_comp (Equiv.mulRight (b i)) (fun s => x (a 0,s))
    have hh := Finset.sum_congr (s₁:=univ) rfl (fun s _ => row s)
    rw [sum_comm] at hh
    simp_rw [col] at hh
    exact hc (by simpa [nsmul_eq_mul] using hh.symm)
  · intro h
    obtain ⟨x,hx⟩ := offsets_solvable gp a h
    exact ⟨fun t => x t.1, fun g _ => hx g⟩

#print axioms product_offsets_iff
end TransitiveLCS

