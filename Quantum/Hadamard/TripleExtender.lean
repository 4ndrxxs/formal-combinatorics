import Quantum.Hadamard.ArithmeticCompositeSteps
import Quantum.Hadamard.PowerConference

/-! At an arbitrary odd modulus a Brouwer extender exists at every class whose
difference from two is a unit. A dense set of positive half-orders suffices. -/
noncomputable section
namespace HadamardMod
open Hadamard.PG Hadamard.Arithmetic

theorem brouwer_odd_class {m:ℕ} (mp : 0 < m) (om : (2:ℕ).Coprime m)
    {r:ZMod m} (hr : IsUnit (r-2)) :
    ∃ v>1, Nonempty (Extender m (Fin v) r) := by
  have ut : IsUnit (2:ZMod m) := by simpa using (ZMod.isUnit_iff_coprime 2 m).mpr om
  obtain ⟨Q,big,qp,hq,q4⟩ := realize_unit_prime mp om (ut.mul hr.unit⁻¹.isUnit) 3 (by decide) 2
  have cq : Q.Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (hq ▸ ut.mul hr.unit⁻¹.isUnit)
  have mulr : (Q:ZMod m)*(r-2)=2 := calc
    _ = (Q:ZMod m)*↑hr.unit := congrArg ((Q:ZMod m)*·) hr.unit_spec.symm
    _ = 2 := by rw [hq,mul_assoc]; simp
  obtain ⟨d,zero,power⟩ := geom_period mp cq
  letI : Fact Q.Prime := ⟨qp⟩
  obtain ⟨D⟩ := Hadamard.Brouwer.extender (n := d) (m := m) q4 (by rw [zero,mul_zero])
  have eq : 2*((Q:ZMod m)+1)*Q^(d+1)=r := by
    rw [show d+2=d+1+1 by omega,pow_succ] at power
    linear_combination r*power-(Q:ZMod m)^(d+1)*mulr
  refine ⟨_,?_,⟨eq ▸ D⟩⟩
  rw [show d+2=d+1+1 by omega,geom_succ]
  exact Nat.lt_add_of_pos_right (by positivity)

theorem large_double_from_seeds {b w:ℕ} {I:Type} [Fintype I]
    (D : Extender b I ((2*w:ℕ):ZMod b)) (large : 1<Fintype.card I)
    (seeds : ∀ a, 0<a → b∣a → ∀ t, t ≡ w [MOD b] →
        ∃ h>0, AtOrder b (2*h) ∧ h ≡ t [MOD a]) :
    ∃ N, ∀ t ≥ N, t ≡ w [MOD b] → AtOrder b (2*t) := by
  classical
  let a := Fintype.card I-1
  have ap : 0<a := by dsimp [a]; omega
  have ba : b∣a := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    dsimp [a]
    rw [Nat.cast_sub (by omega),Nat.cast_one,D.dim,sub_self]
  have cls (i:Fin a) : ∃ B, ∀ t ≥ B, t ≡ i.val [MOD a] → t ≡ w [MOD b] → AtOrder b (2*t) := by
    by_cases good : i.val ≡ w [MOD b]
    · obtain ⟨h,pos,H,hi⟩ := seeds a ap ba i.val good
      refine ⟨h,?_⟩
      intro t big ti _
      obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' big).mp (hi.trans ti.symm)
      have res := (ZMod.natCast_eq_natCast_iff _ _ b).mpr (((hi.of_dvd ba).trans good).mul_left 2)
      have reached := D.iterate (by omega : 0<2*h) H res (2*j)
      change AtOrder b (2*h+2*j*a) at reached
      have eq : t=h+a*j := by omega
      rwa [eq,show 2*(h+a*j)=2*h+2*j*a by ring]
    · exact ⟨0,fun _ _ ti tw => (good ((ti.of_dvd ba).symm.trans tw)).elim⟩
  choose B spec using cls
  refine ⟨Finset.univ.sup B,?_⟩
  intro t big tw
  let i : Fin a := ⟨t%a,Nat.mod_lt _ ap⟩
  exact spec i t ((Finset.le_sup (f:=B) (Finset.mem_univ i)).trans big) (Nat.mod_modEq t a).symm tw

#print axioms large_double_from_seeds
end HadamardMod
