module
public import Quantum.OrbitPeriodic

/-! Finite criteria for forward and reverse reachability of rational point states. -/
@[expose] public section
noncomputable section
open Polynomial
namespace RationalOrbit

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def Reaches (T : Module.End ℚ V) (v w : V) := ∃ k : ℕ, (T^k) v=w
def Periodic (T : Module.End ℚ V) (v : V) := ∃ k : ℕ, 0<k ∧ (T^k) v=v

/-- This condition is a linear system on the first d orbit columns. -/
def InKrylov (T : Module.End ℚ V) (v : V) (d : ℕ) (w : V) :=
  ∃ P : ℚ[X], P.natDegree<d ∧ act T v P=w

theorem SourceEquation.ann {T : Module.End ℚ V} {v : V} {D : ℤ[X]}
    (h : SourceEquation T v D) : act T v (D.map castQ)=0 := (h.detects D).mpr dvd_rfl

theorem SourceEquation.unit_of_periodic {T : Module.End ℚ V} {v : V} {D : ℤ[X]}
    (h : SourceEquation T v D) (per : Periodic T v) : IsUnit D.leadingCoeff := by
  obtain ⟨k,hk,eq⟩ := per
  have div : D∣X^k-1 := (h.detects _).mp (by simp [act,eq])
  have ld := leadingCoeff_dvd_leadingCoeff div
  rw [(monic_X_pow_sub_one hk.ne').leadingCoeff] at ld
  exact isUnit_iff_dvd_one.mpr ld

theorem SourceEquation.periodic_iff_unit {E : Type*} [Fintype E]
    {T : Module.End ℚ (E → ℚ)} (hinj : Function.Injective T) {v : E → ℚ} {D : ℤ[X]}
    (h : SourceEquation T v D) (H : ℕ) (bound : ∀ k e, |(T^k) v e|≤H) :
    Periodic T v ↔ IsUnit D.leadingCoeff := by
  refine ⟨h.unit_of_periodic, fun u => ?_⟩
  rcases Int.isUnit_iff.mp u with hd | hd
  · exact periodic_of_monic T hinj v (Monic.def.mpr hd) h.ann H bound
  · have m : (-D).Monic := by simp [Monic.def,hd]
    exact periodic_of_monic T hinj v m (by simpa [act] using congrArg Neg.neg h.ann) H bound

theorem SourceEquation.positive_degree {T : Module.End ℚ V} {v : V} {D : ℤ[X]}
    (h : SourceEquation T v D) (nz : D≠0) (hv : v≠0) : 0<D.natDegree := by
  by_contra! hz
  have z : D.natDegree=0 := by omega
  have e := Polynomial.eq_C_of_natDegree_eq_zero z
  have nc : D.coeff 0≠0 := by intro hc; apply nz; rw [e,hc]; simp
  have nn : (D.coeff 0:ℚ)≠0 := by exact_mod_cast nc
  have a := h.ann
  conv at a => lhs; rw [e]
  have bad : castQ (D.coeff 0) • v=0 := by simpa only [act,Polynomial.map_C,aeval_C,Module.algebraMap_end_apply] using a
  have ncq : castQ (D.coeff 0)≠0 := by simpa [castQ] using nc
  exact (smul_ne_zero ncq hv) bad

theorem SourceEquation.in_krylov_of_reaches {T : Module.End ℚ V} {v w : V} {D : ℤ[X]}
    (h : SourceEquation T v D) (nz : D≠0) (hv : v≠0) (reaches : Reaches T v w) :
    InKrylov T v D.natDegree w := by
  obtain ⟨k,rfl⟩ := reaches
  let g := D.map castQ
  have deg : g.natDegree=D.natDegree := natDegree_map_eq_of_injective (by exact Rat.intCast_injective) _
  have pos := h.positive_degree nz hv
  let P := (X^k:ℚ[X]) % g
  let Q := (X^k:ℚ[X]) / g
  have eq := EuclideanDomain.mod_add_div (X^k:ℚ[X]) g
  change P+g*Q=_ at eq
  rw [mul_comm g Q] at eq
  have a : act T v g=0 := h.ann
  have annih : act T v (Q*g)=0 := by simpa [act,mul_apply_eq_comp] using congrArg (aeval T Q) a
  have full : act T v P+act T v (Q*g)=(T^k) v := by
    simpa [act] using congrArg (act T v) eq
  refine ⟨P, ?_, by rwa [annih,add_zero] at full⟩
  rw [← deg]
  exact natDegree_mod_lt _ (by omega)

theorem InKrylov.clear {T : Module.End ℚ V} {v w : V} {d : ℕ} (h : InKrylov T v d w) :
    ∃ A : ℤ, A≠0 ∧ ∃ P : ℤ[X], P.natDegree<d ∧ act T v (P.map castQ)=(A:ℚ) • w := by
  obtain ⟨Q,hQ,eq⟩ := h
  let P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q
  obtain ⟨A,hA,eqA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
  have an := mem_nonZeroDivisors_iff_ne_zero.mp hA
  have aq : (A:ℚ)≠0 := by exact_mod_cast an
  have mulQ : P.map castQ=C (A:ℚ)*Q := by simpa only [P,C_mul',Int.cast_smul_eq_zsmul] using eqA
  have dp : P.natDegree=(P.map castQ).natDegree :=
    (natDegree_map_eq_of_injective (by exact Rat.intCast_injective) _).symm
  refine ⟨A,an,P,?_,?_⟩
  · rw [dp,mulQ,natDegree_C_mul aq]
    exact hQ
  · rw [mulQ,← eq]
    simp only [act,map_mul,aeval_C,mul_apply_eq_comp,Module.algebraMap_end_apply]

theorem SourceEquation.prime_of_nonunit {T : Module.End ℚ V} {v : V} {D : ℤ[X]}
    (_h : SourceEquation T v D) (hn : ¬IsUnit D.leadingCoeff) :
    ∃ p : ℕ, p.Prime ∧ (p:ℤ)∣D.leadingCoeff := by
  have nn : D.leadingCoeff.natAbs≠1 := by
    intro em
    exact hn (Int.isUnit_iff.mpr (by simpa using Int.natAbs_eq_iff.mp em))
  obtain ⟨p,hp,div⟩ := Nat.exists_prime_and_dvd nn
  exact ⟨p,hp,Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr div)⟩

theorem SourceEquation.finite_hits {T : Module.End ℚ V} {v w : V} {D : ℤ[X]}
    (h : SourceEquation T v D) {p : ℕ} [Fact p.Prime] (hd : (p:ℤ)∣D.leadingCoeff)
    {A : ℤ} (ha : A≠0) {P : ℤ[X]} (target : act T v (P.map castQ)=(A:ℚ) • w) :
    Reaches T v w ↔ ∃ k ≤ P.natDegree+A.natAbs.factorization p*(D.natDegree-(D.map (red p)).natDegree), (T^k) v=w := by
  refine ⟨?_,fun ⟨k,_,hk⟩ => ⟨k,hk⟩⟩
  rintro ⟨k,hk⟩
  refine ⟨k,h.hit_bound_sharp hd A P target _ ?_ k hk,hk⟩
  intro dv
  have natd := Int.natAbs_dvd_natAbs.mpr dv
  simp only [Int.natAbs_pow,Int.natAbs_natCast] at natd
  exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr ha) (Fact.out : p.Prime) natd

theorem reaches_iff_before_return {T : Module.End ℚ V} {v w : V} {n : ℕ}
    (hn : 0<n) (period : (T^n) v=v) : Reaches T v w ↔ ∃ k<n, (T^k) v=w := by
  refine ⟨?_, fun ⟨k,_,h⟩ => ⟨k,h⟩⟩
  rintro ⟨k,rfl⟩
  have per : Function.IsPeriodicPt T n v := by simpa [Function.IsPeriodicPt,Function.IsFixedPt,pow_apply_eq_iterate] using period
  exact ⟨k%n,Nat.mod_lt _ hn,by simpa only [pow_apply_eq_iterate] using per.iterate_mod_apply k⟩

/-- For distinct states on a single orbit, reverse transfer is equivalent to periodicity. -/
theorem reverse_iff_periodic {T : Module.End ℚ V} {v w : V} (ne : v≠w) (fwd : Reaches T v w) :
    Reaches T w v ↔ Periodic T v := by
  obtain ⟨a,ha⟩ := fwd
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b+a,?_,by rw [pow_add,mul_apply_eq_comp,ha,hb]⟩
    have h0 : a≠0 := by rintro rfl; exact ne (by simpa using ha)
    omega
  · rintro ⟨t,ht,per⟩
    obtain ⟨r,lt,hr⟩ := (reaches_iff_before_return ht per).mp ⟨a,ha⟩
    refine ⟨t-r,?_⟩
    rw [← hr,← mul_apply_eq_comp,← pow_add,Nat.sub_add_cancel lt.le,per]

end RationalOrbit
