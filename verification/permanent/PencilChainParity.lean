import PencilChainGenerators
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.Algebra.Polynomial.FieldDivision

/-! A polynomial chain frame of degree indivisible by its chain length
must lose maximal rank over a residue field. -/

noncomputable section
open Polynomial Matrix Finset UniqueFactorizationMonoid
namespace PencilChain
variable {K k : Type*} [Field K] [Fintype k] [DecidableEq k]

open scoped Classical in
private theorem bad_factor {s : ℕ} {D : K[X]} (nz : D ≠ 0) (bad : ¬s ∣ D.natDegree) :
    ∃ p : K[X], Irreducible p ∧ p.Monic ∧ p ∣ D ∧ ¬s ∣ factorization D p := by
  classical
  by_contra! all
  apply bad
  rw [←D.sum_natDegree_normalizedFactors,Finset.sum_multiset_map_count]
  apply Finset.dvd_sum
  intro p hp
  obtain ⟨irr,mon,pdvd⟩ := (Polynomial.mem_normalizedFactors_iff nz).mp (Multiset.mem_toFinset.mp hp)
  simpa only [smul_eq_mul,←factorization_eq_count] using
    dvd_mul_of_dvd_left (all p irr mon pdvd) p.natDegree

open scoped Classical in
private theorem valuation_ratio {s : ℕ} {D E p : K[X]} (dz : D ≠ 0) (ez : E ≠ 0)
    (avoid : ¬p ∣ E) (q : RatFunc K)
    (ratio : algebraMap K[X] (RatFunc K) E =
      algebraMap K[X] (RatFunc K) D * q^s) : s ∣ factorization D p := by
  classical
  let f := algebraMap K[X] (RatFunc K)
  have inj : Function.Injective f := IsFractionRing.injective _ _
  have den : q.denom ≠ 0 := q.denom_ne_zero
  have fn : f q.denom ≠ 0 := (map_ne_zero_iff f inj).mpr den
  have scaled : E * q.denom^s = D * q.num^s := by
    apply inj
    change f E = f D * q^s at ratio
    rw [←q.num_div_denom,div_pow,←mul_div_assoc] at ratio
    simpa only [map_mul,map_pow] using (eq_div_iff (pow_ne_zero _ fn)).mp ratio
  have numer : q.num^s ≠ 0 := by
    intro h
    rw [h,mul_zero] at scaled
    exact (mul_ne_zero ez (pow_ne_zero _ den)) scaled
  have outside : factorization E p = 0 := by
    rw [factorization_eq_count,Multiset.count_eq_zero]
    intro h
    exact avoid ((Polynomial.mem_normalizedFactors_iff ez).mp h).2.2
  have eq := congrArg (fun a : K[X] ↦ factorization a p) scaled
  simp only [factorization_mul ez (pow_ne_zero _ den),factorization_mul dz numer,
    factorization_pow,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,outside,zero_add] at eq
  have hd : s ∣ factorization D p + s * factorization q.num p := eq ▸ dvd_mul_right s _
  exact (Nat.dvd_add_iff_left (dvd_mul_right s _)).mpr hd

omit [Fintype k] [DecidableEq k] in
theorem frame_map {R S n : Type*} [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]
    (s : ℕ) (f : R →+* S) (A : Matrix n n R) (V : Matrix n k R) :
    (frame s A V).map f = frame s (A.map f) (V.map f) := by
  ext i j
  change f ((A^j.1.val*V) i j.2) = (((A.map f)^j.1.val)*(V.map f)) i j.2
  have prod : (A^j.1.val*V).map f = (A^j.1.val).map f * V.map f := Matrix.map_mul
  have power : (A^j.1.val).map f = (A.map f)^j.1.val := map_pow f.mapMatrix A _
  exact congrFun (congrFun (prod.trans (congrArg (fun B ↦ B * V.map f) power)) i) j.2

theorem residue_rank_drop {s : ℕ} (length : s=2 ∨ s=4)
    (A : Matrix (Fin s × k) (Fin s × k) K[X]) (nil : A^s=0)
    (V : Matrix (Fin s × k) k K[X]) (nz : (frame s A V).det ≠ 0)
    (bad : ¬s ∣ (frame s A V).det.natDegree) :
    ∃ p : K[X], ∃ hp : Irreducible p, p ∣ (frame s A V).det ∧ (let _ := Fact.mk hp
      ((A.map (AdjoinRoot.mk p))^(s-1)).rank ≠ Fintype.card k) := by
  classical
  let D := (frame s A V).det
  obtain ⟨p,hp,_,pdvd,hbad⟩ := bad_factor nz bad
  refine ⟨p,hp,pdvd,?_⟩
  let _ : Fact (Irreducible p) := ⟨hp⟩
  change ((A.map (AdjoinRoot.mk p))^(s-1)).rank ≠ Fintype.card k
  intro full
  let f := AdjoinRoot.mk p
  have fnil : (A.map f)^s = 0 := by
    change (f.mapMatrix A)^s=0
    rw [←map_pow,nil,map_zero]
  obtain ⟨W,fw⟩ := exists_full_frame length (A.map f) fnil full
  choose lift hLift using (AdjoinRoot.mk_surjective (g:=p))
  let U : Matrix (Fin s × k) k K[X] := fun i j ↦ lift (W i j)
  have wu : U.map f = W := by ext i j; exact hLift _
  let E := (frame s A U).det
  have fe : f E ≠ 0 := by
    change f (frame s A U).det ≠ 0
    rw [f.map_det]
    change ((frame s A U).map f).det ≠ 0
    rw [frame_map,wu]
    exact fw
  have ez : E ≠ 0 := fun h ↦ fe (by rw [h,map_zero])
  have avoid : ¬p ∣ E := fun h ↦ fe (AdjoinRoot.mk_eq_zero.mpr h)
  let g := algebraMap K[X] (RatFunc K)
  have gn : (A.map g)^s=0 := by
    change (g.mapMatrix A)^s=0
    rw [←map_pow,nil,map_zero]
  have cv (T : Matrix (Fin s × k) k K[X]) :
      g (frame s A T).det = (frame s (A.map g) (T.map g)).det := by
    rw [g.map_det]
    exact congrArg Matrix.det (frame_map s g A T)
  have gd : g D ≠ 0 := (map_ne_zero_iff g (IsFractionRing.injective _ _)).mpr nz
  rw [show g D = _ from cv V] at gd
  obtain ⟨a,ratio⟩ := det_ratio length (A.map g) gn (V.map g) (U.map g) gd
  apply hbad
  apply valuation_ratio nz ez avoid a
  change g (frame s A U).det = g (frame s A V).det * a^s
  simpa only [cv] using ratio

#print axioms residue_rank_drop
end PencilChain
