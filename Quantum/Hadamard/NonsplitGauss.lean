import Quantum.Hadamard.ProjectiveNonsplitTorus
import Quantum.Hadamard.LinPhoaJacobi
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Duality

/-! Fourier transform of the imaginary-coordinate sequence of the odd
norm-one torus. All Gauss sums use zero-extended multiplicative characters. -/

noncomputable section
open Finset Hadamard.ProjectiveSigning.Coordinates Hadamard.LinPhoa
namespace Hadamard.NonsplitTorus

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {d : F} [Fact (¬ IsSquare d)]

noncomputable local instance extFintype (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F×F) (QuadraticAlgebra.equivProd d 0).symm

private theorem sum_nonzero {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (f : K → ℂ) (zero : f 0=0) : (∑ u : Kˣ, f u)=∑ x : K, f x := by
  classical
  calc
    _ = ∑ x : {x : K // x≠0}, f x := Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ ↦ rfl)
    _ = _ := by
      rw [←sum_subtype (univ.erase 0) (by simp) f]
      simp [zero]

omit [Fintype F] [DecidableEq F] in
private theorem vector_nonzero (h : (Ext d)ˣ) (i : Bool×Fin (orderOf h)) : vector h i≠0 := by
  apply mul_ne_zero _ (pow_ne_zero _ h.ne_zero)
  rcases i with ⟨b,i⟩
  cases b
  · exact one_ne_zero
  · intro z
    exact one_ne_zero (congrArg QuadraticAlgebra.im z)

def scaledTorusUnit (h : (Ext d)ˣ) (v : (Bool×Fin (orderOf h))×Fˣ) : (Ext d)ˣ :=
  Units.mk0 (algebraMap F (Ext d) v.2*vector h v.1)
    (mul_ne_zero ((algebraMap F (Ext d)).injective.ne_iff.mpr v.2.ne_zero) (vector_nonzero h v.1))

/-- A nonzero extension-field element has a unique scalar and projective torus coordinate. -/
theorem scalar_torus_bijective (q4 : Fintype.card F%4=1) (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) :
    Function.Bijective (scaledTorusUnit h) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro u
    obtain ⟨i,hi⟩ := (projective_chart_bijective q4 hm h ho hn).2
      (point (u:Ext d).re (u:Ext d).im)
    obtain ⟨r,hnz,hr⟩ := scalar_of_point_eq u.ne_zero (vector_nonzero h i) hi.symm
    exact ⟨(i,Units.mk0 r hnz),Units.ext hr.symm⟩
  · have fc := Fintype.card_congr (QuadraticAlgebra.equivProd d 0)
    simp only [Fintype.card_prod] at fc
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_units,fc,ho]
    have qpos : 0<Fintype.card F := Fintype.card_pos
    have ar : 2*((Fintype.card F+1)/2)=Fintype.card F+1 := by omega
    rw [ar]
    obtain ⟨n,en⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Fintype.card F≠0)
    rw [en]
    apply Nat.eq_sub_of_add_eq
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring

/-- Lift an additive character by the quadratic trace, x+y sqrt(d) ↦ 2x. -/
def traceCharacter (ψ : AddChar F ℂ) : AddChar (Ext d) ℂ :=
  ψ.compAddMonoidHom {
    toFun := fun z ↦ 2*z.re
    map_zero' := by simp
    map_add' := by intro z w; simp [mul_add] }

/-- Pull the base quadratic character back through the quadratic norm. -/
def normCharacter : MulChar (Ext d) ℂ where
  toFun z := eta F z.norm
  map_one' := by simp
  map_mul' := by intro x y; simp only [map_mul]
  map_nonunit' := by
    intro z hz
    have e : z=0 := by simpa using hz
    simp [e]

private theorem quadratic_shift (hc : ringChar F≠2) (ψ : AddChar F ℂ) (y : F) :
    (∑ s : F, eta F s*ψ (s*y))=eta F y*gaussSum (eta F) ψ := by
  by_cases zero : y=0
  · have ne : eta F≠1 := (MulChar.ringHomComp_ne_one_iff
        (by exact_mod_cast (Int.cast_injective (α:=ℂ)))).mpr (quadraticChar_ne_one hc)
    simpa [zero,eta] using MulChar.sum_eq_zero_of_ne_one ne
  · let u := Units.mk0 y zero
    have shift := gaussSum_mulShift_eq (eta F) ψ u
    have self := ((quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)).inv
    rw [show (eta F)⁻¹=eta F from self] at shift
    simpa only [gaussSum,AddChar.mulShift_apply,u,Units.val_mk0,mul_comm y] using shift

def twiceRoot (d : F) : Ext d := algebraMap F (Ext d) 2*offset d true

private theorem scalar_norm_character (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) (hn : (h:Ext d).norm=1) (b : Bool) (i : Fin (orderOf h)) (s : Fˣ) :
    normCharacter (scaledTorusUnit h ((b,i),s) : Ext d)=(if b then -1 else 1 : ℂ) := by
  have ns : quadraticChar F d= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr Fact.out
  change (quadraticChar F ((algebraMap F (Ext d) (s:F)* (offset d b*spin h i)).norm):ℂ)=_
  simp only [map_mul,QuadraticAlgebra.norm_algebraMap,spin,map_pow,hn,one_pow,mul_one,
    quadraticChar_sq_one s.ne_zero,one_mul]
  cases b
  · simp [offset]
  · have n : (offset d true).norm= -d := by simp [offset,QuadraticAlgebra.norm_def]
    rw [n,show -d=(-1)*d by ring,map_mul,hm,ns]
    norm_num

omit [Fintype F] [DecidableEq F] in
private theorem root_times_point (h : (Ext d)ˣ) (i : Fin (orderOf h)) (s : Fˣ) :
    twiceRoot d*(scaledTorusUnit h ((true,i),s) : Ext d) =
      algebraMap F (Ext d) (2*d*(s:F))*spin h i := by
  have sr : offset d true*offset d true=algebraMap F (Ext d) d := by
    apply QuadraticAlgebra.ext <;> simp [offset]
  change (algebraMap F (Ext d) 2*offset d true)*
    (algebraMap F (Ext d) (s:F)*(offset d true*spin h i))=_
  rw [map_mul,map_mul,←sr]
  ring

omit [Fintype F] [DecidableEq F] in
private theorem trace_scaled_point (h : (Ext d)ˣ) (i : Fin (orderOf h)) (s : Fˣ)
    (ψ : AddChar F ℂ) :
    traceCharacter ψ (scaledTorusUnit h ((true,i),s) : Ext d)=ψ ((2*d*(s:F))*(spin h i).im) := by
  apply congrArg ψ
  change 2*(algebraMap F (Ext d) (s:F)*(offset d true*spin h i)).re=_
  simp only [offset,ite_true,QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im,zero_mul,mul_zero,zero_add,add_zero,mul_one]
  ring

/-- Difference of the two extension-field Gauss sums for the nonsplit torus mode.
The twist is the quadratic character pulled back by the norm. -/
theorem torus_gauss_difference (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ)
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1)
    (Ω : MulChar (Ext d) ℂ) (restricts : ∀ s : F, Ω (algebraMap F (Ext d) s)=eta F s)
    (ψ : AddChar F ℂ) :
    Ω (twiceRoot d)*(gaussSum Ω (traceCharacter ψ)-gaussSum (Ω*normCharacter) (traceCharacter ψ)) =
      2*gaussSum (eta F) ψ*∑ i : Fin (orderOf h), Ω (spin h i)*eta F (spin h i).im := by
  classical
  let D (z : Ext d) := Ω (twiceRoot d)*(Ω z*traceCharacter ψ z-((Ω*normCharacter : MulChar (Ext d) ℂ) z)*traceCharacter ψ z)
  have dz : D 0=0 := by
    have z : Ω 0=0 := Ω.map_nonunit (by simp)
    simp [D,z]
  let u := Equiv.ofBijective _ (scalar_torus_bijective q4 hm h ho hn)
  have changeCoords : (∑ z : Ext d, D z)=
      ∑ i : Bool×Fin (orderOf h), ∑ s : Fˣ, D (scaledTorusUnit h (i,s)) := by
    rw [←sum_nonzero D dz]
    convert (u.sum_comp (fun z : (Ext d)ˣ ↦ D z)).symm using 1
    exact (Fintype.sum_prod_type (fun v ↦ D (scaledTorusUnit h v))).symm
  have evenZero (i : Fin (orderOf h)) (s : Fˣ) : D (scaledTorusUnit h ((false,i),s))=0 := by
    simp only [D,MulChar.mul_apply,scalar_norm_character hm h hn,Bool.false_eq_true,ite_false,
      mul_one,sub_self,mul_zero]
  have oddTerm (i : Fin (orderOf h)) (s : Fˣ) : D (scaledTorusUnit h ((true,i),s))=
      (2*Ω (spin h i))*(eta F (2*d*(s:F))*ψ ((2*d*(s:F))*(spin h i).im)) := by
    simp only [D,MulChar.mul_apply,scalar_norm_character hm h hn,ite_true,
      trace_scaled_point h i s ψ]
    have map := congrArg Ω (root_times_point h i s)
    rw [map_mul,map_mul,restricts] at map
    linear_combination (2*ψ ((2*d*(s:F))*(spin h i).im))*map
  have twoNZ : (2:F)≠0 := Ring.two_ne_zero hc
  have dn : d≠0 := fun z ↦ Fact.out (p:=¬ IsSquare d) (z ▸ IsSquare.zero)
  let k := Units.mk0 (2*d) (mul_ne_zero twoNZ dn)
  have inner (y : F) : (∑ s : Fˣ, eta F (2*d*(s:F))*ψ ((2*d*(s:F))*y))=
      eta F y*gaussSum (eta F) ψ := by
    calc
      _ = ∑ s : Fˣ, eta F (s:F)*ψ ((s:F)*y) :=
        Equiv.sum_comp (Equiv.mulLeft k) (fun s : Fˣ ↦ eta F (s:F)*ψ ((s:F)*y))
      _ = ∑ s : F, eta F s*ψ (s*y) := sum_nonzero (fun s : F ↦ eta F s*ψ (s*y)) (by simp)
      _ = _ := quadratic_shift hc ψ y
  calc
    _ = ∑ z : Ext d, D z := by simp only [gaussSum,←sum_sub_distrib,mul_sum,D]
    _ = _ := changeCoords
    _ = ∑ i : Fin (orderOf h), (2*Ω (spin h i))*(eta F (spin h i).im*gaussSum (eta F) ψ) := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool,evenZero,sum_const_zero,add_zero,oddTerm,←mul_sum,inner]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring

#print axioms scalar_torus_bijective
#print axioms torus_gauss_difference

/-- Any complex character of the odd torus extends to a character of the
quadratic extension which simultaneously restricts to the base quadratic character. -/
theorem torus_character_lift (q4 : Fintype.card F%4=1) (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) [NeZero (orderOf h)] (ho : orderOf h=(Fintype.card F+1)/2)
    (hn : (h:Ext d).norm=1) (θ : AddChar (Fin (orderOf h)) ℂ) :
    ∃ Ω : MulChar (Ext d) ℂ, (∀ s : F, Ω (algebraMap F (Ext d) s)=eta F s) ∧
      ∀ i : Fin (orderOf h), Ω (spin h i)=θ i := by
  classical
  let T := Multiplicative (Fin (orderOf h))×Fˣ
  let ι : Fˣ →* (Ext d)ˣ := Units.map (algebraMap F (Ext d)).toMonoidHom
  let f : T →* (Ext d)ˣ := {
    toFun := fun v ↦ ι v.2 * h^v.1.toAdd.val
    map_one' := by simp [ι]
    map_mul' := by
      rintro ⟨a,r⟩ ⟨b,s⟩
      change ι (r*s)*h^(a.toAdd+b.toAdd).val=(ι r*h^a.toAdd.val)*(ι s*h^b.toAdd.val)
      simp only [map_mul,Fin.val_add,pow_mod_orderOf,pow_add]
      ac_rfl }
  have fp (v : T) : f v=scaledTorusUnit h ((false,v.1.toAdd),v.2) := by
    apply Units.ext
    simp [f,ι,scaledTorusUnit,vector,offset,spin]
  have inj : Function.Injective f := by
    intro v w e
    rw [fp,fp] at e
    have same := (scalar_torus_bijective q4 hm h ho hn).1 e
    have e1 := congrArg (fun x : (Bool×Fin (orderOf h))×Fˣ ↦ x.1.2) same
    have e2 := congrArg (fun x : (Bool×Fin (orderOf h))×Fˣ ↦ x.2) same
    exact Prod.ext e1 e2
  let φ : T →* ℂ := {
    toFun := fun v ↦ θ v.1.toAdd*eta F (v.2:F)
    map_one' := by simp
    map_mul' := by
      rintro ⟨a,r⟩ ⟨b,s⟩
      change θ (a.toAdd+b.toAdd)*eta F ((r*s:Fˣ):F)=_
      rw [θ.map_add_eq_mul,Units.val_mul,map_mul]
      ring }
  let e : T ≃* f.range := MonoidHom.ofInjective inj
  let ρ := (φ.comp e.symm.toMonoidHom).toHomUnits
  obtain ⟨G,extG⟩ := MonoidHom.domRestrict_surjective (G:=(Ext d)ˣ) ℂ f.range ρ
  let Ω := MulChar.ofUnitHom G
  have agree (v : T) : Ω (f v : Ext d)=θ v.1.toAdd*eta F (v.2:F) := by
    have eq := congrArg (fun l : f.range →* ℂˣ ↦ ((l (e v)):ℂ)) extG
    change ((G (f v) : ℂˣ):ℂ)=φ (e.symm (e v)) at eq
    rw [e.symm_apply_apply] at eq
    exact (MulChar.ofUnitHom_coe G (f v)).trans eq
  refine ⟨Ω,?_,?_⟩
  · intro s
    by_cases z : s=0
    · subst s
      have zero : Ω 0=0 := Ω.map_nonunit (by simp)
      simp [zero]
    · simpa [f,ι] using agree ((1,Units.mk0 s z) : T)
  · intro i
    simpa [f,ι,spin] using agree ((Multiplicative.ofAdd i,1) : T)

#print axioms torus_character_lift

/-- Over the quadratic extension, the pulled-back base character is the
ordinary quadratic character. This identifies the twist in the Gauss difference. -/
theorem normCharacter_eq_quadratic (hm : quadraticChar F (-1)=1) :
    normCharacter (d:=d)=eta (Ext d) := by
  classical
  have onSquares (z : Ext d) (zn : z≠0) (sq : IsSquare z) : normCharacter z=1 := by
    have nn : z.norm≠0 := fun e ↦ zn (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp e)
    change (quadraticChar F z.norm : ℂ)=1
    exact_mod_cast (quadraticChar_one_iff_isSquare nn).mpr (sq.map QuadraticAlgebra.norm)
  let w := offset d true
  have wn : w≠0 := by
    intro e
    exact one_ne_zero (congrArg QuadraticAlgebra.im e)
  have neg : normCharacter w= -1 := by
    have ns : quadraticChar F d= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr Fact.out
    have n : w.norm= -d := by simp [w,offset,QuadraticAlgebra.norm_def]
    change (quadraticChar F w.norm : ℂ)= -1
    rw [n,show -d=(-1)*d by ring,map_mul,hm,ns]
    norm_num
  have nonsquare : ¬ IsSquare w := by intro sq; have := (onSquares w wn sq).symm.trans neg; norm_num at this
  have negE : quadraticChar (Ext d) w= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr nonsquare
  apply MulChar.ext
  intro z
  by_cases sq : IsSquare (z:Ext d)
  · rw [onSquares z z.ne_zero sq]
    change (1:ℂ)=(quadraticChar (Ext d) (z:Ext d):ℂ)
    rw [(quadraticChar_one_iff_isSquare z.ne_zero).mpr sq,Int.cast_one]
  · have nz : quadraticChar (Ext d) (z:Ext d)= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr sq
    have ne := mul_ne_zero z.ne_zero wn
    have prod : IsSquare ((z:Ext d)*w) := (quadraticChar_one_iff_isSquare ne).mp
      (by rw [map_mul,nz,negE]; norm_num)
    have val := onSquares ((z:Ext d)*w) ne prod
    rw [map_mul,neg] at val
    change normCharacter (z:Ext d)=(quadraticChar (Ext d) (z:Ext d):ℂ)
    rw [nz]
    push_cast
    linear_combination -val

/-- The phase at 2 sqrt(d) is a square root of -1 for every admissible extension. -/
theorem torus_gauss_phase (hc : ringChar F≠2) (Ω : MulChar (Ext d) ℂ)
    (restricts : ∀ s : F, Ω (algebraMap F (Ext d) s)=eta F s) :
    (Ω (twiceRoot d))^2= -1 := by
  have sq : (twiceRoot d)^2 = algebraMap F (Ext d) ((2:F)^2*d) := by
    apply QuadraticAlgebra.ext <;> simp [twiceRoot,offset,pow_two]; ring
  rw [←map_pow,sq,restricts,map_mul]
  change (quadraticChar F ((2:F)^2):ℂ)*(quadraticChar F d:ℂ)= -1
  rw [map_pow,quadraticChar_sq_one (Ring.two_ne_zero hc),
    quadraticChar_neg_one_iff_not_isSquare.mpr (Fact.out : ¬IsSquare d)]
  norm_num

/-- The Fourier coefficient of every torus character has its own pair of
ordinary extension-field Gauss sums, with a specified fourth-root phase. -/
theorem exists_torus_gauss_pair (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1)
    (θ : AddChar (Fin (orderOf h)) ℂ) :
    ∃ Ω : MulChar (Ext d) ℂ, (∀ s : F, Ω (algebraMap F (Ext d) s)=eta F s) ∧
      (∀ i : Fin (orderOf h), Ω (spin h i)=θ i) ∧ (Ω (twiceRoot d))^2= -1 ∧
      ∀ ψ : AddChar F ℂ, Ω (twiceRoot d)*
        (gaussSum Ω (traceCharacter ψ)-gaussSum (Ω*eta (Ext d)) (traceCharacter ψ))=
          2*gaussSum (eta F) ψ*∑ i : Fin (orderOf h), θ i*eta F (spin h i).im := by
  obtain ⟨Ω,base,torus⟩ := torus_character_lift q4 hm h ho hn θ
  refine ⟨Ω,base,torus,torus_gauss_phase hc Ω base,fun ψ ↦ ?_⟩
  simpa only [normCharacter_eq_quadratic hm,torus] using torus_gauss_difference hc q4 hm h ho hn Ω base ψ

#print axioms normCharacter_eq_quadratic
#print axioms torus_gauss_phase
#print axioms exists_torus_gauss_pair

end Hadamard.NonsplitTorus
