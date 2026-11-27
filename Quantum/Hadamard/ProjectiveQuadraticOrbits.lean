import Quantum.Hadamard.ProjectivePaleyAction

/-! All nonsingular binary quadratic signings of the Paley matrix have their
absolute determinant among six explicit signings in the same finite field. -/

noncomputable section
open Finset
open scoped BigOperators

namespace Hadamard.ProjectiveSigning
open Coordinates
variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

def binary (a b c u v : F) : F := a*u^2+b*u*v+c*v^2

omit [DecidableEq F] [Fintype F] in
private theorem binary_point (a b c : F) (i : Option F) :
    binary a b c (x i) (y i) = quadraticValue a b c i := by
  cases i <;> simp [binary,x,y,quadraticValue]

inductive FormKind | split | nonsplit

def FormKind.value (d : F) : FormKind → F → F → F
  | .split,u,v => u*v
  | .nonsplit,u,v => u^2-d*v^2

/-- The explicit substitution takes the field form to a scalar multiple of
either XY or X²-dY². No choice of projective orbit representatives is assumed. -/
theorem quadratic_normal_form (two : (2:F)≠0) (d : F) (hd : quadraticChar F d= -1)
    (a b c : F) (disc : b^2-4*a*c≠0) :
    ∃ (j : FormKind) (g : Change F) (k : F), k≠0 ∧
      ∀ u v, binary a b c (g.top u v) (g.bot u v)=k*j.value d u v := by
  let D := b^2-4*a*c
  have norm (u v : F) : binary a b c (u-b*v) (2*a*v)=a*(u^2-D*v^2) := by
    unfold binary D; ring
  by_cases ha : a=0
  · subst a
    have hb : b≠0 := by simpa using disc
    refine ⟨.split,⟨1,-c,0,b,by simpa using hb⟩,b^2,pow_ne_zero _ hb,?_⟩
    intro u v
    dsimp [binary,Change.top,Change.bot,FormKind.value]; ring
  by_cases h : IsSquare D
  · obtain ⟨t,ht⟩ := h
    have tn : t≠0 := by intro eq; apply disc; change D=0; simp [ht,eq]
    have nn : -((2:F)^2*a*t)≠0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ two) ha) tn)
    let g : Change F := ⟨t-b,t+b,2*a,-(2*a),by
      convert nn using 1; ring⟩
    refine ⟨.split,g,(2:F)^2*a*t^2,mul_ne_zero (mul_ne_zero (pow_ne_zero _ two) ha) (pow_ne_zero _ tn),?_⟩
    intro u v
    have top : g.top u v=t*(u+v)-b*(u-v) := by dsimp [g,Change.top]; ring
    have bot : g.bot u v=2*a*(u-v) := by dsimp [g,Change.bot]; ring
    rw [top,bot,norm,ht]; dsimp [FormKind.value]; ring
  · have dn : d≠0 := by intro e; simp [e] at hd
    have value := quadraticChar_neg_one_iff_not_isSquare.mpr h
    have prod : quadraticChar F (D/d)*quadraticChar F d=quadraticChar F D := by
      rw [←map_mul,div_mul_cancel₀ _ dn]
    rw [hd,value] at prod
    have sq : IsSquare (D/d) := (quadraticChar_one_iff_isSquare (div_ne_zero disc dn)).mp (by linarith)
    obtain ⟨t,ht⟩ := sq
    have eqD : D=d*t^2 := by rw [←div_mul_cancel₀ D dn,ht]; ring
    have tn : t≠0 := by intro e; apply disc; change D=0; simp [eqD,e]
    let g : Change F := ⟨t,-b,0,2*a,by simpa using mul_ne_zero tn (mul_ne_zero two ha)⟩
    refine ⟨.nonsplit,g,a*t^2,mul_ne_zero ha (pow_ne_zero _ tn),?_⟩
    intro u v
    have top : g.top u v=t*u-b*v := by dsimp [g,Change.top]; ring
    have bot : g.bot u v=2*a*v := by simp [g,Change.bot]
    rw [top,bot,norm,eqD]; dsimp [FormKind.value]; ring

def signOf (b : Bool) : ℤ := if b then 1 else -1

inductive Pattern
  | split (squarePositive zeroPositive : Bool)
  | nonsplit (positiveOrientation : Bool)
  deriving DecidableEq

def Pattern.read (character : F→ℤ) (d : F) : Pattern → Option F → ℤ
  | .split _ z,none => -signOf z
  | .split o z,some u => if u=0 then signOf z else signOf o*character u
  | .nonsplit o,i => signOf o*character (quadraticValue 1 0 (-d) i)

def Pattern.sign (d : F) (pat : Pattern) : Option F→ℤ := pat.read (quadraticChar F) d

omit [Fintype F] in
private theorem factors_at (a b c d k : F) (kind : FormKind) (g : Change F)
    (identity : ∀ u v, binary a b c (g.top u v) (g.bot u v)=k*kind.value d u v)
    (i : Option F) :
    g.factor i^2*quadraticValue a b c (g.perm i) = k*kind.value d (x i) (y i) := by
  rw [←identity,←g.top_eq,←g.bot_eq,←binary_point]
  change g.factor i^2*binary a b c (x (g.act i)) (y (g.act i))=_
  unfold binary; ring

omit [Fintype F] in
private theorem root_iff (a b c d k : F) (hk : k≠0) (kind : FormKind) (g : Change F)
    (normal : ∀ u v, binary a b c (g.top u v) (g.bot u v)=k*kind.value d u v) (i : Option F) :
    quadraticValue a b c (g.perm i)=0 ↔ kind.value d (x i) (y i)=0 := by
  have h := congrArg (fun t : F ↦ t=0) (factors_at a b c d k kind g normal i)
  simpa [mul_eq_zero,hk,g.factor_ne i] using Iff.of_eq h

private theorem nonsplit_ne (d : F) (hd : quadraticChar F d= -1) (i : Option F) :
    FormKind.nonsplit.value d (x i) (y i)≠0 := by
  have ns := quadraticChar_neg_one_iff_not_isSquare.mp hd
  cases i with
  | none => simp [FormKind.value,x,y]
  | some u =>
    simpa [FormKind.value,x,y,sub_ne_zero] using (show u^2≠d by
      intro h; exact ns ⟨u,by rw [←h,pow_two]⟩)

/-- Assigning opposite signs to distinct projective roots makes their total
zero. A nonsingular form has either both of the split roots or no roots. -/
theorem sum_at_opposite_roots (hc : ringChar F≠2) (a b c : F) (disc : b^2-4*a*c≠0)
    (s : Option F→Bool) (opposite : ∀ i j, i≠j → quadraticValue a b c i=0 →
      quadraticValue a b c j=0 → s i≠s j) :
    (∑ i, if quadraticValue a b c i=0 then signOf (s i) else 0)=0 := by
  have two : (2:F)≠0 := fun h ↦ hc (CharP.ringChar_of_prime_eq_zero Nat.prime_two h)
  obtain ⟨d,hd⟩ := quadraticChar_exists_neg_one (F:=F) hc
  obtain ⟨kind,g,k,hk,normal⟩ := quadratic_normal_form two d hd a b c disc
  have zero := root_iff a b c d k hk kind g normal
  rw [←g.perm.sum_comp (fun i ↦ if quadraticValue a b c i=0 then signOf (s i) else 0)]
  simp only [zero]
  cases kind with
  | split =>
    have distinct : g.perm none≠g.perm (some 0) := g.perm.injective.ne (by simp)
    have their := opposite _ _ distinct ((zero none).mpr (by simp [FormKind.value,x,y]))
      ((zero (some 0)).mpr (by simp [FormKind.value,x,y]))
    have neg : signOf (s (g.perm none))+signOf (s (g.perm (some 0)))=0 := by
      cases a0 : s (g.perm none) <;> cases a1 : s (g.perm (some 0)) <;> simp_all [signOf]
    simpa [Fintype.sum_option,FormKind.value,x,y] using neg
  | nonsplit =>
    simp [nonsplit_ne d hd]

private theorem flag_of_unit {n : ℤ} (u : n^2=1) : ∃b : Bool, signOf b=n := by
  rcases sq_eq_one_iff.mp u with h|h
  · exact ⟨true,h.symm⟩
  · exact ⟨false,h.symm⟩

/-- Every resolved quadratic signing has exactly the same absolute
determinant as one of the four split and two nonsplit canonical signings. -/
theorem quadratic_det_six (two : (2:F)≠0) (hm : quadraticChar F (-1)=1)
    (d : F) (hd : quadraticChar F d= -1) (a b c : F) (disc : b^2-4*a*c≠0)
    (s : Option F→ℤ) (w : ℤ) (hw : w^2=1) (hs : ∀ i, (s i)^2=1)
    (agree : ∀ i, quadraticValue a b c i≠0 → s i=w*quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i, if quadraticValue a b c i=0 then s i else 0)=0) :
    ∃ pat : Pattern, signedDet s=signedDet (pat.sign d) := by
  obtain ⟨kind,g,k,hk,identity⟩ := quadratic_normal_form two d hd a b c disc
  let K := quadraticChar F g.det
  let z (i : Option F) := K*s (g.perm i)
  let v := K*w*quadraticChar F k
  have Ksq : K^2=1 := quadraticChar_sq_one (show g.det≠0 from g.invertible)
  have vsq : v^2=1 := by simp only [v,mul_pow,Ksq,hw,quadraticChar_sq_one hk,one_mul]
  obtain ⟨o,ho⟩ := flag_of_unit vsq
  have zs (i) : (z i)^2=1 := by simp [z,mul_pow,Ksq,hs]
  have zero (i) : quadraticValue a b c (g.perm i)=0 ↔ kind.value d (x i) (y i)=0 := by
    exact root_iff a b c d k hk kind g identity i
  have val (i) (hn : kind.value d (x i) (y i)≠0) :
      z i = signOf o*quadraticChar F (kind.value d (x i) (y i)) := by
    have ch := congrArg (quadraticChar F) (factors_at a b c d k kind g identity i)
    simp only [map_mul,map_pow,quadraticChar_sq_one (g.factor_ne i),one_mul] at ch
    rw [ho]; dsimp [z,v]
    rw [agree _ (mt (zero i).mp hn),ch]; ring
  have total : (∑ i, if kind.value d (x i) (y i)=0 then z i else 0)=0 := by
    calc
      _ = K*∑ i, if quadraticValue a b c (g.perm i)=0 then s (g.perm i) else 0 := by
        rw [mul_sum]; apply sum_congr rfl; intro i _
        by_cases h : kind.value d (x i) (y i)=0
        · simp [h,(zero i).mpr h,z]
        · simp [h,mt (zero i).mp h]
      _ = 0 := by rw [g.perm.sum_comp (fun i ↦ if quadraticValue a b c i=0 then s i else 0),ties,mul_zero]
  have det := signedDet_change hm g s
  change signedDet s=signedDet z at det
  cases kind with
  | split =>
    obtain ⟨b0,hb⟩ := flag_of_unit (zs (some 0))
    have roots : z none+z (some 0)=0 := by
      simpa [Fintype.sum_option,FormKind.value,x,y] using total
    refine ⟨.split o b0,det.trans (congrArg signedDet (funext ?_))⟩
    rintro (_|u)
    · change z none= -signOf b0; rw [hb]; linarith
    · by_cases h : u=0
      · subst u; simpa [Pattern.sign,Pattern.read] using hb.symm
      · simpa [FormKind.value,Pattern.sign,Pattern.read,x,y,h] using val (some u) (by simpa [FormKind.value,x,y] using h)
  | nonsplit =>
    refine ⟨.nonsplit o,det.trans (congrArg signedDet (funext ?_))⟩
    intro i
    have h := val i (nonsplit_ne d hd i)
    cases i <;> simpa [FormKind.value,Pattern.sign,Pattern.read,x,y,quadraticValue,sub_eq_add_neg] using h

#print axioms sum_at_opposite_roots
#print axioms quadratic_normal_form
#print axioms quadratic_det_six
end Hadamard.ProjectiveSigning
