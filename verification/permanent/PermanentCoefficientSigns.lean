import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Signs of coefficients after splitting the variables of a generic matrix
into two sets. A row monomial is a partial matching between row and column
subsets. A complementary monomial uses the two complementary subsets. -/

noncomputable section
open Equiv Equiv.Perm
open scoped Classical
namespace PermanentCuts

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (S T : I → Prop) [DecidablePred S] [DecidablePred T]

abbrev Left := Subtype S ≃ Subtype T
abbrev Right := {i : I // ¬S i} ≃ {i : I // ¬T i}

/-- Glue complementary partial matchings to the permutation of a full monomial. -/
def glue (u : Left S T) (v : Right S T) : Perm I :=
  (Equiv.sumCompl S).symm.trans ((Equiv.sumCongr u v).trans (Equiv.sumCompl T))

/-- Independent local signs factor the permutation sign on any block of
complementary row and column supports. -/
theorem sign_factors (u₀ : Left S T) (v₀ : Right S T) (u : Left S T) (v : Right S T) :
    sign (glue S T u v)=sign (glue S T u₀ v₀)*
      sign (u.trans u₀.symm)*sign (v.trans v₀.symm) := by
  let a := u.trans u₀.symm
  let b := v.trans v₀.symm
  let side := Equiv.sumCompl S
  let split := Equiv.sumCongr a b
  have e : glue S T u v=(side.permCongr split).trans (glue S T u₀ v₀) := by
    apply Equiv.ext
    intro i
    obtain ⟨j,rfl⟩ := side.surjective i
    cases j <;> simp [glue,side,Equiv.permCongr,split,a,b]
  rw [e,sign_trans,sign_permCongr,sign_sumCongr]
  exact (mul_assoc _ _ _).symm

/-- The edge colouring selects the variables that are available in each monomial. -/
def allowed (colour : I → I → Bool) (u : Left S T) (v : Right S T) : Prop :=
  (∀ i, colour i.val (u i).val=true) ∧ (∀ i, colour i.val (v i).val=false)

/-- Within a support block, coefficients of both polynomials vanish at the
same forbidden pairs. At every allowed pair the determinant coefficient is
the product of two signs depending separately on the partial matchings. -/
theorem coefficient_signs (colour : I → I → Bool) :
    ∃ row : Left S T → ℤˣ, ∃ col : Right S T → ℤˣ, ∀ u v,
      (if allowed S T colour u v then (sign (glue S T u v):ℤ) else 0)=
      (row u:ℤ)*(col v:ℤ)*(if allowed S T colour u v then 1 else 0) := by
  classical
  by_cases hasLeft : Nonempty (Left S T)
  · by_cases hasRight : Nonempty (Right S T)
    · obtain ⟨u₀⟩ := hasLeft
      obtain ⟨v₀⟩ := hasRight
      refine ⟨fun u ↦ sign (glue S T u₀ v₀)*sign (u.trans u₀.symm),
        fun v ↦ sign (v.trans v₀.symm),fun u v ↦ ?_⟩
      by_cases present : allowed S T colour u v
      · simp only [present,ite_true,mul_one,←Units.val_mul,sign_factors S T u₀ v₀ u v]
      · simp [present]
    · exact ⟨fun _ ↦ 1,fun _ ↦ 1,fun _ v ↦ (hasRight ⟨v⟩).elim⟩
  · exact ⟨fun _ ↦ 1,fun _ ↦ 1,fun u _ ↦ (hasLeft ⟨u⟩).elim⟩

#print axioms sign_factors
#print axioms coefficient_signs
open Matrix

abbrev Support (I : Type*) := Finset I × Finset I
abbrev LeftAt (k : Support I) := Left (fun i ↦ i∈k.1) (fun i ↦ i∈k.2)
abbrev RightAt (k : Support I) := Right (fun i ↦ i∈k.1) (fun i ↦ i∈k.2)

/-- A support block of the coefficient matrix, indexed by partial matchings. -/
def block (K : Type*) [Field K] (colour : I → I → Bool) (signed : Bool) (k : Support I) :
    Matrix (LeftAt k) (RightAt k) K := fun u v ↦
  if allowed (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour u v then
    if signed then ((sign (glue (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) u v):ℤ):K) else 1
  else 0

/-- Complete matching-indexed coefficient matrix for a binary variable cut.
Other squarefree monomial labels would give identically zero rows or columns. -/
def coefficients (K : Type*) [Field K] (colour : I → I → Bool) (signed : Bool) :
    Matrix (Σ k : Support I, LeftAt k) (Σ k : Support I, RightAt k) K :=
  Matrix.blockDiagonal' (block K colour signed)

/-- All binary variable cuts give the same rank for the two coefficient
matrices over every field, including fields of positive characteristic. -/
theorem coefficients_rank (K : Type*) [Field K] (colour : I → I → Bool) :
    (coefficients K colour true).rank=(coefficients K colour false).rank := by
  classical
  choose l r eq using (fun k : Support I ↦
    coefficient_signs (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour)
  let U (i : Σ k : Support I, LeftAt k) : K := ((l i.1 i.2:ℤ):K)
  let V (j : Σ k : Support I, RightAt k) : K := ((r j.1 j.2:ℤ):K)
  have units (z : ℤˣ) : IsUnit ((z:ℤ):K) := z.isUnit.map (Int.castRingHom K)
  have mat : coefficients K colour true =
      diagonal U * coefficients K colour false * diagonal V := by
    ext ⟨k,u⟩ ⟨m,v⟩
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases same : k=m
    · subst m
      simp only [coefficients,blockDiagonal'_apply_eq]
      have val := congrArg (Int.castRingHom K) (eq k u v)
      by_cases full : allowed (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour u v
      · simpa [full,block,U,V,mul_left_comm,mul_comm,mul_assoc] using val
      · simp [block,full]
    · simp [coefficients,blockDiagonal'_apply_ne _ _ _ same]
  have hu : IsUnit (diagonal U).det := by
    rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (units _).ne_zero)
  have hv : IsUnit (diagonal V).det := by
    rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (units _).ne_zero)
  rw [mat,rank_mul_eq_left_of_isUnit_det _ _ hv,rank_mul_eq_right_of_isUnit_det _ _ hu]

#print axioms coefficients_rank

open Finset MvPolynomial

/-- Exponent vector of a permutation monomial in the generic matrix. -/
def exponents (σ : Perm I) : (I×I) →₀ ℕ :=
  ∑ i, Finsupp.single (i,σ i) 1

private theorem exponents_apply (σ : Perm I) (i j : I) :
    exponents σ (i,j)=if σ i=j then 1 else 0 := by
  simp [exponents,Finsupp.single_apply,Prod.mk.injEq,ite_and]

private theorem exponents_injective : Function.Injective (exponents (I:=I)) := by
  intro σ τ e
  apply Equiv.ext
  intro i
  have eq := congrArg (fun a : (I×I) →₀ ℕ ↦ a (i,σ i)) e
  simp only [exponents_apply,ite_true] at eq
  split_ifs at eq with same
  · exact same.symm

def generic (K : Type*) [CommRing K] (I : Type*) : Matrix I I (MvPolynomial (I×I) K) :=
  Matrix.of (fun i j ↦ X (i,j))

private theorem product_variables (K : Type*) [CommRing K] (σ : Perm I) :
    (∏ i, X (i,σ i):MvPolynomial (I×I) K)=monomial (exponents σ) 1 := by
  have part (t : Finset I) : (∏ i ∈ t,X (i,σ i):MvPolynomial (I×I) K)=
      monomial (∑ i ∈ t,Finsupp.single (i,σ i) 1) 1 := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      rw [prod_insert hi,sum_insert hi,ih]
      change monomial (Finsupp.single (i,σ i) 1) 1*monomial _ 1=_
      rw [monomial_mul_monomial,mul_one]
  exact part univ

/-- These are the coefficients of Mathlib's determinant and permanent of
the actual generic multivariate polynomial matrix at every exponent. -/
theorem generic_coefficients (K : Type*) [CommRing K] (d : (I×I) →₀ ℕ) :
    (generic K I).permanent.coeff d=(∑ σ : Perm I, if exponents σ=d then (1:K) else 0) ∧
    (generic K I).det.coeff d=∑ σ : Perm I, if exponents σ=d then ((sign σ:ℤ):K) else 0 := by
  constructor
  · rw [←Matrix.permanent_transpose,Matrix.permanent,coeff_sum]
    apply sum_congr rfl
    intro σ _
    change (∏ i,X (i,σ i):MvPolynomial (I×I) K).coeff d=_
    rw [product_variables,coeff_monomial]
  · rw [←Matrix.det_transpose,Matrix.det_apply',coeff_sum]
    apply sum_congr rfl
    intro σ _
    change (((sign σ:ℤ):MvPolynomial (I×I) K)*(∏ i,X (i,σ i))).coeff d=_
    rw [product_variables,←show C ((sign σ:ℤ):K)=((sign σ:ℤ):MvPolynomial (I×I) K) from by simp,
      C_mul_monomial,coeff_monomial]
    simp

/-- On a completing permutation the generic coefficients are one and its sign. -/
theorem generic_matching (K : Type*) [CommRing K] (σ : Perm I) :
    (generic K I).permanent.coeff (exponents σ)=1 ∧
    (generic K I).det.coeff (exponents σ)=((sign σ:ℤ):K) := by
  have eq (τ : Perm I) : exponents τ=exponents σ ↔ τ=σ := exponents_injective.eq_iff
  obtain ⟨p,d⟩ := generic_coefficients K (exponents σ)
  simp [p,d,eq]

/-- Coefficient matrix read from the determinant or permanent polynomial itself. -/
def polynomialCoefficients (K : Type*) [Field K] (colour : I → I → Bool) (signed : Bool) :
    Matrix (Σ k : Support I, LeftAt k) (Σ k : Support I, RightAt k) K :=
  blockDiagonal' (fun k u v ↦ if allowed (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour u v then
    (if signed then (generic K I).det else (generic K I).permanent).coeff
      (exponents (glue (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) u v)) else 0)

/-- Rank equality using the polynomial coefficients on every matching block. -/
theorem polynomial_coefficients_rank (K : Type*) [Field K] (colour : I → I → Bool) :
    (polynomialCoefficients K colour true).rank=(polynomialCoefficients K colour false).rank := by
  have same (s : Bool) : polynomialCoefficients K colour s=coefficients K colour s := by
    unfold polynomialCoefficients coefficients
    congr 1
    funext k u v
    cases s <;> simp [block,(generic_matching K _).1,(generic_matching K _).2]
  rw [same,same,coefficients_rank]

#print axioms generic_coefficients
#print axioms polynomial_coefficients_rank

/-- The usual exponent vector of a squarefree monomial. -/
def squareDegree (a : Finset (I × I)) : (I × I) →₀ ℕ :=
  ∑ e ∈ a, Finsupp.single e 1

omit [Fintype I] in
private theorem squareDegree_apply (a : Finset (I × I)) (e : I × I) :
    squareDegree a e = if e ∈ a then 1 else 0 := by
  simp [squareDegree, Finsupp.single_apply]

/-- An edge set representing one monomial on the indicated side of the cut. -/
abbrev Labels (colour : I → I → Bool) (side : Bool) :=
  {a : Finset (I × I) // ∀ e ∈ a, colour e.1 e.2 = side}

/-- The ordinary coefficient matrix, including rows and columns indexed by
monomials whose edge sets fail to be partial matchings. -/
def cutMatrix (colour : I → I → Bool) {K : Type*} [CommRing K]
    (p : MvPolynomial (I × I) K) : Matrix (Labels colour true) (Labels colour false) K :=
  fun a b ↦ p.coeff (squareDegree (a.val ∪ b.val))

private def matchingGraph {S T : I → Prop} (u : Left S T) [Fintype (Subtype S)] :
    Finset (I × I) := univ.image (fun x : Subtype S ↦ (x.val, (u x).val))

section
omit [Fintype I]

private theorem mem_matchingGraph {S T : I → Prop} (u : Left S T) [Fintype (Subtype S)] (i j : I) :
    (i,j) ∈ matchingGraph u ↔ ∃ h : S i, (u ⟨i,h⟩).val = j := by
  constructor
  · intro m
    obtain ⟨⟨x,h⟩, _, e⟩ := mem_image.mp m
    cases e
    exact ⟨h,rfl⟩
  · rintro ⟨h,rfl⟩
    exact mem_image.mpr ⟨⟨i,h⟩,mem_univ _,rfl⟩

private theorem matchingGraph_domain {S T : I → Prop} (u : Left S T) [Fintype (Subtype S)] (i : I) :
    (∃ j, (i,j) ∈ matchingGraph u) ↔ S i := by
  constructor
  · rintro ⟨j,h⟩
    exact ((mem_matchingGraph u _ _).mp h).choose
  · intro h
    exact ⟨_,(mem_matchingGraph u _ _).mpr ⟨h,rfl⟩⟩

private theorem matchingGraph_range {S T : I → Prop} (u : Left S T) [Fintype (Subtype S)] (j : I) :
    (∃ i, (i,j) ∈ matchingGraph u) ↔ T j := by
  constructor
  · rintro ⟨i,h⟩
    obtain ⟨hi,rfl⟩ := (mem_matchingGraph u _ _).mp h
    exact (u ⟨i,hi⟩).property
  · intro h
    obtain ⟨i,e⟩ := u.surjective ⟨j,h⟩
    exact ⟨i.val,(mem_matchingGraph u _ _).mpr ⟨i.property,congrArg Subtype.val e⟩⟩

private theorem matchingGraph_inj {S T : I → Prop} [Fintype (Subtype S)] :
    Function.Injective (fun u : Left S T ↦ matchingGraph u) := by
  intro u v eq
  change matchingGraph u = matchingGraph v at eq
  apply Equiv.ext
  intro i
  apply Subtype.ext
  have m := (mem_matchingGraph u i.val (u i).val).mpr ⟨i.property,rfl⟩
  rw [eq] at m
  exact ((mem_matchingGraph v _ _).mp m).choose_spec.symm

end

private def rowLabel (a : Σ k : Support I, LeftAt k) : Finset (I × I) := matchingGraph a.2
private def colLabel (a : Σ k : Support I, RightAt k) : Finset (I × I) := matchingGraph a.2

omit [Fintype I] in
private theorem rowLabel_injective : Function.Injective (rowLabel (I:=I)) := by
  rintro ⟨⟨s,t⟩,u⟩ ⟨⟨s',t'⟩,v⟩ h
  change matchingGraph u = matchingGraph v at h
  have es : s=s' := by
    ext i
    simp only [← matchingGraph_domain u i,← matchingGraph_domain v i,h]
  have et : t=t' := by
    ext j
    simp only [← matchingGraph_range u j,← matchingGraph_range v j,h]
  subst s'
  subst t'
  have uv : u = v := matchingGraph_inj (S:=fun i ↦ i∈s) (T:=fun i ↦ i∈t) h
  cases uv
  rfl

private theorem colLabel_injective : Function.Injective (colLabel (I:=I)) := by
  rintro ⟨⟨s,t⟩,u⟩ ⟨⟨s',t'⟩,v⟩ h
  change matchingGraph u = matchingGraph v at h
  have es : s=s' := by
    ext i
    have e : (i∉s) ↔ (i∉s') := by
      simp only [← matchingGraph_domain u i,← matchingGraph_domain v i,h]
    simpa only [not_not] using e.not
  have et : t=t' := by
    ext j
    have e : (j∉t) ↔ (j∉t') := by
      simp only [← matchingGraph_range u j,← matchingGraph_range v j,h]
    simpa only [not_not] using e.not
  subst s'
  subst t'
  have uv : u = v := matchingGraph_inj (S:=fun i ↦ i∉s) (T:=fun i ↦ i∉t) h
  cases uv
  rfl

private theorem split_term (colour : I → I → Bool) (a : Labels colour true)
    (b : Labels colour false) (σ : Perm I) (h : exponents σ = squareDegree (a.val ∪ b.val)) :
    ∃ (k : Support I) (u : LeftAt k) (v : RightAt k),
      rowLabel ⟨k,u⟩ = a.val ∧ colLabel ⟨k,v⟩ = b.val ∧
      glue (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) u v = σ ∧
      allowed (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour u v := by
  have edges (i j : I) : (i,j) ∈ a.val ∪ b.val ↔ σ i = j := by
    have val := congrArg (fun x : (I × I) →₀ ℕ ↦ x (i,j)) h
    change exponents σ (i,j) = squareDegree (a.val ∪ b.val) (i,j) at val
    rw [exponents_apply,squareDegree_apply] at val
    by_cases e : (i,j) ∈ a.val ∪ b.val <;> by_cases g : σ i = j <;> simp [e,g] at *
  let s := univ.filter (fun i ↦ colour i (σ i) = true)
  let t := s.map σ.toEmbedding
  have maps (i : I) : i∈s ↔ σ i∈t := by simp [t]
  let u : LeftAt (s,t) := σ.subtypeEquiv maps
  let v : RightAt (s,t) := σ.subtypeEquiv (fun i ↦ (maps i).not)
  have red (i j : I) : (i,j) ∈ a.val ↔ i∈s ∧ σ i=j := by
    constructor
    · intro hx
      have e := (edges i j).mp (mem_union_left _ hx)
      exact ⟨mem_filter.mpr ⟨mem_univ _,by simpa only [e] using a.property _ hx⟩,e⟩
    · rintro ⟨hs,rfl⟩
      rcases mem_union.mp ((edges i _).mpr rfl) with ha|hb
      · exact ha
      · have hc := (mem_filter.mp hs).2
        have hn := b.property _ hb
        simp_all
  have blue (i j : I) : (i,j) ∈ b.val ↔ i∉s ∧ σ i=j := by
    constructor
    · intro hx
      have e := (edges i j).mp (mem_union_right _ hx)
      refine ⟨?_,e⟩
      intro hs
      have hc := (mem_filter.mp hs).2
      have hn := b.property _ hx
      simp_all
    · rintro ⟨hs,rfl⟩
      rcases mem_union.mp ((edges i _).mpr rfl) with ha|hb
      · exact (hs ((red _ _).mp ha).1).elim
      · exact hb
  refine ⟨(s,t),u,v,?_,?_,?_,?_⟩
  · ext ⟨i,j⟩
    rw [rowLabel,mem_matchingGraph,red]
    change (∃ _ : i∈s, σ i=j) ↔ i∈s ∧ σ i=j
    exact exists_prop
  · ext ⟨i,j⟩
    rw [colLabel,mem_matchingGraph,blue]
    change (∃ _ : i∉s, σ i=j) ↔ i∉s ∧ σ i=j
    exact exists_prop
  · apply Equiv.ext
    intro i
    obtain ⟨m,rfl⟩ := (Equiv.sumCompl (fun j ↦ j∈s)).surjective i
    cases m <;> simp [glue,u,v]
  · constructor
    · intro i
      exact (mem_filter.mp i.property).2
    · intro i
      change colour i.val (σ i.val) = false
      cases e : colour i.val (σ i.val) with
      | false => rfl
      | true => exact (i.property (mem_filter.mpr ⟨mem_univ _,e⟩)).elim

/-- For the ordinary squarefree coefficient matrices, row and column signs
take the permanent to the determinant across every binary cut. -/
theorem squarefree_diagonal_equivalence (K : Type*) [CommRing K] (colour : I → I → Bool) :
    ∃ (row : Labels colour true → ℤˣ) (col : Labels colour false → ℤˣ),
      cutMatrix colour (generic K I).det =
        diagonal (fun a ↦ ((row a : ℤ) : K)) * cutMatrix colour (generic K I).permanent *
          diagonal (fun b ↦ ((col b : ℤ) : K)) := by
  classical
  choose l r h using (fun k : Support I ↦
    coefficient_signs (fun i ↦ i∈k.1) (fun i ↦ i∈k.2) colour)
  let row := Function.extend rowLabel (fun i ↦ l i.1 i.2) (fun _ ↦ (1 : ℤˣ))
  let col := Function.extend colLabel (fun j ↦ r j.1 j.2) (fun _ ↦ (1 : ℤˣ))
  have term (a : Labels colour true) (b : Labels colour false) (σ : Perm I)
      (e : exponents σ = squareDegree (a.val ∪ b.val)) :
      (sign σ : ℤ) = (row a.val : ℤ) * (col b.val : ℤ) := by
    obtain ⟨k,u,v,hu,hv,hg,ha⟩ := split_term colour a b σ e
    have eq := h k u v
    simp only [ha,ite_true,mul_one,hg] at eq
    rw [←hu,←hv]
    simpa only [row,col,rowLabel_injective.extend_apply,colLabel_injective.extend_apply] using eq
  refine ⟨fun a ↦ row a.val,fun b ↦ col b.val,?_⟩
  ext a b
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  unfold cutMatrix
  obtain ⟨p,d⟩ := generic_coefficients K (squareDegree (a.val ∪ b.val))
  rw [p,d,Finset.mul_sum,Finset.sum_mul]
  apply sum_congr rfl
  intro σ _
  by_cases e : exponents σ = squareDegree (a.val ∪ b.val)
  · simp [e,term a b σ e]
  · simp [e]

/-- The rank test on all squarefree monomials agrees for the generic determinant
and permanent, for every matrix order, every variable partition and every field. -/
theorem squarefree_cut_rank (K : Type*) [Field K] (colour : I → I → Bool) :
    (cutMatrix colour (generic K I).det).rank = (cutMatrix colour (generic K I).permanent).rank := by
  classical
  obtain ⟨row,col,eq⟩ := squarefree_diagonal_equivalence K colour
  have ur : IsUnit (diagonal (fun a ↦ ((row a : ℤ) : K))).det := by
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun a _ ↦
      ((row a).isUnit.map (Int.castRingHom K)).ne_zero)
  have uc : IsUnit (diagonal (fun b ↦ ((col b : ℤ) : K))).det := by
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun b _ ↦
      ((col b).isUnit.map (Int.castRingHom K)).ne_zero)
  rw [eq,rank_mul_eq_left_of_isUnit_det _ _ uc,rank_mul_eq_right_of_isUnit_det _ _ ur]

#print axioms squarefree_diagonal_equivalence
#print axioms squarefree_cut_rank

private theorem sign_diagonal_square {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (s : ι → ℤˣ) :
    diagonal (fun i ↦ ((s i : ℤ) : K)) * diagonal (fun i ↦ ((s i : ℤ) : K)) = 1 := by
  rw [diagonal_mul_diagonal]
  change diagonal _ = diagonal (fun _ ↦ (1 : K))
  congr 1
  funext i
  rcases Int.units_eq_one_or (s i) with h|h <;> simp [h]

/-- The transpose Gram matrices have identical characteristic polynomials.
Over the reals this gives the same singular values with multiplicity. -/
theorem squarefree_gram_charpoly (K : Type*) [CommRing K] (colour : I → I → Bool) :
    let D := cutMatrix colour (generic K I).det
    let P := cutMatrix colour (generic K I).permanent
    (D.transpose * D).charpoly = (P.transpose * P).charpoly := by
  classical
  dsimp only
  obtain ⟨row,col,eq⟩ := squarefree_diagonal_equivalence K colour
  let U := diagonal (fun a ↦ ((row a : ℤ) : K))
  let V := diagonal (fun b ↦ ((col b : ℤ) : K))
  let P := cutMatrix colour (generic K I).permanent
  have hu : U * U = 1 := sign_diagonal_square row
  have hv : V * V = 1 := sign_diagonal_square col
  rw [eq]
  change ((U*P*V).transpose*(U*P*V)).charpoly = (P.transpose*P).charpoly
  have gram : (U*P*V).transpose*(U*P*V) = (V*(P.transpose*P))*V := by
    rw [transpose_mul,transpose_mul,show U.transpose = U from diagonal_transpose _,
      show V.transpose = V from diagonal_transpose _]
    calc
      _ = V * (P.transpose * ((U*U) * (P*V))) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu,Matrix.one_mul]; simp only [Matrix.mul_assoc]
  rw [gram,charpoly_mul_comm,←Matrix.mul_assoc,hv,one_mul]

#print axioms squarefree_gram_charpoly

end PermanentCuts
