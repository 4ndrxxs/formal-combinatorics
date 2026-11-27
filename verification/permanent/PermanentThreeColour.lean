import PermanentCoefficientSigns

/-! A three-colour restriction obstructs local reweighting, even when arbitrary
field scalars are allowed. The obstruction persists in every larger size. -/

noncomputable section
open Equiv Equiv.Perm Finset
open scoped Classical
namespace PermanentCuts

private theorem six_terms {K : Type*} [Field K] (two : (2 : K) ≠ 0)
    (u v w : Fin 3 → K) :
    ¬ ∀ p : Perm (Fin 3), u (p 0) * v (p 1) * w (p 2) = ((sign p : ℤ) : K) := by
  intro all
  let a : Perm (Fin 3) := swap 0 1
  let b : Perm (Fin 3) := swap 1 2
  let c : Perm (Fin 3) := swap 0 2
  have val (p : Perm (Fin 3)) {i j k : Fin 3} {s : ℤ}
      (h : p 0=i ∧ p 1=j ∧ p 2=k ∧ (sign p : ℤ)=s) :
      u i * v j * w k = (s : K) := by simpa only [h.1,h.2.1,h.2.2.1,h.2.2.2] using all p
  have e0 : u 0 * v 1 * w 2 = 1 := by simpa using val (Equiv.refl _) (s:=1) (i:=0) (j:=1) (k:=2) (by decide)
  have e1 : u 1 * v 2 * w 0 = 1 := by simpa using val (b.trans a) (s:=1) (i:=1) (j:=2) (k:=0) (by decide)
  have e2 : u 2 * v 0 * w 1 = 1 := by simpa using val (a.trans b) (s:=1) (i:=2) (j:=0) (k:=1) (by decide)
  have o0 : u 1 * v 0 * w 2 = -1 := by simpa using val a (s:= -1) (i:=1) (j:=0) (k:=2) (by decide)
  have o1 : u 0 * v 2 * w 1 = -1 := by simpa using val b (s:= -1) (i:=0) (j:=2) (k:=1) (by decide)
  have o2 : u 2 * v 1 * w 0 = -1 := by simpa using val c (s:= -1) (i:=2) (j:=1) (k:=0) (by decide)
  have clash : (u 0*v 1*w 2) * (u 1*v 2*w 0) * (u 2*v 0*w 1) =
      (u 1*v 0*w 2) * (u 0*v 2*w 1) * (u 2*v 1*w 0) := by ring
  rw [e0,e1,e2,o0,o1,o2] at clash
  apply two
  calc
    (2 : K) = 1 - (-1) := by ring
    _ = 0 := sub_eq_zero.mpr (by simpa using clash)

/-- The edges used by one colour in a full permutation term. -/
def colouredEdges {I : Type*} [Fintype I] [DecidableEq I] (colour : I → I → Fin 3)
    (k : Fin 3) (p : Perm I) : Finset (I × I) :=
  (univ.filter (fun i ↦ colour i (p i) = k)).image (fun i ↦ (i,p i))

private theorem colouredEdges_mem {I : Type*} [Fintype I] [DecidableEq I]
    (colour : I → I → Fin 3) (k : Fin 3) (p : Perm I) (i j : I) :
    (i,j) ∈ colouredEdges colour k p ↔ colour i j = k ∧ p i = j := by
  simp [colouredEdges]
  aesop

/-- A three-row, three-column submatrix with a distinct constant colour per row
obstructs every factorization of the determinant coefficients into three
functions of the local monomials. The remaining entries have arbitrary colours. -/
theorem striped_minor_obstruction {J K : Type*} [Fintype J] [DecidableEq J] [Field K]
    (two : (2 : K) ≠ 0)
    (colour : (Fin 3 ⊕ J) → (Fin 3 ⊕ J) → Fin 3)
    (stripes : ∀ i j, colour (.inl i) (.inl j) = i) :
    ¬ ∃ d : Fin 3 → Finset ((Fin 3 ⊕ J) × (Fin 3 ⊕ J)) → K, ∀ p : Perm (Fin 3 ⊕ J),
      (∏ k, d k (colouredEdges colour k p)) =
        (generic K (Fin 3 ⊕ J)).det.coeff (exponents p) := by
  rintro ⟨d, hd⟩
  let emb (p : Perm (Fin 3)) := Equiv.sumCongr p (Equiv.refl J)
  have local_eq (k : Fin 3) (p q : Perm (Fin 3)) (h : p k=q k) :
      colouredEdges colour k (emb p) = colouredEdges colour k (emb q) := by
    ext ⟨i,j⟩
    rw [colouredEdges_mem,colouredEdges_mem]
    cases i with
    | inr i => rfl
    | inl i =>
      cases j with
      | inr j => simp [emb]
      | inl j =>
        by_cases e : i=k
        · subst i
          simp [emb,stripes,h]
        · simp [emb,stripes,e]
  let f (k j : Fin 3) := d k (colouredEdges colour k (emb (swap k j)))
  have value (k : Fin 3) (p : Perm (Fin 3)) : f k (p k) = d k (colouredEdges colour k (emb p)) := by
    change d k _ = d k _
    congr 1
    exact local_eq k _ _ (swap_apply_left _ _)
  apply six_terms two (f 0) (f 1) (f 2)
  intro p
  have e := hd (emb p)
  rw [(generic_matching K _).2] at e
  simpa only [Fin.prod_univ_three,←value,emb,sign_sumCongr,sign_refl,mul_one,mul_assoc] using e

#print axioms striped_minor_obstruction
/-- Local scalar weights must respect every identity between multisets of
local monomials, including identities that do not come from a striped minor. -/
theorem matching_trade {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
    (colour : I → I → Fin 3) (pos neg : List (Perm I))
    (labels : ∀ k, (pos.map (colouredEdges colour k)).Perm (neg.map (colouredEdges colour k)))
    (different : (pos.map (fun p ↦ ((sign p : ℤ) : K))).prod ≠
      (neg.map (fun p ↦ ((sign p : ℤ) : K))).prod) :
    ¬ ∃ d : Fin 3 → Finset (I × I) → K, ∀ p : Perm I,
      (∏ k, d k (colouredEdges colour k p)) = (generic K I).det.coeff (exponents p) := by
  rintro ⟨d,hd⟩
  let part (k : Fin 3) (ps : List (Perm I)) := (ps.map (fun p ↦ d k (colouredEdges colour k p))).prod
  have factor (ps : List (Perm I)) :
      (ps.map (fun p ↦ ((sign p : ℤ) : K))).prod = part 0 ps * part 1 ps * part 2 ps := by
    induction ps with
    | nil => simp [part]
    | cons p ps ih =>
      have hp := hd p
      rw [Fin.prod_univ_three,(generic_matching K p).2] at hp
      simp only [List.map_cons,List.prod_cons,←hp,ih]
      simp [part,mul_assoc,mul_left_comm]
  have eq (k) : part k pos = part k neg := by
    have h := ((labels k).map (d k)).prod_eq
    simpa [part,List.map_map,Function.comp_def] using h
  apply different
  rw [factor,factor,eq,eq,eq]

/-- The rows of this four by four colouring read 2112, 2012, 1011 and 0000. -/
def fourColour (i j : Fin 4) : Fin 3 :=
  ![![2,1,1,2], ![2,0,1,2], ![1,0,1,1], ![0,0,0,0]] i j

private def positiveTrade : List (Perm (Fin 4)) :=
  [Equiv.refl _,
   (swap 0 2).trans (swap 1 0),
   (swap 0 2).trans (swap 0 3),
   (swap 0 2).trans (swap 1 3),
   (swap 0 3).trans (swap 1 2)]
private def negativeTrade : List (Perm (Fin 4)) :=
  [swap 1 2,
   ((swap 0 2).trans (swap 1 0)).trans (swap 1 3),
   swap 0 2,
   ((swap 0 2).trans (swap 1 3)).trans (swap 0 1),
   swap 0 3]

/-- Every three by three submatrix contains a nonconstant row and a
nonconstant column. On four indices deleting one index enumerates all triples. -/
theorem four_no_striped_minor :
    (∀ r c : Fin 4, ∃ i j l, i≠r ∧ j≠c ∧ l≠c ∧ fourColour i j ≠ fourColour i l) ∧
    (∀ r c : Fin 4, ∃ j i l, j≠c ∧ i≠r ∧ l≠r ∧ fourColour i j ≠ fourColour l j) := by decide +kernel

/-- Even without a striped three by three minor, no three local scalar
weights produce the determinant signs over a field of characteristic other than two. -/
theorem four_trade_obstruction {K : Type*} [Field K] (two : (2 : K) ≠ 0) :
    ¬ ∃ d : Fin 3 → Finset (Fin 4 × Fin 4) → K, ∀ p : Perm (Fin 4),
      (∏ k, d k (colouredEdges fourColour k p)) = (generic K (Fin 4)).det.coeff (exponents p) := by
  apply matching_trade fourColour positiveTrade negativeTrade
  · decide +kernel
  · have p : (positiveTrade.map (fun σ ↦ (sign σ : ℤ))).prod = 1 := by decide
    have n : (negativeTrade.map (fun σ ↦ (sign σ : ℤ))).prod = -1 := by decide
    have castProd (ps : List (Perm (Fin 4))) :
        (ps.map (fun σ ↦ ((sign σ : ℤ) : K))).prod = ((ps.map (fun σ ↦ (sign σ : ℤ))).prod : ℤ) := by
      induction ps with
      | nil => simp
      | cons p ps ih => simp [ih]
    rw [castProd,castProd,p,n]
    push_cast
    intro e
    apply two
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 0 := sub_eq_zero.mpr e

#print axioms four_no_striped_minor
#print axioms matching_trade
#print axioms four_trade_obstruction

/-- One multiplicative scalar from each colour reproduces every permutation coefficient. -/
abbrev HasLocalWeights (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
    (colour : I → I → Fin 3) :=
  ∃ d : Fin 3 → Finset (I × I) → K, ∀ p : Perm I,
    (∏ k, d k (colouredEdges colour k p)) = (generic K I).det.coeff (exponents p)

/-- Fixing a perfect matching on the complementary rows and columns lifts
any obstruction to arbitrary scalar weights from a square submatrix. -/
theorem obstruction_extension {I J K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Field K] (small : I → I → Fin 3)
    (large : (I ⊕ J) → (I ⊕ J) → Fin 3)
    (restrict : ∀ i j, large (.inl i) (.inl j) = small i j)
    (obstruction : ¬ HasLocalWeights K small) : ¬ HasLocalWeights K large := by
  rintro ⟨d,hd⟩
  let liftSet (k : Fin 3) (a : Finset (I × I)) : Finset ((I ⊕ J) × (I ⊕ J)) :=
    a.image (fun e ↦ (Sum.inl e.1,Sum.inl e.2)) ∪
      (univ.filter (fun j : J ↦ large (.inr j) (.inr j) = k)).image (fun j ↦ (Sum.inr j,Sum.inr j))
  have lifted (k : Fin 3) (p : Perm I) :
      colouredEdges large k (Equiv.sumCongr p (Equiv.refl J)) = liftSet k (colouredEdges small k p) := by
    ext ⟨i,j⟩
    rw [colouredEdges_mem]
    cases i <;> cases j <;> simp [liftSet,mem_image,Prod.exists,colouredEdges_mem,restrict]
    aesop
  apply obstruction
  refine ⟨fun k a ↦ d k (liftSet k a),?_⟩
  intro p
  have e := hd (Equiv.sumCongr p (Equiv.refl J))
  rw [(generic_matching K _).2] at e ⊢
  simpa only [lifted,sign_sumCongr,sign_refl,mul_one] using e

/-- Extend the displayed four-by-four grid by filling every new entry with colour zero. -/
def paddedFour (J : Type*) : (Fin 4 ⊕ J) → (Fin 4 ⊕ J) → Fin 3
  | .inl i, .inl j => fourColour i j
  | _, _ => 0

private theorem padded_two {J : Type*} (i j : Fin 4 ⊕ J) :
    paddedFour J i j = 2 ↔ (i = .inl 0 ∨ i = .inl 1) ∧ (j = .inl 0 ∨ j = .inl 3) := by
  have finite_case : ∀ i j : Fin 4, fourColour i j = 2 ↔
      (i=0 ∨ i=1) ∧ (j=0 ∨ j=3) := by decide
  cases i <;> cases j <;> simp [paddedFour,finite_case]

private theorem three_distinct {ι : Type*} (f : Fin 3 ↪ ι) (x y : ι) :
    ¬ ∀ i, f i=x ∨ f i=y := by
  intro h
  have d01 : f 0 ≠ f 1 := f.injective.ne (by decide)
  have d02 : f 0 ≠ f 2 := f.injective.ne (by decide)
  have d12 : f 1 ≠ f 2 := f.injective.ne (by decide)
  rcases h 0 with a|a <;> rcases h 1 with b|b <;> rcases h 2 with c|c <;> grind

/-- A separating three-way partition without any striped three by three
submatrix exists at every order at least four, over every field of characteristic
different from two. The row and column embeddings are independent. -/
theorem padded_obstruction {J K : Type*} [Fintype J] [DecidableEq J] [Field K] (two : (2 : K) ≠ 0) :
    (¬ HasLocalWeights K (paddedFour J)) ∧
    (∀ r c : Fin 3 ↪ (Fin 4 ⊕ J), ¬ ∀ i j, paddedFour J (r i) (c j) = i) ∧
    (∀ r c : Fin 3 ↪ (Fin 4 ⊕ J), ¬ ∀ i j, paddedFour J (r i) (c j) = j) := by
  refine ⟨obstruction_extension fourColour (paddedFour J) (fun _ _ ↦ rfl) (four_trade_obstruction two),?_,?_⟩
  · intro r c h
    exact three_distinct c (.inl 0) (.inl 3) (fun j ↦ ((padded_two _ _).mp (h 2 j)).2)
  · intro r c h
    exact three_distinct r (.inl 0) (.inl 1) (fun i ↦ ((padded_two _ _).mp (h i 2)).1)

#print axioms obstruction_extension
#print axioms padded_obstruction

end PermanentCuts
