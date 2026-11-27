import DeterminantalParametrization

/-! Intersect the space of rank-deficient matrices with the graph of a
polynomial matrix. If the graph meets it only above the origin in the
sense of prime ideals, the input space has at most four parameters. -/
noncomputable section
namespace DeterminantalRegularity.RankParam
open MvPolynomial Matrix Finset
variable (K : Type*) [Field K] (U H : Type*) [Fintype H] [DecidableEq H]
  [Fintype U] [DecidableEq U]

def fullOrigin (A : Matrix H (Slot H) K) : Matrix (Slot H) (Slot H) K :=
  Matrix.of (fun i j ↦ Sum.elim (fun h ↦ A h j) (fun _ ↦ 0) i)

def atOrigin (A : Matrix H (Slot H) K) : Coord K U H →+* K :=
  (MvPolynomial.eval (origin K U H A)).comp (incl K U H)

def evalInput : MvPolynomial U K →+* Coord K U H :=
  eval₂Hom (ground K U H) (input K U H)

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
@[simp] theorem at_ground (A : Matrix H (Slot H) K) (k : K) :
    atOrigin K U H A (ground K U H k) = k := by simp [atOrigin]

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
@[simp] theorem at_input (A : Matrix H (Slot H) K) (u : U) :
    atOrigin K U H A (input K U H u) = 0 := by simp [atOrigin,origin]

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
@[simp] theorem at_entry (A : Matrix H (Slot H) K) (i j : Slot H) :
    atOrigin K U H A (entry K U H i j) = fullOrigin K H A i j := by
  cases i <;> simp [atOrigin,fullOrigin,origin,raw,topRows,coeffRows]

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
private theorem at_eval (A : Matrix H (Slot H) K) :
    (atOrigin K U H A).comp (evalInput K U H) = MvPolynomial.eval 0 := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp [evalInput]
  · intro u; simp [evalInput]

private theorem prime_eq (A : Matrix H (Slot H) K) :
    originPrime K U H A = RingHom.ker (atOrigin K U H A) := by
  have eq : specialize (origin K U H A) univ = C.comp (MvPolynomial.eval (origin K U H A)) := by
    apply MvPolynomial.ringHom_ext
    · intro k; simp
    · intro i; simp
  ext y
  change specialize (origin K U H A) univ (incl K U H y) = 0 ↔
    (MvPolynomial.eval (origin K U H A)) (incl K U H y) = 0
  rw [eq,RingHom.comp_apply]
  simp

def equation (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) (ij : Slot H × Slot H) :
    Coord K U H := entry K U H ij.1 ij.2 - evalInput K U H (L ij.1 ij.2)

def generators (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) : Finset (Coord K U H) := by
  classical exact univ.image (equation K U H L)

def graph (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) : Ideal (Coord K U H) :=
  Ideal.span (generators K U H L : Set (Coord K U H))

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
private theorem graph_eq_iff (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) (J : Ideal (Coord K U H)) :
    graph K U H L ≤ J ↔ ∀ i j, equation K U H L (i,j) ∈ J := by
  classical simp [graph,generators,Ideal.span_le,Set.range_subset_iff]

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
/-- In a quotient killing the graph equations, the generic matrix coincides
entry by entry with the polynomial matrix evaluated at the inputs. -/
theorem quotient_entry (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) {J : Ideal (Coord K U H)}
    (hj : graph K U H L ≤ J) (i j : Slot H) :
    Ideal.Quotient.mk J (entry K U H i j) = Ideal.Quotient.mk J (evalInput K U H (L i j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub,Ideal.Quotient.eq_zero_iff_mem]
  exact (graph_eq_iff K U H L J).mp hj i j

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
private theorem graph_at (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) (A : Matrix H (Slot H) K)
    (at0 : ∀ i j, MvPolynomial.eval 0 (L i j) = fullOrigin K H A i j) :
    graph K U H L ≤ RingHom.ker (atOrigin K U H A) := by
  rw [graph_eq_iff]
  intro i j
  change atOrigin K U H A (entry K U H i j - evalInput K U H (L i j)) = 0
  rw [map_sub,at_entry,← RingHom.comp_apply,at_eval,at0,sub_self]

omit [DecidableEq H] [Fintype U] [DecidableEq U] in
private theorem point_le (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) (A : Matrix H (Slot H) K)
    (at0 : ∀ i j, MvPolynomial.eval 0 (L i j) = fullOrigin K H A i j)
    (J : Ideal (Coord K U H)) (hj : graph K U H L ≤ J) (inputs : ∀ u, input K U H u ∈ J) :
    RingHom.ker (atOrigin K U H A) ≤ J := by
  let q := Ideal.Quotient.mk J
  have zero (u : U) : q (input K U H u) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (inputs u)
  have poly : q.comp (evalInput K U H) = (q.comp (ground K U H)).comp (MvPolynomial.eval 0) := by
    apply MvPolynomial.ringHom_ext
    · intro k; simp [evalInput]
    · intro u; simp [evalInput,zero]
  have matrix (i j : Slot H) : q (entry K U H i j) = q (ground K U H (fullOrigin K H A i j)) := by
    rw [show q (entry K U H i j) = _ from quotient_entry K U H L hj i j]
    have eq := RingHom.congr_fun poly (L i j)
    change q (evalInput K U H (L i j)) = q (ground K U H (MvPolynomial.eval 0 (L i j))) at eq
    rwa [at0] at eq
  have same : q.comp (pull K U H) =
      ((q.comp (ground K U H)).comp (atOrigin K U H A)).comp (pull K U H) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change q (ground K U H k) = q (ground K U H (atOrigin K U H A (ground K U H k)))
      rw [at_ground]
    · intro x
      cases x with
      | inl u =>
        change q (input K U H u) = q (ground K U H (atOrigin K U H A (input K U H u)))
        simp [zero]
      | inr ij =>
        change q (entry K U H ij.1 ij.2) =
          q (ground K U H (atOrigin K U H A (entry K U H ij.1 ij.2)))
        rw [at_entry,matrix]
  intro b hb
  obtain ⟨p,hp⟩ := (paramMap K U H).rangeRestrict_surjective b
  change pull K U H p = b at hp
  have eq := RingHom.congr_fun same p
  change q (pull K U H p) = q (ground K U H (atOrigin K U H A (pull K U H p))) at eq
  change atOrigin K U H A b = 0 at hb
  rw [hp,hb,map_zero,map_zero] at eq
  exact Ideal.Quotient.eq_zero_iff_mem.mp eq

/-- An isolated intersection with the corank-two locus can use at most
four input parameters. The proof uses Krull's height theorem. -/
theorem isolated_graph_card_le (L : Matrix (Slot H) (Slot H) (MvPolynomial U K)) (A : Matrix H (Slot H) K)
    (at0 : ∀ i j, MvPolynomial.eval 0 (L i j) = fullOrigin K H A i j)
    (isolated : ∀ J : Ideal (Coord K U H), J.IsPrime → graph K U H L ≤ J → ∀ u, input K U H u ∈ J) :
    Fintype.card U ≤ 4 := by
  classical
  let M := RingHom.ker (atOrigin K U H A)
  have minimal : M ∈ (graph K U H L).minimalPrimes := by
    refine ⟨⟨RingHom.ker_isPrime _,graph_at K U H L A at0⟩,?_⟩
    intro J hJ _
    exact point_le K U H L A at0 J hJ.2 (isolated J hJ.1 hJ.2)
  have upper := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := generators K U H L) minimal
  have card : (generators K U H L).card ≤ Fintype.card (Slot H × Slot H) := by
    simpa [generators] using (Finset.card_image_le (s := (univ : Finset (Slot H × Slot H)))
      (f := equation K U H L))
  have lower := origin_height K U H A
  rw [prime_eq] at lower
  have both : (Fintype.card (Key U H) : ℕ∞) ≤ (Fintype.card (Slot H × Slot H) : ℕ) :=
    lower.trans (upper.trans (by exact_mod_cast card))
  have natural : Fintype.card (Key U H) ≤ Fintype.card (Slot H × Slot H) := by exact_mod_cast both
  simp [Key,Slot] at natural
  nlinarith

#print axioms isolated_graph_card_le
end DeterminantalRegularity.RankParam
