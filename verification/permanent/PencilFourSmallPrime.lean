import PencilMiddleLayers

/-! A square matrix of linear forms in one variable with five full
four-step chains at infinity necessarily degenerates over a prime of
degree at most fourteen. No algebraic closure is needed. -/
noncomputable section
open Matrix Finset Polynomial
namespace PencilLayers
variable {K : Type*} [Field K]

private theorem generic_minor {m n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (A : Matrix m n K[X]) (r : k → m) (c : k → n)
    (top : ∀ i j, PencilWeight.Top (A (r i) (c j)) 1 ((1 : Matrix k k K) i j)) :
    Fintype.card k ≤ (A.map (algebraMap K[X] (RatFunc K))).rank := by
  let T := A.submatrix r c
  let g := algebraMap K[X] (RatFunc K)
  have h := (PencilWeight.top_det T (fun _ ↦ 1) (1 : Matrix k k K) top).2
  have nz : T.det ≠ 0 := by
    intro z
    rw [z,coeff_zero,Matrix.det_one] at h
    exact zero_ne_one h
  have nk : (g.mapMatrix T).det ≠ 0 := by
    rw [←g.map_det]
    exact (map_ne_zero_iff g (IsFractionRing.injective _ _)).mpr nz
  have nk' : ((A.map g).submatrix r c).det ≠ 0 := nk
  have le := Matrix.rank_submatrix_le (A.map g) r c
  rwa [Matrix.rank_of_det_ne_zero nk'] at le

private theorem full_generic (A : Matrix (Layer 4) (Layer 4) K[X])
    (top : ∀ i j, PencilWeight.Top (A i j) 1 (shift K 4 i j)) :
    15 ≤ (A.map (algebraMap K[X] (RatFunc K))).rank := by
  have ht (i j : Layer 3) : PencilWeight.Top (A (tail 3 i) (head 3 j)) 1
      ((1 : Matrix (Layer 3) (Layer 3) K) i j) := by
    rw [←pinned (K:=K)]
    exact top _ _
  have le := generic_minor A (tail 3) (head 3) ht
  simpa only [Layer,Fintype.card_prod,Fintype.card_fin] using le

private theorem mapped_middle {H : Type*} [Field H] (g : K[X] →+* H)
    (A : Matrix (Layer 4) (Layer 4) K[X]) (nil : A^4=0)
    (rows : ∀ x : Fin 5, ∀ j, A (0,x) j=0) (cols : ∀ i, ∀ y : Fin 5, A i (3,y)=0)
    (full : 15 ≤ (A.map g).rank) :
    (((middle A).map g)^2)=0 ∧ ((middle A).map g).rank=5 := by
  have n : (A.map g)^4=0 := by
    change (g.mapMatrix A)^4=0
    rw [←map_pow,nil,map_zero]
  exact middle_field (A.map g) (fun x j ↦ by change g (A (0,x) j)=0; rw [rows,map_zero])
    (fun i y ↦ by change g (A i (3,y))=0; rw [cols,map_zero]) n full

theorem normalized_small_bad_prime (A : Matrix (Layer 4) (Layer 4) K[X])
    (top : ∀ i j, PencilWeight.Top (A i j) 1 (shift K 4 i j))
    (nil : A^4=0) (nil₁ : (shift K 4)^4=0) (full₁ : ((shift K 4)^3).rank=5) :
    ∃ p : K[X], ∃ hp : Irreducible p, p.natDegree < 15 ∧
      (let _ := Fact.mk hp; ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5) := by
  classical
  by_contra none
  have good (p : K[X]) (hp : Irreducible p) [Fact (Irreducible p)] (d : p.natDegree < 15) :
      ((A.map (AdjoinRoot.mk p))^3).rank=5 := by
    by_contra drop
    exact none ⟨p,hp,d,drop⟩
  have total : (∑ j : Layer 4, j.1.val) = 30 := by decide
  obtain ⟨p,hp,_,drop⟩ := PencilChain.bad_prime_of_slope (k:=Fin 5) (s:=4)
    (Or.inr rfl) A (shift K 4) top nil nil₁ (by simpa using full₁) (by rw [total]; decide)
  let _ : Fact (Irreducible p) := ⟨hp⟩
  change ((A.map (AdjoinRoot.mk p))^3).rank ≠ 5 at drop
  have big : 15 ≤ p.natDegree := le_of_not_gt (fun h ↦ drop (good p hp h))
  have nr : (A.map (AdjoinRoot.mk p))^4=0 := by
    change ((AdjoinRoot.mk p).mapMatrix A)^4=0
    rw [←map_pow,nil,map_zero]
  obtain ⟨rows,cols⟩ := fixed_flags p big A top (insufficient_rank _ nr drop)
  let B := middle A
  let b := middle (shift K 4)
  have gen := (mapped_middle (algebraMap K[X] (RatFunc K)) A nil rows cols (full_generic A top)).1
  let g := algebraMap K[X] (RatFunc K)
  have square : B^2=0 := by
    have eq : g.mapMatrix (B^2) = g.mapMatrix 0 := by rw [map_pow,map_zero]; exact gen
    apply Matrix.ext
    intro i j
    apply IsFractionRing.injective K[X] (RatFunc K)
    exact congrFun (congrFun eq i) j
  obtain ⟨nilB,rankB⟩ := middle_field (shift K 4) shift_rows shift_cols nil₁
    (rank_of_full_last _ nil₁ full₁).ge
  have leading (i j : Layer 2) : PencilWeight.Top (B i j) 1 (b i j) := top _ _
  obtain ⟨q,hq,qd,lose⟩ := PencilChain.square_zero_five_bad B b leading square nilB rankB
  let _ : Fact (Irreducible q) := ⟨hq⟩
  change (B.map (AdjoinRoot.mk q)).rank ≠ 5 at lose
  have nq : (A.map (AdjoinRoot.mk q))^4=0 := by
    change ((AdjoinRoot.mk q).mapMatrix A)^4=0
    rw [←map_pow,nil,map_zero]
  exact lose (mapped_middle (AdjoinRoot.mk q) A nil rows cols
    (rank_of_full_last _ nq (good q hq (by omega))).ge).2

#print axioms normalized_small_bad_prime
end PencilLayers
