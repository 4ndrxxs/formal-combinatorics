module

public import Quantum.PartialArray
public import Quantum.MaximalHypercubes

/-! Two quantum Latin squares can share exactly the coordinate rays of an
identical first row, irrespective of their original cardinalities. -/

@[expose] public section
noncomputable section
namespace QuantumCertificate

open Finset Complex
open scoped ComplexConjugate

structure BasedSquare (n c : ℕ) [NeZero n] where
  entry : Fin n → Fin n → Space n
  nz : ∀ i j, entry i j ≠ 0
  rows : ∀ i, ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = entry i
  cols : ∀ j, ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = fun i => entry i j
  first : ∀ j, entry 0 j = EuclideanSpace.single j 1
  count : (rayRange (fun p : Cell n => entry p.1 p.2) (fun p => nz p.1 p.2)).ncard = c

def BasedSquare.rays {n c : ℕ} [NeZero n] (b : BasedSquare n c) :
    Set (Projectivization ℂ (Space n)) :=
  rayRange (fun p : Cell n => b.entry p.1 p.2) (fun p => b.nz p.1 p.2)

theorem BasedSquare.ncard_rays {n c : ℕ} [NeZero n] (b : BasedSquare n c) :
    b.rays.ncard = c := b.count

theorem BasedSquare.realized {n c : ℕ} [NeZero n] (b : BasedSquare n c) : Realized n c :=
  ⟨b.entry,b.nz,b.rows,b.cols,b.count⟩

theorem single_nz {n : ℕ} (i : Fin n) : (EuclideanSpace.single i 1 : Space n) ≠ 0 := by
  intro h
  have hh := congrArg (fun w : Space n => w i) h
  simp at hh

def coordinateRay {n : ℕ} (i : Fin n) : Projectivization ℂ (Space n) :=
  Projectivization.mk ℂ (EuclideanSpace.single i 1 : Space n) (single_nz i)

def coordinateRays (n : ℕ) : Set (Projectivization ℂ (Space n)) := Set.range (@coordinateRay n)

theorem coordinateRay_injective (n : ℕ) : Function.Injective (@coordinateRay n) := by
  intro i j h
  obtain ⟨z,hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  by_contra hne
  have hh := congrArg (fun w : Space n => w i) hz
  change z * (EuclideanSpace.single j 1 : Space n) i = (EuclideanSpace.single i 1 : Space n) i at hh
  simp [hne] at hh

theorem ncard_coordinateRays (n : ℕ) : (coordinateRays n).ncard = n := by
  rw [coordinateRays, Set.ncard_range_of_injective (coordinateRay_injective _)]
  simp

theorem BasedSquare.coordinate_subset {n c : ℕ} [NeZero n] (b : BasedSquare n c) :
    coordinateRays n ⊆ b.rays := by
  rintro _ ⟨i,rfl⟩
  refine ⟨(0,i),?_⟩
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1,by simp [b.first]⟩

theorem Realized.based {n c : ℕ} [NeZero n] (h : Realized n c) : Nonempty (BasedSquare n c) := by
  obtain ⟨v,hn,rows,cols,hc⟩ := h
  obtain ⟨B,hB⟩ := rows 0
  let f := B.repr
  refine ⟨⟨fun i j => f (v i j),fun i j he => hn i j (f.injective (he.trans (map_zero f).symm)),
    ?_,?_,?_,?_⟩⟩
  · intro i
    obtain ⟨b,hb⟩ := rows i
    exact ⟨b.map f,funext fun j => by simp [hb]⟩
  · intro j
    obtain ⟨b,hb⟩ := cols j
    exact ⟨b.map f,funext fun i => by simpa using congrArg f (congrFun hb i)⟩
  · intro j
    rw [← hB]
    exact B.repr_self j
  · let s := rayRange (fun p : Cell n => v p.1 p.2) (fun p => hn p.1 p.2)
    have he : rayRange (fun p : Cell n => f (v p.1 p.2))
        (fun p he => hn _ _ (f.injective (he.trans (map_zero f).symm))) =
        (Projectivization.map f.toLinearEquiv.toLinearMap f.injective) '' s := by
      ext x
      constructor
      · rintro ⟨p,rfl⟩
        exact ⟨_,⟨p,rfl⟩,rfl⟩
      · rintro ⟨_,⟨p,rfl⟩,rfl⟩
        exact ⟨p,rfl⟩
    rw [he,Set.ncard_image_of_injective _ (Projectivization.map_injective _ f.injective)]
    exact hc

def diagonalPhaseLinear {n : ℕ} (z : ℂ) : Space n →ₗ[ℂ] Space n where
  toFun v := WithLp.toLp 2 (fun i => z^i.val * v i)
  map_add' v w := by
    ext i
    change z^i.val * (v i + w i) = z^i.val*v i + z^i.val*w i
    ring
  map_smul' t v := by
    ext i
    change z^i.val * (t*v i) = t*(z^i.val*v i)
    ring

theorem diagonalPhaseLinear_inner {n : ℕ} {z : ℂ} (hz : conj z*z=1) (v w : Space n) :
    inner ℂ (diagonalPhaseLinear z v) (diagonalPhaseLinear z w) = inner ℂ v w := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply sum_congr rfl
  intro i _
  change (z^i.val * w i)*conj (z^i.val * v i) = w i * conj (v i)
  rw [map_mul,mul_mul_mul_comm,map_pow,← mul_pow,mul_comm z,hz,one_pow,one_mul]

def diagonalPhaseIsometry {n : ℕ} (z : ℂ) (hz : conj z*z=1) : Space n →ₗᵢ[ℂ] Space n :=
  (diagonalPhaseLinear z).isometryOfInner (diagonalPhaseLinear_inner hz)

def BasedSquare.twistEntry {n c : ℕ} [NeZero n] (b : BasedSquare n c)
    (z : ℂ) (hz : conj z*z=1) (i j : Fin n) : Space n :=
  conj (z^j.val) • diagonalPhaseIsometry z hz (b.entry i j)

theorem twistGram {n c : ℕ} [NeZero n] (b : BasedSquare n c) (z : ℂ) (hz : conj z*z=1)
    (i j k l : Fin n) :
    inner ℂ (b.twistEntry z hz i j) (b.twistEntry z hz k l) =
      z^j.val * conj (z^l.val) * inner ℂ (b.entry i j) (b.entry k l) := by
  simp [BasedSquare.twistEntry,inner_smul_left,inner_smul_right,
    LinearIsometry.inner_map_map,mul_assoc]
  ring

theorem phase_pow_unit {z : ℂ} (hz : conj z*z=1) (n : ℕ) :
    z^n * conj (z^n) = 1 := by
  rw [map_pow, ← mul_pow,mul_comm z,hz,one_pow]

theorem basedONB {n : ℕ} [NeZero n] (v : Fin n → Space n)
    (h : ∀ i j, inner ℂ (v i) (v j) = if i=j then 1 else 0) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = v := by
  classical
  have ortho := orthonormal_iff_ite.mpr h
  exact ⟨OrthonormalBasis.mk ortho (ortho.linearIndependent.span_eq_top_of_card_eq_finrank
    (by simp)).ge,OrthonormalBasis.coe_mk _ _⟩

def BasedSquare.twist {n c : ℕ} [NeZero n] (b : BasedSquare n c) (z : ℂ) (hz : conj z*z=1) :
    BasedSquare n c := by
  let f := diagonalPhaseIsometry (n:=n) z hz
  have hn : z ≠ 0 := by intro h; simp [h] at hz
  have nz (i j : Fin n) : b.twistEntry z hz i j ≠ 0 := by
    apply smul_ne_zero (by simpa using pow_ne_zero j.val hn)
    exact fun h => b.nz i j (f.injective (h.trans (map_zero f).symm))
  refine ⟨b.twistEntry z hz,nz,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨B,hB⟩ := b.rows i
    apply basedONB
    intro j k
    rw [twistGram,← hB, B.inner_eq_ite]
    split <;> rename_i h
    · subst k
      simp only [phase_pow_unit hz,mul_one]
    · simp
  · intro j
    obtain ⟨B,hB⟩ := b.cols j
    apply basedONB
    intro i k
    rw [twistGram,phase_pow_unit hz,one_mul,← congrFun hB i,← congrFun hB k,B.inner_eq_ite]
  · intro j
    ext k
    change conj (z^j.val) * (z^k.val * b.entry 0 j k) = (EuclideanSpace.single j 1 : Space n) k
    rw [b.first]
    by_cases h : k=j
    · subst k
      simpa [mul_comm] using phase_pow_unit hz j.val
    · simp [h]
  · let proj := Projectivization.map f.toLinearMap f.injective
    have pt (p : Cell n) :
        Projectivization.mk ℂ (b.twistEntry z hz p.1 p.2) (nz _ _) =
        proj (Projectivization.mk ℂ (b.entry p.1 p.2) (b.nz _ _)) := by
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      exact ⟨conj (z^p.2.val),rfl⟩
    have he : rayRange (fun p : Cell n => b.twistEntry z hz p.1 p.2) (fun p=>nz p.1 p.2) =
        proj '' b.rays := by
      ext x
      constructor
      · rintro ⟨p,rfl⟩
        exact ⟨_,⟨p,rfl⟩,(pt p).symm⟩
      · rintro ⟨_,⟨p,rfl⟩,rfl⟩
        exact ⟨p,pt p⟩
    rw [he,Set.ncard_image_of_injective _ (Projectivization.map_injective _ f.injective)]
    exact b.count

theorem BasedSquare.twist_entry {n c : ℕ} [NeZero n] (b : BasedSquare n c)
    (z : ℂ) (hz : conj z*z=1) (i j : Fin n) :
    (b.twist z hz).entry i j = b.twistEntry z hz i j := rfl

theorem two_coordinates {n : ℕ} (v : Space n) (hv : v ≠ 0)
    (h : Projectivization.mk ℂ v hv ∉ coordinateRays n) :
    ∃ i j : Fin n, i ≠ j ∧ v i ≠ 0 ∧ v j ≠ 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hall
    exact hv (by ext i; exact hall i)
  by_cases hother : ∃ j, i ≠ j ∧ v j ≠ 0
  · obtain ⟨j,hij,hj⟩ := hother
    exact ⟨i,j,hij,hi,hj⟩
  · exfalso
    apply h
    refine ⟨i,?_⟩
    symm
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨v i,?_⟩
    ext j
    change v i * (EuclideanSpace.single i 1 : Space n) j = v j
    by_cases eq : i=j
    · subst j
      simp
    · have hz : v j=0 := by by_contra hn; exact hother ⟨j,eq,hn⟩
      simp [Ne.symm eq,hz]

def collision {n : ℕ} (v w : Space n) (i j : Fin n) : Polynomial ℂ :=
  Polynomial.monomial j.val (v i * w j) - Polynomial.monomial i.val (v j * w i)

theorem collision_ne {n : ℕ} {v w : Space n} {i j : Fin n}
    (h : i ≠ j) (hi : v i ≠ 0) (hj : w j ≠ 0) : collision v w i j ≠ 0 := by
  intro he
  have hval : i.val ≠ j.val := fun e => h (Fin.ext e)
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff j.val) he
  simp [collision,hval,hi,hj] at hc

/-- A diagonal unitary with successive powers of a single phase removes all
noncoordinate intersections. Column rephasings restore the literal first row. -/
theorem BasedSquare.separate {n c₁ c₂ : ℕ} [NeZero n] (a : BasedSquare n c₁)
    (b : BasedSquare n c₂) : ∃ b' : BasedSquare n c₂, a.rays ∩ b'.rays = coordinateRays n := by
  classical
  let v (p : Cell n) := a.entry p.1 p.2
  let w (p : Cell n) := b.entry p.1 p.2
  let I := { t : (Cell n × Cell n) × (Fin n × Fin n) //
    t.2.1 ≠ t.2.2 ∧ v t.1.1 t.2.1 ≠ 0 ∧ w t.1.2 t.2.2 ≠ 0 }
  let P (t : I) := collision (v t.val.1.1) (w t.val.1.2) t.val.2.1 t.val.2.2
  have hP (t : I) : P t ≠ 0 := collision_ne t.property.1 t.property.2.1 t.property.2.2
  obtain ⟨z,hz,hgood⟩ := MaximalHypercubes.avoid_polynomials P hP
  refine ⟨b.twist z hz,Set.Subset.antisymm ?_ (Set.subset_inter a.coordinate_subset
    (b.twist z hz).coordinate_subset)⟩
  rintro x ⟨⟨p,rfl⟩,⟨q,hq⟩⟩
  by_contra hn
  obtain ⟨i,j,hij,hvi,hvj⟩ := two_coordinates (v p) (a.nz _ _) hn
  obtain ⟨s,he⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hq.symm
  have hcoord (k : Fin n) :
      s * (conj (z^q.2.val) * (z^k.val * w q k)) = v p k :=
    congrArg (fun u : Space n => u k) he
  have hwj : w q j ≠ 0 := by
    intro e
    apply hvj
    simpa [e] using (hcoord j).symm
  let t : I := ⟨((p,q),(i,j)),hij,hvi,hwj⟩
  apply hgood t
  change (collision (v p) (w q) i j).eval z = 0
  rw [collision,Polynomial.eval_sub,Polynomial.eval_monomial,Polynomial.eval_monomial,
    ← hcoord i, ← hcoord j]
  ring

theorem based_pair {n c₁ c₂ : ℕ} [NeZero n] (_hn : 2≤n)
    (h₁ : Realized n c₁) (h₂ : Realized n c₂) :
    ∃ a : BasedSquare n c₁, ∃ b : BasedSquare n c₂, a.rays ∩ b.rays = coordinateRays n := by
  obtain ⟨a⟩ := h₁.based
  obtain ⟨b⟩ := h₂.based
  exact ⟨a,a.separate b⟩

#print axioms Realized.based
#print axioms based_pair

end QuantumCertificate
