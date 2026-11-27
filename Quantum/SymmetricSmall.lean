module
public import Quantum.BasedPairs
public import Quantum.Bounds
public import Std.Tactic.BVDecide

/-! Small symmetric quantum Latin squares over the complex numbers. -/
@[expose] public section
noncomputable section
namespace SymmetricSmall

open QuantumCertificate Complex Finset
open scoped ComplexConjugate BigOperators

/-- The first basis is normalized by one global isometry. -/
def Has (n c : ℕ) [NeZero n] : Prop :=
  ∃ b : BasedSquare n c, ∀ i j, b.entry i j = b.entry j i

def fourRaw : Fin 6 → Fin 4 → ℤ :=
  ![![5,0,0,0], ![0,5,0,0], ![0,0,5,0], ![0,0,0,5], ![3,0,0,4], ![4,0,0,-3]]

def fourReps (j : Fin 6) (k : Fin 4) : IQ := (fourRaw j k,0)

def fourLabels : Fin 4 → Fin 4 → Fin 6 :=
  ![![0,1,2,3], ![1,5,4,2], ![2,4,5,1], ![3,2,1,0]]

theorem four_six : Has 4 6 := by
  classical
  let v (i j : Fin 4) := vector 1 25 (fourReps (fourLabels i j))
  have symm : ∀ i j, fourLabels i j = fourLabels j i := by decide +kernel
  have rows (i : Fin 4) :
      ∃ b : OrthonormalBasis (Fin 4) ℂ (Space 4), ⇑b = v i := by
    apply basis_of_test (by decide : 0<25)
    exact (by decide +kernel : ∀ i, GramTest 1 25 (fun j => fourReps (fourLabels i j))) i
  have sy (i j) : v i j = v j i := congrArg (fun k => vector 1 25 (fourReps k)) (symm i j)
  have nz (i j) : v i j ≠ 0 := by
    obtain ⟨b,hb⟩:=rows i
    exact (congrArg (fun w => w j) hb) ▸ b.orthonormal.ne_zero j
  have surv : ∀ k, ∃ ij : Cell 4, fourLabels ij.1 ij.2 = k := by decide +kernel
  have rne (k : Fin 6) : vector 1 25 (fourReps k) ≠ 0 := by
    obtain ⟨⟨i,j⟩,rfl⟩:=surv k
    exact nz i j
  let ray (k : Fin 6) := Projectivization.mk ℂ (vector 1 25 (fourReps k)) (rne k)
  have inj : Function.Injective ray := by
    intro i j h
    by_contra hne
    obtain ⟨k,l,hkl⟩ := (by decide +kernel : Separated 1 fourReps) i j hne
    obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have coord (s : Fin 4) : t*embed 1 (fourReps j s) = embed 1 (fourReps i s) := by
      have H := congrArg (fun z : Space 4 => z s) ht
      change t * ((_ : ℂ) * _) = _ * _ at H
      apply mul_left_cancel₀ (show (Real.sqrt (25:ℝ) : ℂ)⁻¹ ≠ 0 by norm_num)
      linear_combination H
    apply hkl (embed_injective (by decide : 0<1) ?_)
    rw [embed_times,embed_times,← coord k,← coord l]
    ring
  refine ⟨⟨v,nz,rows,?_,?_,?_⟩,sy⟩
  · intro j
    simpa only [funext (fun i => sy i j)] using rows j
  · intro j
    ext k
    fin_cases j <;> fin_cases k <;>
      norm_num [v,vector,fourReps,fourRaw,fourLabels,embed] <;>
      apply Complex.ext <;> norm_num [Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change (Set.range (ray ∘ (fun p : Cell 4 => fourLabels p.1 p.2))).ncard = 6
    rw [Function.Surjective.range_comp surv,Set.ncard_range_of_injective inj]
    simp

#print axioms four_six

theorem row_orth {n c : ℕ} [NeZero n] (b : BasedSquare n c) (i j k : Fin n)
    (h : j ≠ k) : inner ℂ (b.entry i j) (b.entry i k) = 0 := by
  obtain ⟨B,hB⟩ := b.rows i
  simp [← hB,B.inner_eq_ite,h]

theorem left_zero {n c : ℕ} [NeZero n] (b : BasedSquare n c)
    (sy : ∀ i j, b.entry i j = b.entry j i) (i j : Fin n) (hj : j ≠ 0) :
    b.entry i j i = 0 := by
  have h := row_orth b i 0 j hj.symm
  simpa [sy i 0,b.first,EuclideanSpace.inner_single_left] using h

theorem edge_zero {n c : ℕ} [NeZero n] (b : BasedSquare n c)
    (sy : ∀ i j, b.entry i j = b.entry j i)
    (i j k : Fin n) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k=i ∨ k=j) :
    b.entry i j k = 0 := by
  rcases hk with rfl | rfl
  · exact left_zero b sy k j hj
  · rw [sy i k]
    exact left_zero b sy k i hi

def edgeL : Fin 6 → Fin 5 := ![1,1,1,2,2,3]
def edgeR : Fin 6 → Fin 5 := ![2,3,4,3,4,4]
def triangle : Fin 4 → Fin 3 → Fin 6 := ![![3,4,5],![1,2,5],![0,2,4],![0,1,3]]

def edgeVec {c : ℕ} (b : BasedSquare 5 c) (e : Fin 6) : Space 5 :=
  b.entry (edgeL e) (edgeR e)

theorem edgeVec_zero {c : ℕ} (b : BasedSquare 5 c) (sy : ∀ i j, b.entry i j = b.entry j i)
    (e : Fin 6) (k : Fin 5) (hk : k=edgeL e ∨ k=edgeR e) : edgeVec b e k=0 :=
  edge_zero b sy _ _ k ((by decide +kernel : ∀ e, edgeL e ≠ 0) e)
    ((by decide +kernel : ∀ e, edgeR e ≠ 0) e) hk

theorem edgeVec_orth {c : ℕ} (b : BasedSquare 5 c) (sy : ∀ i j, b.entry i j = b.entry j i)
    (l : Fin 4) (s t : Fin 3) (hst : s ≠ t) :
    inner ℂ (edgeVec b (triangle l s)) (edgeVec b (triangle l t)) = 0 := by
  let ends (e : Fin 6) (i j : Fin 5) := (edgeL e=i ∧ edgeR e=j) ∨ (edgeL e=j ∧ edgeR e=i)
  have E : ∀ l s t, s ≠ t → ∃ i j k, j ≠ k ∧ ends (triangle l s) i j ∧
      ends (triangle l t) i k := by decide +kernel
  obtain ⟨i,j,k,hjk,hs,ht⟩ := E l s t hst
  have entry {e i j} (h : ends e i j) : edgeVec b e = b.entry i j := by
    rcases h with ⟨hi,hj⟩ | ⟨hj,hi⟩ <;> subst i <;> subst j
    · rfl
    · exact sy _ _
  rw [entry hs,entry ht]
  exact row_orth b i j k hjk

theorem reduced_inner {n : ℕ} (v w : Space n) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → v k=0 ∨ w k=0) :
    inner ℂ v w = w i*conj (v i) + w j*conj (v j) := by
  classical
  rw [PiLp.inner_apply]
  change ∑ k, w k * conj (v k) = _
  have term (k : Fin n) : w k * conj (v k) =
      (if k=i then w i*conj (v i) else 0) + (if k=j then w j*conj (v j) else 0) := by
    by_cases hi : k=i
    · subst k
      simp [hij]
    by_cases hj : k=j
    · subst k
      simp [hi]
    rcases h k hi hj with h | h <;> simp [hi,hj,h]
  calc
    _ = ∑ k : Fin n, ((if k=i then w i*conj (v i) else 0) +
        (if k=j then w j*conj (v j) else 0)) := Finset.sum_congr rfl (fun k _ => term k)
    _ = _ := by simp [Finset.sum_add_distrib]

def projectPair {n : ℕ} (v : Space n) (i j : Fin n) : Space 2 :=
  WithLp.toLp 2 ![v i,v j]

theorem projectPair_inner {n : ℕ} (v w : Space n) (i j : Fin n) :
    inner ℂ (projectPair v i j) (projectPair w i j) =
    w i*conj (v i) + w j*conj (v j) := by
  rw [PiLp.inner_apply,Fin.sum_univ_two]
  rfl

theorem triangle_pair {c : ℕ} (b : BasedSquare 5 c) (sy : ∀ i j, b.entry i j = b.entry j i)
    (l : Fin 4) (s t : Fin 3) (hst : s ≠ t) :
    inner ℂ (projectPair (edgeVec b (triangle l s)) 0 l.succ)
      (projectPair (edgeVec b (triangle l t)) 0 l.succ) = 0 := by
  have cut : ∀ l s t, s ≠ t → ∀ k : Fin 5, k ≠ 0 → k ≠ l.succ →
      (k=edgeL (triangle l s) ∨ k=edgeR (triangle l s)) ∨
      (k=edgeL (triangle l t) ∨ k=edgeR (triangle l t)) := by decide +kernel
  rw [projectPair_inner,← reduced_inner _ _ 0 l.succ (Fin.succ_ne_zero l).symm]
  · exact edgeVec_orth b sy l s t hst
  · intro k hk hl
    exact (cut l s t hst k hk hl).imp (edgeVec_zero b sy _ k) (edgeVec_zero b sy _ k)

theorem triangle_has_zero {c : ℕ} (b : BasedSquare 5 c) (sy : ∀ i j, b.entry i j = b.entry j i)
    (l : Fin 4) : ∃ s, edgeVec b (triangle l s) 0=0 ∧ edgeVec b (triangle l s) l.succ=0 := by
  let p (s : Fin 3) := projectPair (edgeVec b (triangle l s)) 0 l.succ
  have hz : ∃ s, p s=0 := by
    by_contra! h
    have ind : LinearIndependent ℂ p :=
      linearIndependent_of_ne_zero_of_inner_eq_zero h (fun s t hst => triangle_pair b sy l s t hst)
    have dim := ind.fintype_card_le_finrank
    norm_num [p] at dim
  obtain ⟨s,hs⟩ := hz
  exact ⟨s,congrArg (fun v : Space 2 => v 0) hs,congrArg (fun v : Space 2 => v 1) hs⟩

theorem triangle_support_pair {c : ℕ} (b : BasedSquare 5 c)
    (sy : ∀ i j, b.entry i j = b.entry j i) (l : Fin 4) (s t : Fin 3) (hst : s≠t) :
    (edgeVec b (triangle l s) 0 ≠ 0 ∧ edgeVec b (triangle l t) 0 ≠ 0) ↔
    (edgeVec b (triangle l s) l.succ ≠ 0 ∧ edgeVec b (triangle l t) l.succ ≠ 0) := by
  have h := triangle_pair b sy l s t hst
  rw [projectPair_inner] at h
  have he := eq_neg_of_add_eq_zero_left h
  have hn := not_congr ((congrArg (fun z : ℂ => z=0) he).to_iff)
  simpa [mul_eq_zero,not_or,and_comm] using hn

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem support_classification (a : Fin 6 → Fin 5 → Bool)
    (hN : ∀ e, ∃ k, a e k=true)
    (hL : ∀ e, a e (edgeL e)=false) (hR : ∀ e, a e (edgeR e)=false)
    (hZ : ∀ l, ∃ s, a (triangle l s) 0=false ∧ a (triangle l s) l.succ=false)
    (hP : ∀ l s t, s≠t →
      (a (triangle l s) 0 && a (triangle l t) 0) =
      (a (triangle l s) l.succ && a (triangle l t) l.succ)) :
    ∀ e i j, i≠j → a e i=true → a e j=false := by
  let a' : Fin 6 → Fin 5 → Bool := ![![a 0 0,a 0 1,a 0 2,a 0 3,a 0 4],
  ![a 1 0,a 1 1,a 1 2,a 1 3,a 1 4],
  ![a 2 0,a 2 1,a 2 2,a 2 3,a 2 4],
  ![a 3 0,a 3 1,a 3 2,a 3 3,a 3 4],
  ![a 4 0,a 4 1,a 4 2,a 4 3,a 4 4],
  ![a 5 0,a 5 1,a 5 2,a 5 3,a 5 4]]
  have ha : a = a' := by funext e i; fin_cases e <;> fin_cases i <;> rfl
  rw [ha] at hN hL hR hZ hP ⊢
  simp [Fin.forall_fin_succ,Fin.exists_fin_succ,edgeL,edgeR,triangle,a'] at hN hL hR hZ hP ⊢
  grind (splits := 100)

theorem five_edges_coordinate {c : ℕ} (b : BasedSquare 5 c)
    (sy : ∀ i j, b.entry i j = b.entry j i) (e : Fin 6) :
    Projectivization.mk ℂ (edgeVec b e) (b.nz _ _) ∈ coordinateRays 5 := by
  classical
  let a (e : Fin 6) (k : Fin 5) := decide (edgeVec b e k ≠ 0)
  have hn (e) : ∃ k, a e k=true := by
    by_contra! h
    apply b.nz (edgeL e) (edgeR e)
    ext k
    by_contra hn
    have ht : a e k=true := decide_eq_true hn
    have hf : a e k=false := by simpa using h k
    exact Bool.false_ne_true (hf.symm.trans ht)
  have hl (e) : a e (edgeL e)=false := by simp [a,edgeVec_zero b sy e _ (Or.inl rfl)]
  have hr (e) : a e (edgeR e)=false := by simp [a,edgeVec_zero b sy e _ (Or.inr rfl)]
  have hz (l) : ∃ s, a (triangle l s) 0=false ∧ a (triangle l s) l.succ=false := by
    simpa [a] using triangle_has_zero b sy l
  have hp (l s t) (h : s≠t) : (a (triangle l s) 0 && a (triangle l t) 0) =
      (a (triangle l s) l.succ && a (triangle l t) l.succ) := by
    apply Bool.eq_iff_iff.mpr
    simpa [a] using triangle_support_pair b sy l s t h
  by_contra h
  obtain ⟨i,j,hij,hi,hj⟩ := two_coordinates _ _ h
  have z := support_classification a hn hl hr hz hp e i j hij (by simpa [a] using hi)
  simp [a,hj] at z

def cellRay {n c : ℕ} [NeZero n] (b : BasedSquare n c) (i j : Fin n) :
    Projectivization ℂ (Space n) := Projectivization.mk ℂ (b.entry i j) (b.nz i j)

theorem cellRay_of_eq {n c : ℕ} [NeZero n] (b : BasedSquare n c) {i j k l : Fin n}
    (h : b.entry i j=b.entry k l) : cellRay b i j=cellRay b k l := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1,by simp [h]⟩

theorem first_ray {n c : ℕ} [NeZero n] (b : BasedSquare n c) (j : Fin n) :
    cellRay b 0 j=coordinateRay j := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1,by simp [b.first]⟩

theorem five_offdiagonal {c : ℕ} (b : BasedSquare 5 c)
    (sy : ∀ i j, b.entry i j = b.entry j i) (i j : Fin 5) (hij : i ≠ j) :
    cellRay b i j ∈ coordinateRays 5 := by
  by_cases hi : i=0
  · subst i
    exact ⟨j,(first_ray b j).symm⟩
  by_cases hj : j=0
  · subst j
    exact ⟨i,(first_ray b i).symm.trans (cellRay_of_eq b (sy 0 i))⟩
  have allE : ∀ i j : Fin 5, i≠j → i≠0 → j≠0 → ∃ e : Fin 6,
      (edgeL e=i ∧ edgeR e=j) ∨ (edgeL e=j ∧ edgeR e=i) := by decide +kernel
  obtain ⟨e,⟨h1,h2⟩|⟨h2,h1⟩⟩ := allE i j hij hi hj
  · subst i; subst j
    exact five_edges_coordinate b sy e
  · subst i; subst j
    rw [cellRay_of_eq b (sy _ _)]
    exact five_edges_coordinate b sy e

theorem remaining_axis {n c : ℕ} [NeZero n] (b : BasedSquare n c) (i x : Fin n)
    (hs : ∀ j, j≠x → cellRay b i j ∈ coordinateRays n) :
    cellRay b i x ∈ coordinateRays n := by
  classical
  let J := {j : Fin n // j ≠ x}
  have hcoord (j : J) : ∃ k, coordinateRay k=cellRay b i j.1 := hs j.1 j.2
  choose f hf using hcoord
  have hns : ¬ Function.Surjective f := by
    intro h
    have hc := Fintype.card_le_of_surjective f h
    have hj : Fintype.card J = n-1 := by
      change Fintype.card {j : Fin n // ¬j=x} = _
      rw [Fintype.card_subtype_compl]
      simp
    have hn : n≠0 := NeZero.ne n
    simp only [Fintype.card_fin,hj] at hc
    omega
  change ¬ ∀ k, ∃ j, f j=k at hns
  push Not at hns
  obtain ⟨k,hk⟩ := hns
  obtain ⟨B,hB⟩ := b.rows i
  let u : Space n := EuclideanSpace.single k 1
  have hor (j : Fin n) (hj : j≠x) : inner ℂ (B j) u=0 := by
    let jj : J := ⟨j,hj⟩
    obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp (hf jj).symm
    have hkj : f jj ≠ k := hk jj
    rw [congrFun hB j,← ht,inner_smul_left,EuclideanSpace.inner_single_left]
    simp [u,hkj]
  refine ⟨k,(Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨inner ℂ (B x) u,?_⟩⟩
  rw [← congrFun hB x]
  calc
    _ = ∑ j, inner ℂ (B j) u • B j := by
      symm
      apply Finset.sum_eq_single x
      · intro j _ hj
        simp [hor j hj]
      · simp
    _ = _ := B.sum_repr' u

theorem five_only {c : ℕ} (h : Has 5 c) : c=5 := by
  obtain ⟨b,sy⟩ := h
  have eq : b.rays=coordinateRays 5 := by
    apply Set.Subset.antisymm _ b.coordinate_subset
    rintro _ ⟨⟨i,j⟩,rfl⟩
    by_cases hij : j=i
    · subst j
      exact remaining_axis b i i (fun k hk => five_offdiagonal b sy _ _ hk.symm)
    · exact five_offdiagonal b sy _ _ (Ne.symm hij)
  rw [← b.ncard_rays,eq,ncard_coordinateRays]

#print axioms five_only

end SymmetricSmall
