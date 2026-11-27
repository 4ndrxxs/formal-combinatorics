module
public import Quantum.FractionalBellPositive

/-! A local polygon inequality is necessary for a shared basis measurement.
It is violated by mixing two deterministic grids whose symbols differ by
one three-cycle. An arbitrarily small mixture with the positive uniform
classical table preserves the strict violation. -/
@[expose] public section
noncomputable section
namespace FractionalBlockBell
open QuantumSudoku FractionalPolygons.Sudoku FractionalLayouts Complex Finset Equiv Filter
open scoped BigOperators ComplexConjugate Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

def overlap (p : BigProb I) (r c d k : Index I) : ℝ :=
  Real.sqrt (p (r,c) k)*Real.sqrt (p (r,d) k)

def defect (p : BigProb I) (r c d j : Index I) : ℝ :=
  2*overlap p r c d j-∑ k,overlap p r c d k

theorem measured_defect {p : BigProb I} (h : Measured p) (r c d j : Index I) (different : c≠d) :
    defect p r c d j≤0 := by
  obtain ⟨v,B,hv,born⟩ := h
  let z (k : Index I) := B.repr (v r d) k*conj (B.repr (v r c) k)
  obtain ⟨R,hr⟩ := hv.row r
  have ort : inner ℂ (B.repr (v r c)) (B.repr (v r d))=0 := by
    rw [B.repr.inner_map_map,←congrFun hr c,←congrFun hr d,R.inner_eq_ite,ite_eq_right different]
  have sz : ∑ k,z k=0 := by
    rw [PiLp.inner_apply] at ort
    exact ort
  have modz (k : Index I) : ‖z k‖=overlap p r c d k := by
    simp only [overlap,←born (r,c) k,←born (r,d) k,Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _),z,norm_mul,Complex.norm_conj,mul_comm]
  have zz := (Finset.sum_erase_add _ _ (mem_univ j)).trans sz
  have eq : z j= -(∑ a ∈ univ.erase j,z a) := eq_neg_of_add_eq_zero_right zz
  have bound : overlap p r c d j≤∑ k ∈ univ.erase j,overlap p r c d k := by
    calc
      _=‖z j‖ := (modz j).symm
      _=‖∑ a ∈ univ.erase j,z a‖ := by rw [eq,norm_neg]
      _≤∑ a ∈ univ.erase j,‖z a‖ := norm_sum_le _ _
      _=_ := by simp only [modz]
  unfold defect
  rw [←Finset.sum_erase_add _ _ (mem_univ j)]
  linarith

omit [DecidableEq I] in
theorem continuous_defect (r c d k : Index I) : Continuous (fun p : BigProb I => defect p r c d k) := by
  unfold defect overlap
  fun_prop

def atomic (f : Site I → Index I) : BigProb I := fun q k => if f q=k then 1 else 0

def ordinary [AddCommGroup I] (q : Site I) : Index I := (q.1.2+q.2.1,q.2.2+q.1.1)

omit [Fintype I] [DecidableEq I] in
theorem ordinary_full [AddCommGroup I] (d : Direction) (k : Index I) :
    Function.Bijective (fun j => ordinary (arrange d (k,j))) := by
  rcases k with ⟨s,t⟩
  cases d
  · exact Prod.map_bijective.mpr ⟨(Equiv.addLeft t).bijective,(Equiv.addRight s).bijective⟩
  · exact (Prod.map_bijective.mpr ⟨(Equiv.addRight s).bijective,(Equiv.addLeft t).bijective⟩).comp
      (Equiv.prodComm I I).bijective
  · exact Prod.map_bijective.mpr ⟨(Equiv.addRight t).bijective,(Equiv.addRight s).bijective⟩

omit [Fintype I] in
theorem classical_ordinary [AddCommGroup I] (σ : Perm (Index I)) :
    Classical (atomic (fun q => σ (ordinary q))) :=
  ⟨_,fun d k => σ.injective.comp (ordinary_full d k).injective,fun _ _ => rfl⟩

theorem uniform_in_hull [AddCommGroup I] :
    (fun (_ : Site I) (_ : Index I) => (Fintype.card (Index I):ℝ)⁻¹)∈convexHull ℝ {p | Classical p} := by
  let n : ℝ := Fintype.card (Index I)
  have hn : n≠0 := by dsimp [n]; exact_mod_cast Fintype.card_ne_zero
  have grid (s : Index I) :=
    subset_convexHull ℝ {p : BigProb I | Classical p} (classical_ordinary (Equiv.addRight s))
  have mix := (convex_convexHull ℝ {p : BigProb I | Classical p}).sum_mem
    (t:=univ) (w:=fun _ : Index I => n⁻¹) (z:=fun s => atomic (fun q => ordinary q+s))
    (fun _ _ => by dsimp [n]; positivity) (by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_inv_cancel₀ hn) (fun s _ => grid s)
  have he : (∑ s : Index I, n⁻¹ • atomic (fun q => ordinary q+s))=
      (fun (_ : Site I) (_ : Index I) => (Fintype.card (Index I):ℝ)⁻¹) := by
    funext q k
    have rel (s : Index I) : ordinary q+s=k ↔ s=k-ordinary q := by constructor <;> intro h <;> abel_nf at * <;> grind
    simp [atomic,Finset.sum_apply,rel,mul_ite,n]
  rwa [he] at mix

private theorem three_seed [AddCommGroup I] (a b c : Index I) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ∃ (p : BigProb I) (r u v : Index I), p∈convexHull ℝ {p | Classical p} ∧
      u≠v ∧ 0<defect p r u v b := by
  let σ := (Equiv.swap a c).trans (Equiv.swap a b)
  have sb : σ b=a := by simp [σ,swap_apply_of_ne_of_ne (Ne.symm ab) bc]
  let p : BigProb I := (1/2:ℝ) • atomic ordinary+(1/2:ℝ) • atomic (fun q => σ (ordinary q))
  have hull : p∈convexHull ℝ {p | Classical p} :=
    convex_convexHull ℝ _ (subset_convexHull ℝ _ (classical_ordinary (Equiv.refl _)))
      (subset_convexHull ℝ _ (classical_ordinary σ)) (by norm_num) (by norm_num) (by norm_num)
  let r : Index I := 0
  obtain ⟨u,hu⟩ := (ordinary_full .row r).surjective b
  obtain ⟨v,hv⟩ := (ordinary_full .row r).surjective c
  change ordinary (r,u)=b at hu
  change ordinary (r,v)=c at hv
  have sc : σ c=b := by simp [σ]
  have uv : u≠v := by rintro rfl; exact bc (hu.symm.trans hv)
  have up (k : Index I) : p (r,u) k=(if b=k then 1/2 else 0)+(if a=k then 1/2 else 0) := by
    simp [p,atomic,hu,sb,mul_ite]
  have vp (k : Index I) : p (r,v) k=(if c=k then 1/2 else 0)+(if b=k then 1/2 else 0) := by
    simp [p,atomic,hv,sc,mul_ite]
  have side (k : Index I) : overlap p r u v k=if k=b then 1/2 else 0 := by
    by_cases kb : k=b
    · subst k
      have u0 : p (r,u) b=1/2 := by simp [up,ab]
      have v0 : p (r,v) b=1/2 := by simp [vp,Ne.symm bc]
      rw [overlap,u0,v0,Real.mul_self_sqrt (by norm_num),ite_eq_left rfl]
    · by_cases ka : k=a
      · subst k; simp [overlap,up,vp,Ne.symm ac,Ne.symm ab,ab]
      · simp [overlap,up,vp,Ne.symm kb,Ne.symm ka,kb]
  exact ⟨p,r,u,v,hull,uv,by norm_num [defect,side]⟩

omit [Fintype I] in
private theorem hull_nonneg {p : BigProb I} (h : p∈convexHull ℝ {p | Classical p}) (q : Site I) (k : Index I) :
    0≤p q k := by
  have cv : Convex ℝ {z : BigProb I | 0≤z q k} :=
    fun p hp r hr a b ha hb _ => add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hr)
  apply convexHull_min _ cv h
  rintro z ⟨f,_,eq⟩
  change 0≤z q k
  rw [eq]
  split <;> norm_num

/-- Every nontrivial size has strictly positive points of the scalar
classical polytope failing even one row's necessary polygon inequality. -/
theorem positive_classical_unmeasured (N : ℕ) (hN : 2≤N) :
    ∃ p : BigProb (Fin N), p∈convexHull ℝ {z | Classical z} ∧
      (∀ q k,0<p q k) ∧ ¬Measured p := by
  let : NeZero N := ⟨by omega⟩
  let x : Fin N := ⟨0,by omega⟩
  let y : Fin N := ⟨1,by omega⟩
  have xy : x≠y := by intro eq; have := congrArg Fin.val eq; simp [x,y] at this
  let a := (x,x)
  let b := (x,y)
  let c := (y,x)
  obtain ⟨p,r,u,v,hp,uv,hd⟩ := three_seed a b c (by simp [a,b,xy]) (by simp [a,c,xy]) (by simp [b,c,xy])
  let U : BigProb (Fin N) := fun _ _ => (Fintype.card (Index (Fin N)):ℝ)⁻¹
  have posU (q : Site (Fin N)) (k : Index (Fin N)) : 0<U q k := by dsimp [U]; positivity
  let mix (t : ℝ) : BigProb (Fin N) := (1-t) • p+t • U
  have cm : Continuous mix := by unfold mix; fun_prop
  have out : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<defect (mix t) r u v b := by
    have initial : 0<defect (mix 0) r u v b := by simpa [mix] using hd
    exact (continuousAt_const.eventually_lt ((continuous_defect r u v b).comp cm).continuousAt
      initial).filter_mono nhdsWithin_le_nhds
  have small : ∀ᶠ t in 𝓝[>] (0:ℝ), t<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0<t := self_mem_nhdsWithin
  obtain ⟨s,holy,sp,sl⟩ := (out.and (pos.and small)).exists
  refine ⟨mix s,convex_convexHull ℝ _ hp uniform_in_hull (by linarith) sp.le (by ring),?_,?_⟩
  · intro q k
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hull_nonneg hp q k)) (mul_pos sp (posU q k))
  · exact fun h => (not_le_of_gt holy) (measured_defect h r u v b uv)

#print axioms positive_classical_unmeasured
end FractionalBlockBell

