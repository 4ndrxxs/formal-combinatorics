import Quantum.Hadamard.ProjectivePaleyAction

/-! Rigidity of a two-row border for Gram matrices with two equal row classes.
A nonzero off-diagonal entry in a Gram class is either +2 or -2. -/

noncomputable section
open Finset Matrix
namespace Hadamard.NearBorder

abbrev Index (m : ℕ) := (Bool × Fin m) ⊕ Bool
abbrev bulk {m : ℕ} (b : Bool) (i : Fin m) : Index m := Sum.inl (b,i)
abbrev rim {m : ℕ} (j : Bool) : Index m := Sum.inr j

/-- The Gram condition in near-Hadamard order 2(m+1), without specifying
which rows belong to the two classes. -/
structure Partition {m : ℕ} (G : Matrix (Index m) (Index m) ℝ) where
  part : Index m→Bool
  count : ∀ b, (∑ i, if part i=b then (1:ℕ) else 0)=m+1
  inside : ∀ i j, i≠j → part i=part j → G i j=2 ∨ G i j= -2
  outside : ∀ i j, part i≠part j → G i j=0

private def boolEquiv (f : Bool→Bool) (h : f false≠f true) : Bool ≃ Bool :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.mp (by
    intro a b eq; cases a <;> cases b <;> simp_all))

/-- Each nonzero bulk clique occupies one class. Counting the two missing
rows forces one border row into each class, even when the original row
labels and the order of the border are unknown. -/
theorem recover_partition {m : ℕ} (hm : 2 ≤ m) {G : Matrix (Index m) (Index m) ℝ}
    (p : Partition G) (nz : ∀ a (i j : Fin m), i≠j → G (bulk a i) (bulk a j)≠0) :
    ∃ (u v : Bool ≃ Bool), (∀ a i, p.part (bulk a i)=u a) ∧ ∀ b, p.part (rim b)=v b := by
  let first : Fin m := ⟨0,by omega⟩
  let u (a : Bool) := p.part (bulk a first)
  let v (b : Bool) := p.part (rim b)
  have same (a i) : p.part (bulk a i)=u a := by
    by_contra h
    have ne : i≠first := by intro eq; subst i; exact h rfl
    exact nz a i first ne (p.outside _ _ h)
  have rimPart (j) : p.part (rim j)=v j := rfl
  have count := p.count true
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,same,rimPart] at count
  have diff : u false≠u true ∧ v false≠v true := by
    cases h0 : u false <;> cases h1 : u true <;> cases h2 : v false <;> cases h3 : v true <;>
      simp [h0,h1,h2,h3] at count ⊢ <;> omega
  exact ⟨boolEquiv u diff.1,boolEquiv v diff.2,same,rimPart⟩

private theorem align {a b : ℝ} (ha : a=2 ∨ a= -2) (hb : b=2 ∨ b= -2) :
    ∃ s : ℝ, (s=1 ∨ s= -1) ∧ a=s*b := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact ⟨1,Or.inl rfl,by norm_num⟩
  · exact ⟨-1,Or.inr rfl,by norm_num⟩
  · exact ⟨-1,Or.inr rfl,by norm_num⟩
  · exact ⟨1,Or.inl rfl,by norm_num⟩

/-- The Gram matrix is fixed, up to reordering and changing signs of the two
border rows, by its two diagonal bulk blocks and its diagonal norm. -/
theorem gram_border_congr {m : ℕ} (hm : 2 ≤ m) {G H : Matrix (Index m) (Index m) ℝ}
    (pg : Partition G) (ph : Partition H) (sg : G.IsSymm) (sh : H.IsSymm)
    (nz : ∀ a (i j : Fin m), i≠j → G (bulk a i) (bulk a j)≠0)
    (blocks : ∀ a i j, G (bulk a i) (bulk a j)=H (bulk a i) (bulk a j))
    (rowG : ∀ a i j b, G (bulk a i) (rim b)=G (bulk a j) (rim b))
    (rowH : ∀ a i j b, H (bulk a i) (rim b)=H (bulk a j) (rim b))
    (norm : ∀ b t, G (rim b) (rim b)=H (rim t) (rim t)) :
    ∃ (e : Index m ≃ Index m) (s : Index m→ℝ), (∀ i, |s i|=1) ∧
      G=diagonal s*(H.submatrix e e)*diagonal s := by
  obtain ⟨u,v,ug,vg⟩ := recover_partition hm pg nz
  obtain ⟨x,y,uh,vh⟩ := recover_partition hm ph (fun a i j h ↦ by rw [←blocks]; exact nz a i j h)
  let first : Fin m := ⟨0,by omega⟩
  let home (t : Bool) := u.symm (v t)
  let e := v.trans (u.symm.trans (x.trans y.symm))
  have gu (t : Bool) : u (home t)=v t := u.apply_symm_apply _
  have hu (t : Bool) : x (home t)=y (e t) := by simp [e,home]
  have pairG (t) := pg.inside (bulk (home t) first) (rim t) (by simp [bulk,rim]) (by rw [ug,vg,gu])
  have pairH (t) := ph.inside (bulk (home t) first) (rim (e t)) (by simp [bulk,rim]) (by rw [uh,vh,hu])
  choose s hs matchAt using fun t ↦ align (pairG t) (pairH t)
  have border (a : Bool) (i : Fin m) (t : Bool) : G (bulk a i) (rim t)=s t*H (bulk a i) (rim (e t)) := by
    by_cases eq : a=home t
    · subst a; rw [rowG _ i first, rowH _ i first,matchAt t]
    · have h1 : pg.part (bulk a i)≠pg.part (rim t) := by rw [ug,vg,←gu]; exact u.injective.ne eq
      have h2 : ph.part (bulk a i)≠ph.part (rim (e t)) := by rw [uh,vh,←hu]; exact x.injective.ne eq
      rw [pg.outside _ _ h1,ph.outside _ _ h2,mul_zero]
  let E := (Equiv.refl (Bool × Fin m)).sumCongr e
  let S : Index m→ℝ := Sum.elim (fun _ ↦ 1) s
  refine ⟨E,S,?_,?_⟩
  · rintro (a|t)
    · norm_num [S]
    · rcases hs t with h|h <;> simp [S,h]
  · ext i j
    simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.submatrix_apply]
    rcases i with ⟨a,i⟩|t <;> rcases j with ⟨b,j⟩|w
    · change G (bulk a i) (bulk b j)=1*H (bulk a i) (bulk b j)*1
      rw [one_mul,mul_one]
      by_cases eq : a=b
      · subst b; apply blocks
      · have h1 : pg.part (bulk a i)≠pg.part (bulk b j) := by rw [ug,ug]; exact u.injective.ne eq
        have h2 : ph.part (bulk a i)≠ph.part (bulk b j) := by rw [uh,uh]; exact x.injective.ne eq
        rw [pg.outside _ _ h1,ph.outside _ _ h2]
    · change G (bulk a i) (rim w)=1*H (bulk a i) (rim (e w))*s w
      rw [border,one_mul,mul_comm]
    · change G (rim t) (bulk b j)=s t*H (rim (e t)) (bulk b j)*1
      rw [←sg.apply (rim t) (bulk b j),←sh.apply (rim (e t)) (bulk b j),border,mul_one]
    · change G (rim t) (rim w)=s t*H (rim (e t)) (rim (e w))*s w
      by_cases eq : t=w
      · subst w; rw [norm t (e t)]
        rcases hs t with h|h <;> rw [h] <;> ring
      · have h1 : pg.part (rim t)≠pg.part (rim w) := by rw [vg,vg]; exact v.injective.ne eq
        have h2 : ph.part (rim (e t))≠ph.part (rim (e w)) := by rw [vh,vh]; exact y.injective.ne (e.injective.ne eq)
        rw [pg.outside _ _ h1,ph.outside _ _ h2,mul_zero,zero_mul]

theorem abs_det_of_border_blocks {m : ℕ} (hm : 2 ≤ m) (M N : Matrix (Index m) (Index m) ℝ)
    (pm : Partition (M*M.transpose)) (pn : Partition (N*N.transpose))
    (nz : ∀ a (i j : Fin m), i≠j → (M*M.transpose) (bulk a i) (bulk a j)≠0)
    (blocks : ∀ a i j, (M*M.transpose) (bulk a i) (bulk a j)=(N*N.transpose) (bulk a i) (bulk a j))
    (rowM : ∀ a i j b, (M*M.transpose) (bulk a i) (rim b)=(M*M.transpose) (bulk a j) (rim b))
    (rowN : ∀ a i j b, (N*N.transpose) (bulk a i) (rim b)=(N*N.transpose) (bulk a j) (rim b))
    (norm : ∀ b t, (M*M.transpose) (rim b) (rim b)=(N*N.transpose) (rim t) (rim t)) :
    |M.det|=|N.det| := by
  have sym (A : Matrix (Index m) (Index m) ℝ) : (A*A.transpose).IsSymm := by
    change (A*A.transpose).transpose=A*A.transpose
    rw [transpose_mul,transpose_transpose]
  obtain ⟨e,s,hs,eq⟩ := gram_border_congr hm pm pn (sym M) (sym N) nz blocks rowM rowN norm
  have d := Hadamard.ProjectiveSigning.abs_det_signed ((N*N.transpose).submatrix e e) s 1 hs (by norm_num)
  rw [one_smul,←eq,det_submatrix_equiv_self,det_mul,det_mul,det_transpose,det_transpose,abs_mul,abs_mul] at d
  nlinarith [abs_nonneg M.det,abs_nonneg N.det]

#print axioms abs_det_of_border_blocks

abbrev Core (m : ℕ) := Bool × Fin m

/-- Each of the four border strips is constant on a bulk class. -/
def bordered {m : ℕ} (A : Matrix (Core m) (Core m) ℝ) (T L H : Matrix Bool Bool ℝ) :
    Matrix (Index m) (Index m) ℝ
  | .inl i,.inl j => A i j
  | .inl i,.inr t => T i.1 t
  | .inr t,.inl j => L t j.1
  | .inr t,.inr u => H t u

def Signs (T : Matrix Bool Bool ℝ) : Prop := ∀i j, (T i j)^2=1

def Regular {m : ℕ} (A : Matrix (Core m) (Core m) ℝ) : Prop :=
  ∀ a b i j, (∑ k, A (a,i) (b,k))=∑ k, A (a,j) (b,k)

private theorem bulk_gram {m : ℕ} (A : Matrix (Core m) (Core m) ℝ) (T L H : Matrix Bool Bool ℝ)
    (ht : Signs T) (a : Bool) (i j : Fin m) :
    let M := bordered A T L H
    (M*M.transpose) (bulk a i) (bulk a j)=(A*A.transpose) (a,i) (a,j)+2 := by
  dsimp only
  rw [Matrix.mul_apply,Matrix.mul_apply]
  simp only [Matrix.transpose_apply,Fintype.sum_sum_type,bulk,bordered,Fintype.sum_bool]
  rw [←sq,←sq,ht,ht]; ring

private theorem mixed_gram {m : ℕ} (A : Matrix (Core m) (Core m) ℝ) (T L H : Matrix Bool Bool ℝ)
    (reg : Regular A) (a : Bool) (i j : Fin m) (b : Bool) :
    let M := bordered A T L H
    (M*M.transpose) (bulk a i) (rim b)=(M*M.transpose) (bulk a j) (rim b) := by
  dsimp only
  rw [Matrix.mul_apply,Matrix.mul_apply]
  simp only [Matrix.transpose_apply,Fintype.sum_sum_type,bulk,rim,bordered,add_left_inj]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro u _
  simp only [←sum_mul,reg a u i j]

private theorem rim_norm {m : ℕ} (A : Matrix (Core m) (Core m) ℝ) (T L H : Matrix Bool Bool ℝ)
    (hl : Signs L) (hh : Signs H) (b : Bool) :
    let M := bordered A T L H
    (M*M.transpose) (rim b) (rim b)=Fintype.card (Core m)+2 := by
  dsimp only
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply,Fintype.sum_sum_type,rim,bordered]
  unfold Signs at hl hh
  simp [←sq,hl,hh]

/-- Any two near-Hadamard borderings by class-constant sign strips have the
same absolute determinant if their regular cores agree in the two diagonal
Gram blocks. No permutation or choice of boundary signs is prescribed. -/
theorem bordering_rigidity {m : ℕ} (hm : 2 ≤ m) (A B : Matrix (Core m) (Core m) ℝ)
    (T L H U V J : Matrix Bool Bool ℝ) (ht : Signs T) (hl : Signs L) (hh : Signs H)
    (hu : Signs U) (hv : Signs V) (hj : Signs J) (ra : Regular A) (rb : Regular B)
    (blocks : ∀ a i j, (A*A.transpose) (a,i) (a,j)=(B*B.transpose) (a,i) (a,j))
    (nz : ∀ a (i j : Fin m), i≠j → (A*A.transpose) (a,i) (a,j)+2≠0)
    (p : Partition (bordered A T L H*(bordered A T L H).transpose))
    (q : Partition (bordered B U V J*(bordered B U V J).transpose)) :
    |(bordered A T L H).det|=|(bordered B U V J).det| := by
  apply abs_det_of_border_blocks hm _ _ p q
  · intro a i j ne
    rw [bulk_gram A T L H ht]; exact nz a i j ne
  · intro a i j
    rw [bulk_gram A T L H ht,bulk_gram B U V J hu,blocks]
  · exact mixed_gram A T L H ra
  · exact mixed_gram B U V J rb
  · intro b t
    rw [rim_norm A T L H hl hh,rim_norm B U V J hv hj]

#print axioms bordering_rigidity


section Circulants

variable {m : ℕ} [NeZero m]

/-- A cyclic shift or a reversal followed by a shift, with a global sign. -/
structure SequenceChange (m : ℕ) where
  offset : Fin m
  reversed : Bool
  scale : ℝ
  unit : scale^2=1

def SequenceChange.apply (c : SequenceChange m) (f : Fin m → ℝ) (k : Fin m) : ℝ :=
  c.scale * f (if c.reversed then c.offset-k else c.offset+k)

def correlation (f : Fin m → ℝ) (i j : Fin m) : ℝ := ∑ k, f (k-i)*f (k-j)

theorem unchanged_correlation (c : SequenceChange m) (f : Fin m → ℝ) (i j : Fin m) :
    correlation (c.apply f) i j = correlation f i j := by
  have unit (a b : ℝ) : c.scale*a*(c.scale*b)=a*b := by
    calc
      _ = c.scale^2*(a*b) := by ring
      _ = _ := by rw [c.unit,one_mul]
  cases h : c.reversed
  · have eq := Equiv.sum_comp (Equiv.addLeft c.offset) (fun k : Fin m ↦ f (k-i)*f (k-j))
    change (∑ k,f (c.offset+k-i)*f (c.offset+k-j))=_ at eq
    simpa only [correlation,SequenceChange.apply,h,Bool.false_eq_true,ite_false,unit,add_sub_assoc] using eq
  · have eq := (Equiv.subLeft (c.offset+i+j)).sum_comp (fun k : Fin m ↦ f (k-i)*f (k-j))
    change (∑ k,f (c.offset+i+j-k-i)*f (c.offset+i+j-k-j))=_ at eq
    have e1 (k : Fin m) : c.offset+i+j-k-i=c.offset-(k-j) := by abel
    have e2 (k : Fin m) : c.offset+i+j-k-j=c.offset-(k-i) := by abel
    unfold correlation SequenceChange.apply
    simp only [h,ite_true,unit]
    simpa only [e1,e2,mul_comm] using eq

/-- Each block row uses both sequences, in either order. The four block
sequences can independently be shifted, reversed, and multiplied by a sign. -/
structure CyclicLayout (m : ℕ) where
  order : Bool → Bool ≃ Bool
  change : Bool → Bool → SequenceChange m

def CyclicLayout.core (u : CyclicLayout m) (f : Bool → Fin m → ℝ) :
    Matrix (Core m) (Core m) ℝ :=
  fun i j ↦ (u.change i.1 j.1).apply (f (u.order i.1 j.1)) (j.2-i.2)

theorem CyclicLayout.regular (u : CyclicLayout m) (f : Bool → Fin m → ℝ) :
    Regular (u.core f) := by
  intro a b i j
  let g := (u.change a b).apply (f (u.order a b))
  exact ((Equiv.subRight i).sum_comp g).trans ((Equiv.subRight j).sum_comp g).symm

theorem CyclicLayout.gram (u : CyclicLayout m) (f : Bool → Fin m → ℝ) (a : Bool) (i j : Fin m) :
    (u.core f*(u.core f).transpose) (a,i) (a,j)=∑ b,correlation (f b) i j := by
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  change (∑ b,correlation ((u.change a b).apply (f (u.order a b))) i j)=_
  simp_rw [unchanged_correlation]
  exact (u.order a).sum_comp (fun b ↦ correlation (f b) i j)

/-- Two circulant cores may use different pairs of sequences. Only the sums
of their periodic autocorrelations must agree. -/
theorem two_circulant_borders (hm : 2 ≤ m)
    (u v : CyclicLayout m) (f g : Bool → Fin m → ℝ)
    (T L H U V J : Matrix Bool Bool ℝ) (ht : Signs T) (hl : Signs L) (hh : Signs H)
    (hu : Signs U) (hv : Signs V) (hj : Signs J)
    (eq : ∀ i j, (∑ b,correlation (f b) i j)=∑ b,correlation (g b) i j)
    (nz : ∀ (i j : Fin m), i≠j → (∑ b,correlation (f b) i j)+2≠0)
    (p : Partition (bordered (u.core f) T L H*(bordered (u.core f) T L H).transpose))
    (q : Partition (bordered (v.core g) U V J*(bordered (v.core g) U V J).transpose)) :
    |(bordered (u.core f) T L H).det|=|(bordered (v.core g) U V J).det| := by
  apply bordering_rigidity hm _ _ T L H U V J ht hl hh hu hv hj (u.regular f) (v.regular g)
  · intro a i j; rw [u.gram,v.gram,eq]
  · intro a i j h; rw [u.gram]; exact nz i j h
  · exact p
  · exact q

#print axioms two_circulant_borders

end Circulants

end Hadamard.NearBorder
