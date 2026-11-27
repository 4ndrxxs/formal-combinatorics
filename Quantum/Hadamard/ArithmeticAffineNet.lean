import Quantum.Hadamard.Basic

/-! Parallel lines over a finite commutative ring form an affine net
whenever every difference between the selected slopes is a unit. -/
noncomputable section
namespace Hadamard.AffineNet
open Finset HadamardMod
variable {m : ℕ} {R S : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
abbrev Point (R : Type*) := R×R
private def line (m : ℕ) (a:R) (i j:Point R) : ZMod m :=
  if j.2 = i.2+a*(j.1-i.1) then 1 else 0
private def bundle (m:ℕ) (f:S→R) (i j:Point R) : ZMod m := ∑ s, line m (f s) i j

private theorem solve (u:Rˣ) (x y:R) : (u:R)*x=y ↔ x=(u⁻¹:Rˣ)*y := by
  constructor <;> intro h
  · rw [← h,←mul_assoc]; simp
  · rw [h,←mul_assoc]; simp

private theorem line_sym (s:R) (i j:Point R) : line m s i j=line m s j i := by
  have eq : j.2=i.2+s*(j.1-i.1) ↔ i.2=j.2+s*(i.1-j.1) := by constructor <;> intro h <;> linear_combination -h
  simp only [line,eq]

private theorem along (a:R) (i:Point R) (g:Point R → ZMod m) :
    (∑ j,line m a i j*g j)=∑ x:R, g (x,i.2+a*(x-i.1)) := by
  rw [Fintype.sum_prod_type]
  simp only [line,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true]

private theorem by_pair (f:S→R) (diff:∀ s t,s≠t→IsUnit (f s-f t)) (s t:S) (i k:Point R) :
    (∑ j,line m (f s) i j*line m (f t) k j)=
      if s=t then (Fintype.card R:ZMod m)*line m (f s) i k else 1 := by
  rw [along]
  by_cases eq:s=t
  · subst t
    have cond (x:R) : i.2+f s*(x-i.1)=k.2+f s*(x-k.1) ↔ k.2=i.2+f s*(k.1-i.1) := by
      constructor <;> intro h <;> linear_combination -h
    simp [line,cond]
  · obtain ⟨u,hu⟩ := diff s t eq
    have cond (x:R) : i.2+f s*(x-i.1)=k.2+f t*(x-k.1) ↔
        x=(u⁻¹:Rˣ)*(k.2-i.2+f s*i.1-f t*k.1) := by
      rw [← solve,hu]
      constructor <;> intro h <;> linear_combination h
    simp [line,cond,eq]

private theorem bundle_dot (f:S→R) (diff:∀ s t,s≠t→IsUnit (f s-f t)) (i k:Point R) :
    (∑ j, bundle m f i j*bundle m f k j) =
      (Fintype.card R:ZMod m)*bundle m f i k+(Fintype.card S:ZMod m)*((Fintype.card S:ZMod m)-1) := by
  unfold bundle
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  have inner (s:S) : (∑ j,∑ t:S,line m (f t) i j*line m (f s) k j)=
      (Fintype.card R:ZMod m)*line m (f s) i k+((Fintype.card S:ZMod m)-1) := by
    rw [sum_comm]
    simp only [by_pair f diff]
    have eq (t:S) : (if t=s then (Fintype.card R:ZMod m)*line m (f t) i k else 1)=
        (if t=s then (Fintype.card R:ZMod m)*line m (f s) i k-1 else 0)+1 := by
      by_cases h:t=s <;> simp [h]
    simp [eq,sum_add_distrib]; ring
  simp only [inner,sum_add_distrib]
  simp
  ring

private def entry (m:ℕ) (f:S→R) (i j:Point R) : ZMod m :=
  1-2*bundle m f i j+(if i=j then 2*(Fintype.card S:ZMod m) else 0)

private theorem entry_sign (f:S→R) (diff:∀ s t,s≠t→IsUnit (f s-f t)) (i j:Point R) :
    Sign (entry m f i j) := by
  by_cases same : i=j
  · subst j; simp [entry,bundle,line,Sign]
  let ok (s:S) := j.2=i.2+f s*(j.1-i.1)
  have unique (s t:S) (hs:ok s) (ht:ok t) : s=t := by
    by_contra ne
    obtain ⟨u,hu⟩ := diff s t ne
    have h : (u:R)*(j.1-i.1)=0 := by rw [hu]; dsimp [ok] at hs ht; linear_combination ht-hs
    have hx := (solve u _ _).mp h
    rw [mul_zero,sub_eq_zero] at hx
    have hy : j.2=i.2 := by simpa [ok,hx] using hs
    exact same (Prod.ext hx.symm hy.symm)
  by_cases any : ∃ s,ok s
  · obtain ⟨s,hs⟩ := any
    have cond (t:S) : ok t ↔ t=s := ⟨fun ht => unique t s ht hs, fun h => h ▸ hs⟩
    have mass : bundle m f i j=1 := by
      change (∑ t:S,if ok t then (1:ZMod m) else 0)=1
      simp only [cond,sum_ite_eq',mem_univ,ite_true]
    exact Or.inr (by simp [entry,same,mass]; ring)
  · have no (s:S) : ¬ok s := fun h => any ⟨s,h⟩
    have mass : bundle m f i j=0 := by
      change (∑ t:S,if ok t then (1:ZMod m) else 0)=0
      simp [no]
    exact Or.inl (by simp [entry,same,mass])

theorem at_square {f:S→R} (diff:∀ s t,s≠t→IsUnit (f s-f t))
    (chosen : 2*(Fintype.card S:ZMod m)=(Fintype.card R:ZMod m)) :
    AtOrder m ((Fintype.card R)^2) := by
  have row (i:Point R) : (∑ j,bundle m f i j)=(Fintype.card S:ZMod m)*(Fintype.card R:ZMod m) := by
    unfold bundle
    rw [sum_comm]
    have ls (s:S) : (∑ j,line m (f s) i j)=(Fintype.card R:ZMod m) := by
      simpa using along (f s) i (fun _ => (1:ZMod m))
    simp only [ls,sum_const,card_univ,nsmul_eq_mul]
  have sym (i j:Point R) : bundle m f i j=bundle m f j i := by simp only [bundle,line_sym (i:=i) (j:=j)]
  have good : Good (entry m f) := by
    refine ⟨entry_sign f diff,?_⟩
    intro i k ne
    let a := 2*(Fintype.card S:ZMod m)
    have factor (j:Point R) :
        entry m f i j*entry m f k j=
        (1-2*bundle m f i j-2*bundle m f k j+4*(bundle m f i j*bundle m f k j))+
        (if i=j then a*(1-2*bundle m f k i) else 0)+
        (if k=j then a*(1-2*bundle m f i k) else 0) := by
      by_cases h:i=j <;> by_cases e:k=j
      · exact (ne (h.trans e.symm)).elim
      · subst j; simp [entry,e,a]; ring
      · subst j; simp [entry,h,a]; ring
      · simp [entry,h,e]; ring
    simp only [factor,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_ite_eq,mem_univ,ite_true,
      sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,mul_one,row,bundle_dot f diff]
    rw [sym k i]
    dsimp [a]
    rw [←chosen]
    ring
  exact of_card good (by simp [Point,pow_two])

end Hadamard.AffineNet
