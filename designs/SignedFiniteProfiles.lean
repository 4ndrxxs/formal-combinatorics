import SignedBudgetCertificate
import Mathlib.Data.List.Sort

/-! Enumerating integer multisets by cardinality, sum and squared sum, and restoring every order. -/

namespace Signed39.Profiles

def squareSum (xs : List ℤ) : ℤ := (xs.map (fun a=>a^2)).sum

theorem squareSum_nonnegative (xs : List ℤ) : 0 ≤ squareSum xs := by
  induction xs with
  | nil => simp [squareSum]
  | cons a xs ih => exact add_nonneg (sq_nonneg a) ih

def sortedWords (choices : List ℤ) : ℕ → ℤ → ℤ → ℤ → List (List ℤ)
  | 0,_,S,E => if S=0 ∧ E=0 then [[]] else []
  | n+1,lo,S,E => choices.flatMap (fun a=>if lo≤a ∧ a^2≤E ∧ (n+1:ℕ)*a≤S then
      (sortedWords choices n a (S-a) (E-a^2)).map (a::·) else [])

theorem lower_sum {xs : List ℤ} {a : ℤ} (lo : ∀x∈xs,a≤x) : (xs.length:ℤ)*a≤xs.sum := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
    have top:=lo z (by simp)
    have rest:=ih (fun x h=>lo x (by simp [h]))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons,add_mul,one_mul]
    omega

theorem sortedWords_mem (choices xs : List ℤ) (lo S E : ℤ) (order : xs.Pairwise (·≤·))
    (domain : ∀x∈xs,x∈choices ∧ lo≤x) (sm : xs.sum=S) (sq : squareSum xs=E) :
    xs∈sortedWords choices xs.length lo S E := by
  induction xs generalizing lo S E with
  | nil => simp_all [squareSum,sortedWords]
  | cons a xs ih =>
    obtain ⟨left,sorted⟩ := List.pairwise_cons.mp order
    obtain ⟨allowed,alow⟩ := domain a (by simp)
    change a+xs.sum=S at sm
    change a^2+squareSum xs=E at sq
    have en:=squareSum_nonnegative xs
    have ge:=lower_sum left
    have above : ((xs.length+1:ℕ):ℤ)*a≤S := by push_cast; linarith
    rw [List.length_cons,sortedWords]
    apply List.mem_flatMap.mpr
    refine ⟨a,allowed,?_⟩
    rw [ite_eq_left ⟨alow,by omega,above⟩]
    apply List.mem_map.mpr
    exact ⟨xs,ih _ _ _ sorted (fun x h=>⟨(domain x (by simp [h])).1,left x h⟩) (by omega) (by omega),rfl⟩

def orders : ℕ → List ℤ → List (List ℤ)
  | 0,_ => [[]]
  | n+1,ys => ys.eraseDups.flatMap (fun y=>(orders n (ys.erase y)).map (y::·))

theorem orders_mem (xs ys : List ℤ) (eq : xs.Perm ys) : xs∈orders xs.length ys := by
  induction xs generalizing ys with
  | nil => simp [orders]
  | cons a xs ih =>
    have mem : a∈ys := eq.mem_iff.mp (by simp)
    have perm : xs.Perm (ys.erase a) := by simpa using eq.erase a
    rw [List.length_cons,orders]
    exact List.mem_flatMap.mpr ⟨a,List.mem_eraseDups.mpr mem,List.mem_map.mpr ⟨xs,ih _ perm,rfl⟩⟩

theorem possible {xs choices : List ℤ} {L S E : ℤ} (domain : ∀x∈xs,x∈choices ∧ L≤x)
    (sm : xs.sum=S) (sq : squareSum xs=E) :
    ∃ ys∈sortedWords choices xs.length L S E, xs.Perm ys ∧ xs∈orders xs.length ys := by
  let ys := xs.mergeSort
  have eq : ys.Perm xs := List.mergeSort_perm _ _
  have ord : ys.Pairwise (·≤·) := List.pairwise_mergeSort' (·≤·) xs
  have m := sortedWords_mem choices ys L S E ord (fun a h=>domain a (eq.mem_iff.mp h))
    (eq.sum_eq.trans sm) ((eq.map (fun x=>x^2)).sum_eq.trans sq)
  rw [eq.length_eq] at m
  exact ⟨ys,m,eq.symm,orders_mem _ _ eq.symm⟩

def finalPair (choices : List ℤ) (lo S E : ℤ) : List (List ℤ) :=
  let gap : ℤ := (2*E-S^2).toNat.sqrt
  let a := (S-gap)/2; let b := S-a
  if a∈choices ∧ b∈choices ∧ lo≤a ∧ a≤b ∧ a^2+b^2=E then [[a,b]] else []

theorem finalPair_mem (choices : List ℤ) {a b lo S E : ℤ} (ha : a∈choices) (hb : b∈choices)
    (lower : lo≤a) (order : a≤b) (sm : a+b=S) (sq : a^2+b^2=E) : [a,b]∈finalPair choices lo S E := by
  let d := (b-a).toNat
  have dd : (d:ℤ)=b-a := Int.toNat_of_nonneg (by omega)
  have num : 2*E-S^2=(d:ℤ)^2 := by rw [dd,←sm,←sq]; ring
  have nat : (2*E-S^2).toNat=d^2 := by rw [num,←Nat.cast_pow,Int.toNat_natCast]
  have eq : (S-(d:ℤ))/2=a := by rw [dd]; omega
  have rt : (d^2).sqrt=d := by simp
  simp only [finalPair,nat,rt,eq,show S-a=b by omega]
  simp [ha,hb,lower,order,sq]

def shortWords (choices : List ℤ) : ℕ → ℤ → ℤ → ℤ → List (List ℤ)
  | 0,_,S,E => if S=0 ∧ E=0 then [[]] else []
  | 1,lo,S,E => if S∈choices ∧ lo≤S ∧ S^2=E then [[S]] else []
  | 2,lo,S,E => finalPair choices lo S E
  | n+3,lo,S,E => choices.flatMap (fun a=>if lo≤a ∧ a^2≤E ∧ ((n+3:ℕ):ℤ)*a≤S then
      (shortWords choices (n+2) a (S-a) (E-a^2)).map (a::·) else [])

theorem shortWords_mem (choices xs : List ℤ) (lo S E : ℤ) (order : xs.Pairwise (·≤·))
    (domain : ∀x∈xs,x∈choices ∧ lo≤x) (sm : xs.sum=S) (sq : squareSum xs=E) :
    xs∈shortWords choices xs.length lo S E := by
  induction xs generalizing lo S E with
  | nil => simp_all [squareSum,shortWords]
  | cons a xs ih =>
    obtain ⟨left,sorted⟩ := List.pairwise_cons.mp order
    obtain ⟨allowed,alow⟩ := domain a (by simp)
    cases xs with
    | nil => simp_all [squareSum,shortWords]
    | cons b bs =>
      cases bs with
      | nil =>
        have bb := domain b (by simp)
        apply finalPair_mem choices allowed bb.1 alow (left b (by simp))
        · simpa using sm
        · simpa [squareSum] using sq
      | cons c cs =>
        let tail:=b::c::cs
        change a+tail.sum=S at sm
        change a^2+squareSum tail=E at sq
        have en:=squareSum_nonnegative tail
        have ge:=lower_sum left
        have above : ((cs.length+3:ℕ):ℤ)*a≤S := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at ge
          change a+(b::c::cs).sum=S at sm
          push_cast; linarith
        change _∈List.flatMap _ choices
        apply List.mem_flatMap.mpr
        refine ⟨a,allowed,?_⟩
        rw [ite_eq_left ⟨alow,by omega,above⟩]
        apply List.mem_map.mpr
        exact ⟨tail,ih _ _ _ sorted (fun x h=>⟨(domain x (by simp [h])).1,left x h⟩)
          (show tail.sum=S-a by omega) (show squareSum tail=E-a^2 by omega),rfl⟩

theorem short_possible {xs choices : List ℤ} {L S E : ℤ} (domain : ∀x∈xs,x∈choices ∧ L≤x)
    (sm : xs.sum=S) (sq : squareSum xs=E) :
    ∃ ys∈shortWords choices xs.length L S E, xs.Perm ys ∧ xs∈orders xs.length ys := by
  let ys := xs.mergeSort
  have eq : ys.Perm xs := List.mergeSort_perm _ _
  have ord : ys.Pairwise (·≤·) := List.pairwise_mergeSort' (·≤·) xs
  have mem:=shortWords_mem choices ys L S E ord (fun a h=>domain a (eq.mem_iff.mp h))
    (eq.sum_eq.trans sm) ((eq.map (fun x=>x^2)).sum_eq.trans sq)
  rw [eq.length_eq] at mem
  exact ⟨ys,mem,eq.symm,orders_mem _ _ eq.symm⟩

end Signed39.Profiles
