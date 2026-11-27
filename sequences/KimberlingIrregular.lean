import KimberlingBlocks
import KimberlingGaps

namespace KimberlingMoses

def irregularPos (q : ℕ) : ℕ := if bit q then 4 else 3
abbrev irregularA := blockA 6 irregularPos
abbrev irregularB := blockB 6 irregularPos

private theorem irregularB_zero (q : ℕ) : irregularB (6*q) = 7*q+1 := by
  have h := blockB_at 6 (by decide) irregularPos q 0 (by decide)
  cases hg : bit q <;> simpa [irregularB,skip,irregularPos,hg] using h

private theorem irregularB_two (q : ℕ) : irregularB (6*q+2) = 7*q+(if bit q then 3 else 4) := by
  unfold irregularB; rw [blockB_at _ (by decide) _ _ _ (by decide)]
  unfold skip irregularPos; cases bit q <;> rfl

private theorem irregularB_four (q : ℕ) : irregularB (6*q+4) = 7*q+6 := by
  unfold irregularB; rw [blockB_at _ (by decide) _ _ _ (by decide)]
  unfold skip irregularPos; cases bit q <;> rfl

theorem irregular_solution : OffsetSolution 2 4 1 irregularA irregularB where
  toComplementary := block_complementary 6 (by decide) _ (fun q => by unfold irregularPos; split_ifs <;> omega)
  initial := by simpa using irregularB_zero 0
  equation n := by
    obtain ⟨q,h|h|h⟩ := three_cases n <;> subst n <;> unfold irregularA blockA irregularPos
    · rw [bit_zero,show 2*(3*q)=6*q by omega,show 4*(3*q)=6*(2*q) by omega,
        irregularB_zero,irregularB_zero]; simp; omega
    · rw [bit_one,show 2*(3*q+1)=6*q+2 by omega,show 4*(3*q+1)=6*(2*q)+4 by omega,
        irregularB_two,irregularB_four]; cases bit q <;> simp <;> omega
    · rw [bit_two,show 2*(3*q+2)=6*q+4 by omega,show 4*(3*q+2)=6*(2*q+1)+2 by omega,
        irregularB_four,irregularB_two]; cases bit (2*q+1) <;> simp <;> omega

theorem irregular_upper {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) (n : ℕ) :
    a n = 7*n+4 ↔ bit n = true := by
  rw [(offset_unique s irregular_solution).1]; unfold irregularA blockA irregularPos; cases bit n <;> simp

/-- Positive periods on a sufficiently late tail are included. -/
def TailPeriod {α : Type*} (f : ℕ → α) (p : ℕ) : Prop := ∃ N, ∀ n ≥ N, f (n+p) = f n

private theorem bit_false_of_mod_zero {n : ℕ} (hn : n%3=0) : bit n = false := by
  rw [show n = 3*(n/3) by omega]; exact bit_zero _

private theorem divides_period {p : ℕ} (h : TailPeriod bit p) : p%3=0 := by
  obtain ⟨N,hN⟩ := h
  let n := 9*N+1
  have hn : N ≤ n := by dsimp [n]; omega
  have hbit : bit n = true := bit_nine_one N
  have h1 := hN n hn
  have h2 := hN (n+p) (by omega)
  by_contra hp
  rcases (show p%3=1 ∨ p%3=2 by omega) with r|r
  · have hz : (n+p+p)%3=0 := by dsimp [n]; omega
    rw [bit_false_of_mod_zero hz,h1,hbit] at h2; contradiction
  · have hz : (n+p)%3=0 := by dsimp [n]; omega
    rw [bit_false_of_mod_zero hz,hbit] at h1; contradiction

private theorem reduce_period (p : ℕ) (h : TailPeriod bit (3*p)) : TailPeriod bit p := by
  obtain ⟨N,hN⟩ := h; refine ⟨N, ?_⟩; intro n hn
  have he := hN (3*n+1) (by omega)
  rw [show 3*n+1+3*p=3*(n+p)+1 by omega,bit_one,bit_one] at he
  simpa using he

theorem bit_aperiodic (p : ℕ) (hp : 0 < p) : ¬TailPeriod bit p := by
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    intro per
    have hd := divides_period per
    have hp' : p=3*(p/3) := by omega
    have lower : TailPeriod bit (p/3) := reduce_period (p/3) (by simpa only [← hp'] using per)
    exact ih _ (by omega) (by omega) lower

/-- The increasing sequence of indices singled out in (10). -/
noncomputable def upperIndices (a : ℕ → ℕ) : ℕ → ℕ := Nat.nth (fun n => a n = 7*n+4)

private theorem upper_infinite {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) :
    (Set.ofPred fun n => a n = 7*n+4).Infinite := by
  apply Set.infinite_of_forall_exists_gt; intro n
  exact ⟨9*n+1,(irregular_upper s _).mpr (bit_nine_one _),by omega⟩

theorem indices_strict {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) : StrictMono (upperIndices a) :=
  Nat.nth_strictMono (upper_infinite s)

theorem indices_range {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) (n : ℕ) :
    (∃ i, upperIndices a i = n) ↔ bit n = true := by
  change n ∈ Set.range (Nat.nth (fun n => a n = 7*n+4)) ↔ _
  rw [Nat.range_nth_of_infinite (upper_infinite s)]; exact irregular_upper s n

private theorem bounded_gaps {r : ℕ → ℕ} (strict : StrictMono r)
    (range : ∀ n, (∃ i, r i = n) ↔ bit n = true) (n : ℕ) : r (n+1)-r n ≤ 5 := by
  obtain ⟨j,lo,hi,good⟩ := good_within_five explicit_solution (r n+1)
  obtain ⟨k,hk⟩ := (range _).mpr ((good_iff_bit explicit_solution j).mp good)
  have hnk : n < k := strict.lt_iff_lt.mp (by omega)
  have ht := strict.monotone (show n+1 ≤ k by omega); omega

private theorem shift_rec {E : LinearRecurrence ℂ} {f : ℕ → ℂ} (rec : E.IsSolution f) (s : ℕ) :
    E.IsSolution (fun n => f (s+n)) := fun n => by simpa [Nat.add_assoc] using rec (s+n)

/-- A bounded integer sequence satisfying a constant-coefficient complex linear
recurrence has a repeated finite window, which determines its entire future. -/
private theorem bounded_recurrence_period (d : ℕ → ℕ) (M : ℕ) (bd : ∀ n, d n ≤ M)
    {E : LinearRecurrence ℂ} (rec : E.IsSolution (fun n => (d n:ℂ))) :
    ∃ p, 0 < p ∧ TailPeriod d p := by
  let window (n : ℕ) (j : Fin E.order) : Fin (M+1) := ⟨d (n+j), by have := bd (n+j); omega⟩
  obtain ⟨i,j,hij,hw⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f:=window) (fun _ => Set.mem_univ _)
  have same (t : ℕ) : (d (j+t):ℂ) = (d (i+t):ℂ) := by
    let init (l : Fin E.order) : ℂ := d (i+l)
    have left := E.eq_mk_of_is_sol_of_eq_init (shift_rec rec j) (init:=init) (by
      intro l; have hel := congrArg Fin.val (congrFun hw l); dsimp [window] at hel
      change (d (j+l):ℂ) = (d (i+l):ℂ); exact_mod_cast hel.symm) t
    have right := E.eq_mk_of_is_sol_of_eq_init (shift_rec rec i) (init:=init) (by intro l; rfl) t
    exact left.trans right.symm
  refine ⟨j-i,by omega,i,?_⟩; intro n hn
  have he : d (j+(n-i)) = d (i+(n-i)) := by exact_mod_cast same (n-i)
  convert he using 2 <;> omega

private theorem period_of_bounded_gaps {r : ℕ → ℕ} (strict : StrictMono r)
    (range : ∀ n, (∃ i, r i=n) ↔ bit n = true) (p : ℕ) (hp : 0<p)
    (hper : TailPeriod (fun n => r (n+1)-r n) p) : False := by
  obtain ⟨N,hn⟩ := hper
  let D := r (N+p)-r N
  have hd : 0<D := by dsimp [D]; have := strict (show N<N+p by omega); omega
  have inc (s : ℕ) : r (N+s+p) = r (N+s)+D := by
    induction s with
    | zero => dsimp [D]; have := strict.monotone (show N≤N+p by omega); omega
    | succ s ih =>
      have he := hn (N+s) (by omega)
      dsimp only at he
      have h1 := strict (show N+s<N+s+1 by omega)
      have h2 := strict (show N+s+p<N+s+p+1 by omega)
      rw [show N+(s+1)+p=N+s+p+1 by omega,show N+(s+1)=N+s+1 by omega]; omega
  have inc' (j : ℕ) (hj : N≤j) : r (j+p)=r j+D := by simpa only [Nat.add_sub_of_le hj] using inc (j-N)
  apply bit_aperiodic D hd
  refine ⟨r (N+p), ?_⟩; intro x hx
  have iff : bit (x+D)=true ↔ bit x=true := by
    rw [← range,← range]; constructor
    · rintro ⟨j,hj⟩
      have hjN : N+p≤j := strict.le_iff_le.mp (by omega)
      have he := inc' (j-p) (by omega)
      rw [show j-p+p=j by omega] at he
      exact ⟨j-p,by omega⟩
    · rintro ⟨j,hj⟩
      have hjN : N+p≤j := strict.le_iff_le.mp (by omega)
      exact ⟨j+p,by rw [inc' j (by omega),hj]⟩
  simpa using iff

/-- Conjecture 8, first assertion. Even an eventual complex-coefficient linear
recurrence for the increasing sequence (10) is impossible. -/
theorem conjecture8_nonrecurrence {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) :
    ¬∃ (N : ℕ) (E : LinearRecurrence ℂ), E.IsSolution (fun n => (upperIndices a (N+n):ℂ)) := by
  rintro ⟨N,E,rec⟩
  let r := upperIndices a
  have strict : StrictMono r := indices_strict s
  have mem := indices_range s
  let d n := r (N+n+1)-r (N+n)
  have bd (n : ℕ) : d n ≤ 5 := bounded_gaps strict mem (N+n)
  have hnext := shift_rec rec 1
  have hnext' : (fun n => (r (N+(1+n)):ℂ)) ∈ E.solSpace := hnext
  have hrec' : (fun n => (r (N+n):ℂ)) ∈ E.solSpace := rec
  have diff : E.IsSolution (fun n => (r (N+(1+n)):ℂ) - (r (N+n):ℂ)) := E.solSpace.sub_mem hnext' hrec'
  have hre : E.IsSolution (fun n => (d n:ℂ)) := by
    have eqn (n : ℕ) : (d n:ℂ) = (r (N+(1+n)):ℂ) - (r (N+n):ℂ) := by
      dsimp only [d]; rw [Nat.cast_sub (strict.monotone (by omega)), show N+(1+n)=N+n+1 by omega]
    simpa only [eqn] using diff
  obtain ⟨p,hp,T,hT⟩ := bounded_recurrence_period d 5 bd hre
  apply period_of_bounded_gaps strict mem p hp
  refine ⟨N+T, ?_⟩; intro n hn
  have he := hT (n-N) (by omega); dsimp [d] at he
  rw [show N+(n-N+p)=n+p by omega, show N+(n-N)=n by omega] at he; exact he

#print axioms conjecture8_nonrecurrence

/-- Identifies consecutive index differences with the gaps defined by set membership. -/
theorem conjecture8_index_gaps {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) (g : ℕ) :
    (∃ j, upperIndices a (j+1) - upperIndices a j = g) ↔ 1 ≤ g ∧ g ≤ 5 := by
  let r := upperIndices a
  have strict : StrictMono r := indices_strict s
  have mem := indices_range s
  constructor
  · rintro ⟨j,rfl⟩; change 1 ≤ r (j+1)-r j ∧ r (j+1)-r j ≤ 5
    have hlt := strict (show j<j+1 by omega)
    exact ⟨by omega,bounded_gaps strict mem j⟩
  · intro hg
    obtain ⟨pos,i,hi,he,hno⟩ := (conjecture18 explicit_solution g).mpr hg
    obtain ⟨j,hj⟩ := (mem i).mpr ((good_iff_bit explicit_solution _).mp hi)
    obtain ⟨k,hk⟩ := (mem (i+g)).mpr ((good_iff_bit explicit_solution _).mp he)
    change r j = i at hj; change r k = i+g at hk
    have hjk : j < k := strict.lt_iff_lt.mp (by omega)
    have hsucc : k = j+1 := by
      by_contra neq
      have hlo := strict (show j<j+1 by omega)
      have hhi := strict (show j+1<k by omega)
      have has := (good_iff_bit explicit_solution (r (j+1))).mpr ((mem _).mp ⟨j+1,rfl⟩)
      have no := hno (r (j+1)-i) (by omega) (by omega)
      rw [show i+(r (j+1)-i)=r (j+1) by omega] at no; exact no has
    exact ⟨j,by change r (j+1)-r j=g; subst k; omega⟩

/-- The second line of the printed Conjecture 8 uses `a` rather than the index
sequence `r` in (10). The literal A differences have exactly the values 6,7,8. -/
theorem conjecture8_printed_gaps {a b : ℕ → ℕ} (s : OffsetSolution 2 4 1 a b) (g : ℕ) :
    (∃ j, a (j+1)-a j = g) ↔ g=6 ∨ g=7 ∨ g=8 := by
  rw [(offset_unique s irregular_solution).1]
  constructor
  · rintro ⟨j,rfl⟩; unfold irregularA blockA irregularPos; split_ifs <;> omega
  · rintro (rfl|rfl|rfl)
    · refine ⟨1,?_⟩; unfold irregularA blockA irregularPos
      have h1 : bit 1 = true := bit_nine_one 0
      have h2 : bit 2 = false := by simpa [h1] using bit_two 0
      change (7*2+(if bit 2 then 4 else 3))-(7*1+(if bit 1 then 4 else 3))=6
      simp [h1,h2]
    · refine ⟨2,?_⟩; unfold irregularA blockA irregularPos
      have h1 : bit 1 = true := bit_nine_one 0
      have h2 : bit 2 = false := by simpa [h1] using bit_two 0
      have h3 : bit 3 = false := bit_zero 1
      change (7*3+(if bit 3 then 4 else 3))-(7*2+(if bit 2 then 4 else 3))=7
      simp [h2,h3]
    · refine ⟨0,?_⟩; unfold irregularA blockA irregularPos
      have h1 : bit 1 = true := bit_nine_one 0
      have h0 : bit 0 = false := bit_zero 0
      change (7*1+(if bit 1 then 4 else 3))-(7*0+(if bit 0 then 4 else 3))=8
      simp [h0,h1]

#print axioms conjecture8_index_gaps
#print axioms conjecture8_printed_gaps

end KimberlingMoses
