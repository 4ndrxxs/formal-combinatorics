import KimberlingBlocks

namespace KimberlingMoses

def generalPos (k n : ℕ) : ℕ := if n%(k+1)=0 then 2 else 3
abbrev generalA (h k : ℕ) := blockA (h*(k+1)) (generalPos k)
abbrev generalB (h k : ℕ) := blockB (h*(k+1)) (generalPos k)

/-- Evaluate the B entry at a multiple of `h`. -/
private theorem scaledB (h k n : ℕ) (hh : 2 ≤ h) :
    generalB h k (h*n) = (h*(k+1)+1)*(n/(k+1)) + h*(n%(k+1)) +
      (if n%(k+1)=0 then 1 else 2) := by
  have hp : 0 < k+1 := by omega
  have hm := Nat.mod_lt n hp
  have hd := Nat.div_add_mod n (k+1)
  have he : h*n = (h*(k+1))*(n/(k+1)) + h*(n%(k+1)) := by
    calc h*n = h*((k+1)*(n/(k+1))+n%(k+1)) := by rw [hd]
         _ = _ := by ring
  have hr : h*(n%(k+1)) < h*(k+1) := Nat.mul_lt_mul_of_pos_left hm (by omega)
  unfold generalB
  rw [he, blockB_at _ (Nat.mul_pos (by omega) hp) _ _ _ hr]
  by_cases zero : n%(k+1)=0
  · simp [zero, skip, generalPos]; split_ifs <;> decide
  · have small : 2 ≤ h*(n%(k+1)) := by
      calc 2 ≤ h := hh
           _ ≤ h*(n%(k+1)) := Nat.le_mul_of_pos_right _ (by omega)
    have t : generalPos k (n/(k+1)) ≤ h*(n%(k+1))+1 := by unfold generalPos; split_ifs <;> omega
    simp [zero,skip,t]; omega

private theorem division_cases (k n : ℕ) :
    (n%(k+1)=0 ∧ (k*n)%(k+1)=0 ∧ n/(k+1)+(k*n)/(k+1)=n) ∨
    (n%(k+1)≠0 ∧ (k*n)%(k+1)≠0 ∧ n%(k+1)+(k*n)%(k+1)=k+1 ∧
      n/(k+1)+(k*n)/(k+1)+1=n) := by
  let P := k+1
  change (n%P=0 ∧ (k*n)%P=0 ∧ n/P+(k*n)/P=n) ∨
    (n%P≠0 ∧ (k*n)%P≠0 ∧ n%P+(k*n)%P=P ∧ n/P+(k*n)/P+1=n)
  have hp : 0 < P := by dsimp [P]; omega
  have hn := Nat.mod_lt n hp; have hk := Nat.mod_lt (k*n) hp
  have eqn : P*(n/P+(k*n)/P)+(n%P+(k*n)%P)=P*n := by
    calc _ = (P*(n/P)+n%P)+(P*((k*n)/P)+(k*n)%P) := by ring
         _ = n+k*n := by rw [Nat.div_add_mod,Nat.div_add_mod]
         _ = _ := by dsimp [P]; ring
  have hmod := congrArg (fun j => j%P) eqn
  simp only [Nat.mul_add_mod_self_left, Nat.mul_mod_right] at hmod
  obtain ⟨w,hw⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hw1 : w ≤ 1 := by
    by_contra! hmore
    have ht := Nat.mul_le_mul_left P (show 2 ≤ w by omega)
    omega
  interval_cases w
  · simp at hw
    have hsum : n/P+(k*n)/P=n := by apply Nat.eq_of_mul_eq_mul_left hp; omega
    left; exact ⟨by omega,by omega,hsum⟩
  · simp at hw
    have hsum : n/P+(k*n)/P+1=n := by apply Nat.eq_of_mul_eq_mul_left hp; rw [Nat.mul_add,Nat.mul_one]; omega
    right; exact ⟨by omega,by omega,hw,hsum⟩

theorem general_solution (h k : ℕ) (hh : 2 ≤ h) (hk : 2 ≤ k) :
    OffsetSolution h (k*h) 0 (generalA h k) (generalB h k) where
  toComplementary := block_complementary _ (by positivity) _ (fun q => by
    unfold generalPos; have hp : 1 ≤ k+1 := by omega
    have hl := Nat.le_mul_of_pos_right h (by omega : 0<k+1); split_ifs <;> omega)
  initial := by simpa using scaledB h k 0 hh
  equation n := by
    have hmul : (k*h)*n = h*(k*n) := by ring
    rw [hmul, scaledB h k n hh, scaledB h k (k*n) hh]; unfold generalA blockA generalPos
    rcases division_cases k n with ⟨hr,hs,hq⟩ | ⟨hr,hs,hm,hq⟩
    · simp only [hr,hs,ite_true,Nat.mul_zero,Nat.add_zero]
      have := congrArg (fun q => (h*(k+1)+1)*q) hq
      nlinarith only [this]
    · simp only [hr,hs,ite_false,Nat.add_zero]
      have h1 := congrArg (fun q => (h*(k+1)+1)*q) hq
      have h2 := congrArg (fun r => h*r) hm
      nlinarith only [h1,h2]

/-- The exact general solution underlying Conjecture 6 of the paper. -/
theorem general_formula {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (n : ℕ) :
    a n = (h*(k+1)+1)*n + if n%(k+1)=0 then 2 else 3 := by
  rw [(offset_unique sol (general_solution h k hh hk)).1]; rfl

theorem general_A_period {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (n : ℕ) :
    a (n+(k+1)) = a n + (h*(k+1)+1)*(k+1) := by
  rw [general_formula hh hk sol, general_formula hh hk sol, Nat.add_mod_right]; ring

/-- The full set of initial values written in Conjecture 6. -/
theorem general_A_initial {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) :
    a 0=2 ∧ ∀ j, 1≤j → j≤k → a j = j*h*(k+1)+j+3 := by
  constructor
  · simp [general_formula hh hk sol]
  · intro j hj hmax
    rw [general_formula hh hk sol,Nat.mod_eq_of_lt (by omega : j<k+1),ite_eq_right (by omega)]; ring

/-- Correct replacement for the modulus in Conjecture 6. The positive A values
are precisely the residue classes of `a 0,...,a k` modulo `(h*(k+1)+1)*(k+1)`. -/
theorem general_A_classes {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (x : ℕ) :
    (∃ n, a n=x) ↔ ∃ r, r≤k ∧ x%((h*(k+1)+1)*(k+1)) = a r := by
  let P := k+1; let S := h*P+1; let D := S*P
  have hP : 0<P := by dsimp [P]; omega
  have hS : 3<S := by
    have ht := Nat.mul_le_mul_left h (show 3≤P by dsimp [P]; omega); dsimp [S]; omega
  have calcA (q r : ℕ) (hr : r<P) : a (P*q+r) = D*q+a r := by
    rw [general_formula hh hk sol,general_formula hh hk sol]
    change S*(P*q+r)+(if (P*q+r)%P=0 then 2 else 3) = D*q+(S*r+if r%P=0 then 2 else 3)
    rw [Nat.mul_add_mod_self_left]; dsimp [D]; ring
  have small (r : ℕ) (hr : r<P) : a r<D := by
    rw [general_formula hh hk sol]; change S*r+(if r%P=0 then 2 else 3)<S*P
    have ht := Nat.mul_le_mul_left S (show r+1≤P by omega)
    rw [Nat.mul_add,Nat.mul_one] at ht; split_ifs <;> omega
  change (∃ n, a n=x) ↔ ∃ r, r≤k ∧ x%D=a r
  constructor
  · rintro ⟨n,rfl⟩
    have hr := Nat.mod_lt n hP
    refine ⟨n%P,by dsimp [P] at hr ⊢; omega,?_⟩
    have ht := calcA (n/P) (n%P) hr
    rw [Nat.div_add_mod] at ht
    rw [ht,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (small _ hr)]
  · rintro ⟨r,hr,hx⟩
    refine ⟨P*(x/D)+r,?_⟩; rw [calcA _ r (by dsimp [P]; omega),← hx,Nat.div_add_mod]

/-- The A recurrence in Conjecture 6, written without truncated subtraction. -/
theorem general_A_recurrence {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (n : ℕ) :
    a (n+k+2)+a n = a (n+k+1)+a (n+1) := by
  have h0 := general_A_period hh hk sol n; have h1 := general_A_period hh hk sol (n+1)
  rw [show n+1+(k+1)=n+k+2 by omega] at h1
  rw [show n+(k+1)=n+k+1 by omega] at h0; omega

/-- The B index period for first differences is `h*(k+1)^2`. -/
theorem general_B_period {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (n : ℕ) :
    b (n+h*(k+1)*(k+1)) = b n + (h*(k+1)+1)*(k+1) := by
  let H := h*(k+1)
  have hH : 0 < H := by dsimp [H]; positivity
  rw [(offset_unique sol (general_solution h k hh hk)).2]; unfold generalB blockB
  change (H+1)*((n+H*(k+1))/H)+skip (generalPos k ((n+H*(k+1))/H)) ((n+H*(k+1))%H) = _
  rw [Nat.add_mul_div_left _ _ hH, Nat.add_mul_mod_self_left]
  have hpos : generalPos k (n/H+(k+1)) = generalPos k (n/H) := by simp [generalPos]
  rw [hpos]; change _ = ((H+1)*(n/H)+skip (generalPos k (n/H)) (n%H))+(H+1)*(k+1); ring

theorem general_B_recurrence {h k : ℕ} (hh : 2 ≤ h) (hk : 2 ≤ k) {a b : ℕ → ℕ}
    (sol : OffsetSolution h (k*h) 0 a b) (n : ℕ) :
    let m := h*(k+1)*(k+1)
    b (n+m+1)+b n = b (n+m)+b (n+1) := by
  dsimp only
  have h0 := general_B_period hh hk sol n; have h1 := general_B_period hh hk sol (n+1)
  rw [show n+1+h*(k+1)*(k+1) = n+h*(k+1)*(k+1)+1 by omega] at h1; omega

/-- At h=3, k=2, the proposed modulus is 24. The term `a 3 = 32` has residue
eight, outside the three residues of `a 0`, `a 1`, `a 2`. -/
theorem conjecture6_modulus_counterexample {a b : ℕ → ℕ} (s : OffsetSolution 3 6 0 a b) :
    a 3 = 32 ∧ ∀ i ≤ 2, a 3 % 24 ≠ a i % 24 := by
  rw [(offset_unique s (general_solution 3 2 (by decide) (by decide))).1]
  exact ⟨by decide, fun i hi => by interval_cases i <;> decide⟩

/-- At h=k=2 the published B recurrence uses m=13; n=19 refutes it. -/
theorem conjecture6_B_counterexample {a b : ℕ → ℕ} (s : OffsetSolution 2 4 0 a b) :
    b 19 ≠ b 18 + b 6 - b 5 := by
  rw [(offset_unique s (general_solution 2 2 (by decide) (by decide))).2]; decide

#print axioms general_formula
#print axioms general_A_classes
#print axioms general_A_initial
#print axioms general_A_recurrence
#print axioms general_B_period
#print axioms general_B_recurrence
#print axioms conjecture6_modulus_counterexample
#print axioms conjecture6_B_counterexample

end KimberlingMoses
