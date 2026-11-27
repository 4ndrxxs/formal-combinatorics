import Quantum.Hadamard.ArithmeticSeed
import Quantum.Hadamard.Asymptotic

/-! Lexicographic prime products work at an arbitrary odd composite modulus
when the residue immediately below the target is a unit. -/

namespace Hadamard.Arithmetic

theorem composite_seed_class {m n₀ a : ℕ} {P : ℕ → Prop} (hm : 1 < m)
    (c2 : (2 : ℕ).Coprime m) (ca : a.Coprime m) (res : n₀ ≡ a+1 [MOD m])
    (C : PrimeOrderConstruction m P) (pos : 0 < n₀) (seed : P n₀) :
    ∃ B, ∀ n ≥ B, n ≡ n₀ [MOD 4] → n ≡ n₀ [MOD m] → P n := by
  obtain ⟨q,p₁,p₂,hq,q4,qa,h₁,h₂,gcd⟩ := product_steps_of_unit hm c2 ca
  have pos₂ : 0 < (p₂*q-1)/4 := by
    have hq2 := hq.two_le
    have p4 := h₂.modFour
    change p₂%4 = 3%4 at p4
    have hp : 3 ≤ p₂ := by omega
    have h : 6 ≤ p₂*q := by nlinarith
    omega
  have grow {p n : ℕ} (hp : ProductStep m q p) (hn : 0<n) (pn : P n)
      (nr : n ≡ n₀ [MOD m]) (t : ℕ) : P (n+t*(4*((p*q-1)/4))) := by
    have h4 : p*q ≡ 1 [MOD 4] := (hp.modFour.mul q4).trans (by decide)
    have po : 1 ≤ p*q := Nat.mul_pos hp.prime.pos hq.pos
    rw [Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' po).mp h4.symm)]
    exact C.productGrow hq q4 hp hn pn ((nr.trans res).trans (qa.add_right 1).symm) t
  exact close_from_seed (by omega) (c2.pow_left 2) gcd pos₂ pos seed (grow h₁) (grow h₂)

theorem composite_class_large {m r a : ℕ} (hm : 1 < m)
    (c2 : (2 : ℕ).Coprime m) (ca : a.Coprime m) (res : r ≡ a+1 [MOD m])
    (seeds : ∀ c : Fin 4, ∃ k > 0, HadamardMod.AtOrder m k ∧ k ≡ c.val [MOD 4] ∧ k ≡ r [MOD m]) :
    ∃ B, ∀ n ≥ B, n ≡ r [MOD m] → HadamardMod.AtOrder m n := by
  classical
  have cls (c : Fin 4) : ∃ B, ∀ n ≥ B, n ≡ c.val [MOD 4] → n ≡ r [MOD m] →
      HadamardMod.AtOrder m n := by
    obtain ⟨k,pos,K,k4,km⟩ := seeds c
    obtain ⟨B,hB⟩ := composite_seed_class hm c2 ca (km.trans res)
      (HadamardMod.primeConstruction m) pos K
    exact ⟨B,fun n hn c4 mr => hB n hn (c4.trans k4.symm) (mr.trans km.symm)⟩
  choose bound hbound using cls
  refine ⟨Finset.univ.sup bound, ?_⟩
  intro n hn hr
  let i : Fin 4 := ⟨n%4, Nat.mod_lt _ (by decide)⟩
  exact hbound i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) (Nat.mod_modEq n 4).symm hr

end Hadamard.Arithmetic
