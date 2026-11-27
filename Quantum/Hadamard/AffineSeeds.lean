import Quantum.Hadamard.Affine
import Quantum.Hadamard.ArithmeticReduction

/-! Every nonzero square over an odd prime field is the residue of the order
of an explicit modular Hadamard matrix of order one modulo four. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic Hadamard.Affine

theorem affine_square_seeds {p : ℕ} (hp : p.Prime) (odd : 2<p) : OddSquareSeeds p := by
  letI : Fact p.Prime := ⟨hp⟩
  intro a ha
  have pos := Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have bound := a.val_lt
  have cp : a.val.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos bound)).symm
  obtain ⟨q,hq,prime,mod4,modp⟩ :=
    prime_crt (m:=4) (n:=p) (a:=1) (b:=a.val) (by decide) hp.ne_zero
      (four_coprime_prime hp odd) (by decide) cp p
  letI : Fact q.Prime := ⟨prime⟩
  have qcast : (q:ZMod p)=a := by
    simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff _ _ p).mpr modp
  let t := (a/2).val
  have ts : t ≤ (Finset.univ : Finset (ZMod q)).card := by
    simp only [Finset.card_univ,ZMod.card]
    have ht := (a/2).val_lt
    dsimp [t]; omega
  obtain ⟨T,_,size⟩ := Finset.exists_subset_card_eq ts
  have nz : (2:ZMod p)≠0 := by
    intro e
    have eq : ((2:ℕ):ZMod p)=((0:ℕ):ZMod p) := by simpa using e
    have he := (ZMod.natCast_eq_natCast_iff _ _ p).mp eq
    change 2%p=0%p at he
    simp [Nat.mod_eq_of_lt odd] at he
  have hT : 2*(T.card:ZMod p)=(q:ZMod p) := by
    rw [size,qcast]
    dsimp [t]
    rw [ZMod.natCast_zmod_val]
    field_simp
  refine ⟨q^2,pow_pos prime.pos 2,at_square_order T hT,?_,by simp [qcast]⟩
  simpa using mod4.pow 2

theorem kuperberg_given_twice_odd_seed {p:ℕ} (prime:p.Prime) (odd:2<p)
    (oneSeed : TwiceOddNonsquareSeed p) :
    ∃ B : ℕ, ∀ n ≥ B, AtOrder p n ↔ KuperbergAdmissible p n :=
  kuperberg_of_one_nonsquare prime odd (affine_square_seeds prime odd) oneSeed

#print axioms affine_square_seeds
#print axioms kuperberg_given_twice_odd_seed
end HadamardMod
