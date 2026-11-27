import SignedMixedVariance

/-! A sharper correlation variance for a row paired with itself. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem fixed_zero_variance (z : H → ℤ) (z0 : z 0=0) :
    let m : ℤ := Fintype.card H; let S := mass z; let r := S%(m-1)
    S^2+m*r*(m-1-r)≤(m-1)*variance z := by
  dsimp only
  let m : ℤ := Fintype.card H
  let S:=mass z
  let q:=S/(m-1)
  let r:=S%(m-1)
  have decomp : S=r+(m-1)*q := (Int.emod_add_mul_ediv S (m-1)).symm
  have positive (x : H) : 0≤(z x-q)*(z x-q-1) := by
    rcases le_total (z x-q) 0 with h|h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · by_cases t : z x-q=0
      · simp [t]
      · exact mul_nonneg h (by omega)
  have bound := single_le_sum (s:=univ) (fun x _=>positive x) (mem_univ 0)
  have ev : (∑ x:H,(z x-q)*(z x-q-1))=energy z-(2*q+1)*S+m*q*(q+1) := by
    calc
      _=∑ x:H,((z x)^2-(2*q+1)*z x+q*(q+1)) := by apply sum_congr rfl; intros; ring
      _=_ := by simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul]; change _=energy z-(2*q+1)*S+m*q*(q+1); dsimp [energy,mass,S,m]; ring
  rw [ev,z0] at bound
  have small : 0≤energy z-(2*q+1)*S+(m-1)*q*(q+1) := by linarith only [bound]
  have mpos : 1 ≤ m := by dsimp [m]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card H)
  have nn := mul_nonneg (mul_nonneg (show 0 ≤ m by omega) (show 0 ≤ m-1 by omega)) small
  have identity : (m-1)*(m*energy z-S^2)-(S^2+m*r*(m-1-r))=
      m*(m-1)*(energy z-(2*q+1)*S+(m-1)*q*(q+1)) := by rw [decomp]; ring
  change S^2+m*r*(m-1-r)≤(m-1)*(m*energy z-S^2)
  omega

variable {p : ℕ} [Fact p.Prime]

theorem self_pair_bound {k l s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬(p:ℤ)∣s) (cop : p.Coprime (Fintype.card H)) (i : ZMod p) :
    let u:=row f i; let m : ℤ := Fintype.card H
    ∃ D : ℤ, (p:ℤ)*D=variance u ∧
      (p:ℤ)^2*(D^2+m*(D%(m-1))*(m-1-D%(m-1)))≤(m-1)*variance (cross u u) := by
  dsimp only
  let u:=row f i
  let m : ℤ := Fintype.card H
  have divides (t:H) : (p:ℤ)∣displacement u t := row_displacement_dvd hf hn hs cop i t
  choose z hz using divides
  have pn : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have dz := hz 0
  rw [displacement,←energy_zero,sub_self] at dz
  have z0 : z 0=0 := (mul_eq_zero.mp dz.symm).resolve_left pn
  have word : cross u u=fun t=>energy u+(-(p:ℤ))*z t := by
    funext t
    change corr u t=_
    have eq:=hz t
    change energy u-corr u t=(p:ℤ)*z t at eq
    linear_combination -eq
  have ms:=cross_mass u u
  rw [word] at ms
  simp only [mass,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum] at ms
  have div : (p:ℤ)*mass z=variance u := by
    change (p:ℤ)*(∑x,z x) = m*energy u-(∑x,u x)^2
    change m*energy u+(-(p:ℤ))*(∑x,z x)=(∑x,u x)*(∑x,u x) at ms
    linear_combination -ms
  refine ⟨mass z,div,?_⟩
  rw [word,variance_affine,neg_sq]
  have lo:=fixed_zero_variance z z0
  have mul:=mul_le_mul_of_nonneg_left lo (sq_nonneg (p:ℤ))
  linear_combination mul

#print axioms self_pair_bound

end Signed39.Contraction
