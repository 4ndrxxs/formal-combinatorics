import Mathlib

/-!
# Universal perfect state transfer in bipartite edge walks

Each edge has a left endpoint and a right endpoint. A time step first reflects
in the subspace of vectors constant at right endpoints, then does the same at
left endpoints. All scalar coordinates in this file are complex.
-/

namespace BipartiteEdgeWalk

noncomputable section
set_option linter.unusedSectionVars false

open Finset Function
open scoped BigOperators

variable {E L R V : Type*} [Fintype E] [DecidableEq E]
variable [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
variable [Fintype V] [DecidableEq V]

def fiber (side : E → V) (u : V) : Finset E := univ.filter (fun a => side a = u)

def degree (side : E → V) (u : V) : ℕ := (fiber side u).card

def mass (side : E → V) (v : E → ℂ) (u : V) : ℂ := ∑ a ∈ fiber side u, v a

def reflect (side : E → V) (v : E → ℂ) (a : E) : ℂ :=
  2 * mass side v (side a) / degree side (side a) - v a

def walk (left : E → L) (right : E → R) (v : E → ℂ) : E → ℂ :=
  reflect left (reflect right v)

def delta (a : E) (e : E) : ℂ := if e = a then 1 else 0

/-- Integer time, allowing the trivial return at time zero, and a global unit phase. -/
def UniversalPST (left : E → L) (right : E → R) : Prop :=
  ∀ a b : E, ∃ k : ℕ, ∃ z : ℂ,
    ‖z‖ = 1 ∧ (walk left right)^[k] (delta a) = z • (delta b)

private theorem degree_pos (side : E → V) (hs : Surjective side) (u : V) :
    0 < degree side u := by
  obtain ⟨a, ha⟩ := hs u
  exact Finset.card_pos.mpr ⟨a, by simp [fiber, ha]⟩

private theorem mass_sum (side : E → V) (v : E → ℂ) :
    ∑ u, mass side v u = ∑ a, v a := by
  exact Finset.sum_fiberwise_of_maps_to (s := (univ : Finset E)) (t := (univ : Finset V))
    (g := side) (fun _ _ => mem_univ _) v

private theorem sum_degree (side : E → V) :
    ∑ u, degree side u = Fintype.card E := by
  simpa [degree, fiber] using
    (Finset.sum_card_fiberwise_eq_card_filter (s := (univ : Finset E))
      (t := (univ : Finset V)) side)

private theorem mass_reflect (side : E → V) (hs : Surjective side) (v : E → ℂ) (u : V) :
    mass side (reflect side v) u = mass side v u := by
  have hd : (degree side u : ℂ) ≠ 0 := by exact_mod_cast (degree_pos side hs u).ne'
  change (∑ a ∈ fiber side u, _) = _
  calc
    _ = ∑ a ∈ fiber side u, (2 * mass side v u / degree side u - v a) := by
      apply sum_congr rfl
      intro a ha
      simp only [fiber, mem_filter, mem_univ, true_and] at ha
      simp only [reflect, ha]
    _ = _ := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
      change degree side u * (2 * mass side v u / degree side u) - mass side v u = _
      field_simp
      ring

private theorem reflect_invol (side : E → V) (hs : Surjective side) :
    Involutive (reflect side) := by
  intro v
  ext a
  simp [reflect, mass_reflect side hs]

private theorem reflect_sum (side : E → V) (hs : Surjective side) (v : E → ℂ) :
    ∑ a, reflect side v a = ∑ a, v a := by
  rw [← mass_sum side (reflect side v), ← mass_sum side v]
  simp only [mass_reflect side hs]

private theorem sum_iterate {α β : Type*} (f : α → α) (g : α → β) (h : ∀ a, g (f a) = g a)
    (k : ℕ) (a : α) : g (f^[k] a) = g a := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterate_succ_apply', h] using ih

private theorem delta_injective : Injective (delta : E → E → ℂ) := by
  intro a b h
  by_contra hab
  have q := congrFun h a
  simp [delta, hab] at q

private theorem walk_sum {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (v : E → ℂ) :
    ∑ e, walk left right v e = ∑ e, v e := by
  simp only [walk, reflect_sum left hl, reflect_sum right hr]

private theorem distinct_hit {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right)
    {a b : E} (hab : a ≠ b) :
    ∃ k : ℕ, 0 < k ∧ (walk left right)^[k] (delta a) = delta b := by
  obtain ⟨k, z, _, hz⟩ := h a b
  have h' := sum_iterate (walk left right) (fun v => ∑ e, v e) (walk_sum hl hr) k (delta a)
  rw [hz] at h'
  simp [delta] at h'
  have hit : (walk left right)^[k] (delta a) = delta b := by simpa [h'] using hz
  cases k with
  | zero => exact (hab (delta_injective hit)).elim
  | succ k => exact ⟨k + 1, by omega, hit⟩

private theorem exact_pst {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right)
    (a b : E) : ∃ k : ℕ, 0 < k ∧ (walk left right)^[k] (delta a) = delta b := by
  by_cases hab : a = b
  · subst b
    by_cases hc : ∃ c : E, c ≠ a
    · obtain ⟨c, hca⟩ := hc
      obtain ⟨s, hs, h₁⟩ := distinct_hit hl hr h hca.symm
      obtain ⟨t, _, h₂⟩ := distinct_hit hl hr h hca
      exact ⟨t+s, by omega, by rw [iterate_add_apply, h₁, h₂]⟩
    · have all (e : E) : e = a := by
        by_contra hne
        exact hc ⟨e, hne⟩
      have hu : (univ : Finset E) = {a} := by ext e; simp [all e]
      have he := walk_sum hl hr (delta a)
      rw [hu] at he
      simp only [sum_singleton] at he
      refine ⟨1, by decide, ?_⟩
      funext e
      change walk left right (delta a) e = delta a e
      rw [all e]
      exact he
  · exact distinct_hit hl hr h hab

private def pair (v w : E → ℂ) : ℂ := ∑ e, v e * w e

private theorem pair_reflect_of_mass_zero (side : E → V) (v w : E → ℂ)
    (hv : ∀ u, mass side v u = 0) : pair v (reflect side w) = -pair v w := by
  let k := fun u => 2 * mass side w u / degree side u
  have hz (u : V) : mass side (fun e => v e * k (side e)) u = 0 := by
    change (∑ e ∈ fiber side u, v e * k (side e)) = 0
    calc
      _ = ∑ e ∈ fiber side u, v e * k u := by
        apply sum_congr rfl
        intro e he
        simp only [fiber, mem_filter, mem_univ, true_and] at he
        rw [he]
      _ = mass side v u * k u := by rw [mass, Finset.sum_mul]
      _ = 0 := by rw [hv u, zero_mul]
  have htotal : (∑ e, v e * k (side e)) = 0 := by
    rw [← mass_sum side (fun e => v e * k (side e))]
    simp only [hz, sum_const_zero]
  unfold pair
  change (∑ e, v e * (k (side e) - w e)) = _
  simp only [mul_sub, sum_sub_distrib, htotal, zero_sub]

/-- Every zero-incidence circulation has equal weights on the two edges of a
perfect transfer, at any time. The walk preserves the sum of coordinates, so
the global phase in the transfer is forced to be one. -/
theorem circulation_equal {left : E → L} {right : E → R} (hl : Surjective left) (hr : Surjective right)
    (v : E → ℂ) (hL : ∀ u, mass left v u=0) (hR : ∀ u, mass right v u=0)
    {a b : E} {k : ℕ} {z : ℂ} (hit : (walk left right)^[k] (delta a)=z • delta b) : v a=v b := by
  have total := sum_iterate (walk left right) (fun w => ∑ e, w e) (walk_sum hl hr) k (delta a)
  rw [hit] at total
  have one : z=1 := by simpa [delta] using total
  have pres (w : E → ℂ) : pair v (walk left right w)=pair v w := by
    rw [walk,pair_reflect_of_mass_zero left _ _ hL,pair_reflect_of_mass_zero right _ _ hR,neg_neg]
  have inv := sum_iterate (walk left right) (pair v) pres k (delta a)
  rw [hit,one,one_smul] at inv
  simpa [pair,delta] using inv.symm

private def incidence (left : E → L) (right : E → R) :
    (E → ℂ) →ₗ[ℂ] (L → ℂ) × (R → ℂ) where
  toFun v := (mass left v, mass right v)
  map_add' v w := by ext <;> simp [mass, sum_add_distrib]
  map_smul' z v := by ext <;> simp [mass, Finset.mul_sum]

private theorem incidence_injective {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    Injective (incidence left right) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hL (u : L) : mass left v u = 0 := congrFun (congrArg Prod.fst hv) u
  have hR (u : R) : mass right v u = 0 := congrFun (congrArg Prod.snd hv) u
  have pres (w : E → ℂ) : pair v (walk left right w) = pair v w := by
    rw [walk, pair_reflect_of_mass_zero left _ _ hL, pair_reflect_of_mass_zero right _ _ hR,
      neg_neg]
  have constant (a b : E) : v b = v a := by
    obtain ⟨k, _, hk⟩ := exact_pst hl hr h a b
    have eq := sum_iterate (walk left right) (pair v) pres k (delta a)
    rw [hk] at eq
    simpa [pair, delta] using eq
  ext a
  have hd : (degree left (left a) : ℂ) ≠ 0 := by
    exact_mod_cast (degree_pos left hl (left a)).ne'
  have z := hL (left a)
  unfold mass at z
  simp only [constant a, sum_const, nsmul_eq_mul] at z
  exact (mul_eq_zero.mp z).resolve_left hd

theorem edge_count_lt [Nonempty E] {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    Fintype.card E < Fintype.card L + Fintype.card R := by
  classical
  let f := incidence left right
  have proper : LinearMap.range f ≠ ⊤ := by
    intro hf
    have hsur := LinearMap.range_eq_top.mp hf
    let a : E := Classical.choice inferInstance
    obtain ⟨v, hv⟩ := hsur (delta (left a), (0 : R → ℂ))
    have hL := congrArg (fun t : (L → ℂ) × (R → ℂ) => ∑ u, t.1 u) hv
    have hR := congrArg (fun t : (L → ℂ) × (R → ℂ) => ∑ u, t.2 u) hv
    change (∑ u, mass left v u) = _ at hL
    change (∑ u, mass right v u) = _ at hR
    simp [mass_sum, delta] at hL hR
    exact one_ne_zero (hL.symm.trans hR)
  have hrank := Submodule.finrank_lt proper
  have hinj := incidence_injective hl hr h
  have heq := (LinearEquiv.ofInjective f hinj).finrank_eq
  simpa [← heq, Module.finrank_prod] using hrank

/-! A reflection reversing a periodic orbit fixes at most two points of it. -/

private theorem mirror_iterate {A : Type*} (d c : A → A)
    (h : ∀ x, d (c (d x)) = c x) (k : ℕ) (x : A) :
    d^[k] (c (d^[k] x)) = c x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      _ = d^[k] (d (c (d (d^[k] x)))) := by
        rw [iterate_succ_apply d k, iterate_succ_apply' d k x]
      _ = _ := by rw [h, ih]

private theorem at_most_two_marks {A W : Type*} [Fintype W] (d c : A → A) (m : W → A)
    (inject : Injective m) (mirror : ∀ x, d (c (d x)) = c x)
    (fixed : ∀ w, c (m w) = m w)
    (reach : ∀ i j, ∃ k : ℕ, 0 < k ∧ d^[k] (m i) = m j) : Fintype.card W ≤ 2 := by
  classical
  cases isEmpty_or_nonempty W with
  | inl h => simp
  | inr h =>
    let w₀ : W := Classical.choice h
    let x := m w₀
    let p := minimalPeriod d x
    obtain ⟨k, hk, hkx⟩ := reach w₀ w₀
    have hp : 0 < p := Function.IsPeriodicPt.minimalPeriod_pos hk hkx
    have hcover (w : W) : m w = x ∨ m w = d^[p / 2] x := by
      obtain ⟨t, _, ht⟩ := reach w₀ w
      let s := t % p
      have hs : s < p := Nat.mod_lt _ hp
      have hsw : d^[s] x = m w :=
        (iterate_mod_minimalPeriod_eq (f := d) (x := x) (n := t)).trans ht
      have hh := mirror_iterate d c mirror s x
      rw [hsw, fixed w, ← hsw, show c x = x from fixed w₀] at hh
      have hdiv : p ∣ s + s := Function.IsPeriodicPt.minimalPeriod_dvd
        (show IsPeriodicPt d (s + s) x by simpa [IsPeriodicPt, IsFixedPt, iterate_add_apply] using hh)
      obtain ⟨v, hv⟩ := hdiv
      have hv' : v < 2 := by
        by_contra! hle
        have := Nat.mul_le_mul_left p hle
        omega
      rcases (show v = 0 ∨ v = 1 by omega) with hv0 | hv1
      · left
        have hs0 : s = 0 := by simp [hv0] at hv; omega
        simpa [hs0] using hsw.symm
      · right
        have hsp : s = p / 2 := by simp [hv1] at hv; omega
        simpa [hsp] using hsw.symm
    let flag (w : W) : Bool := decide (m w = x)
    have inj : Injective flag := by
      intro a b hflag
      apply inject
      by_cases ha : m a = x
      · have hb : m b = x := by simpa [flag, ha] using hflag.symm
        exact ha.trans hb.symm
      · have hb : m b ≠ x := by simpa [flag, ha] using hflag.symm
        exact ((hcover a).resolve_left ha).trans ((hcover b).resolve_left hb).symm
    simpa using Fintype.card_le_of_injective flag inj

private abbrev ArcState (E : Type*) := (E → ℂ) ⊕ (E → ℂ)

private def halfStep (left : E → L) (right : E → R) : ArcState E → ArcState E
  | .inl v => .inr (reflect right v)
  | .inr v => .inl (reflect left v)

private def coin (left : E → L) (right : E → R) : ArcState E → ArcState E
  | .inl v => .inl (reflect right v)
  | .inr v => .inr (reflect left v)

private theorem half_mirror {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (a : ArcState E) :
    halfStep left right (coin left right (halfStep left right a)) = coin left right a := by
  cases a <;> simp [halfStep, coin, reflect_invol left hl _, reflect_invol right hr _]

private theorem half_injective {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) : Injective (halfStep left right) := by
  rintro (v | v) (w | w) hh <;> simp [halfStep] at hh ⊢
  · exact (reflect_invol right hr).injective hh
  · exact (reflect_invol left hl).injective hh

private theorem even_steps (left : E → L) (right : E → R) (k : ℕ) (v : E → ℂ) :
    (halfStep left right)^[2*k] (Sum.inl v) = Sum.inl ((walk left right)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*k), iterate_add_apply, ih,
      iterate_succ_apply' (walk left right) k]
    rfl

theorem mass_delta (side : E → V) (a : E) (u : V) :
    mass side (delta a) u = if side a = u then 1 else 0 := by
  simp [mass, delta, fiber]

private theorem reflect_delta_leaf (side : E → V) (a : E) (h : degree side (side a) = 1) :
    reflect side (delta a) = delta a := by
  have ha : a ∈ fiber side (side a) := by simp [fiber]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h
  have hab : a = b := by simpa [hb] using ha
  subst b
  ext e
  by_cases he : e = a
  · subst e
    simp [reflect, mass_delta, h, delta]
    norm_num
  · have hed : side a ≠ side e := by
      intro hv
      have hin : e ∈ fiber side (side a) := by simp [fiber, hv]
      exact he (by simpa [hb] using hin)
    simp [reflect, mass_delta, hed, delta, he]

private def combinedDegree (left : E → L) (right : E → R) : L ⊕ R → ℕ
  | .inl u => degree left u
  | .inr v => degree right v

private abbrev Leaf (left : E → L) (right : E → R) :=
  {u : L ⊕ R // combinedDegree left right u = 1}

private def incident {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) : L ⊕ R → E
  | .inl u => (hl u).choose
  | .inr v => (hr v).choose

private def mark {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (u : Leaf left right) : ArcState E :=
  match u.val with
  | .inl _ => .inr (delta (incident hl hr u.val))
  | .inr _ => .inl (delta (incident hl hr u.val))

private theorem mark_injective {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) : Injective (mark hl hr) := by
  rintro ⟨u | u, hu⟩ ⟨v | v, hv⟩ hh <;> simp [mark, incident] at hh ⊢
  · exact (hl u).choose_spec.symm.trans ((congrArg left (delta_injective hh)).trans (hl v).choose_spec)
  · exact (hr u).choose_spec.symm.trans ((congrArg right (delta_injective hh)).trans (hr v).choose_spec)

private theorem mark_fixed {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (u : Leaf left right) :
    coin left right (mark hl hr u) = mark hl hr u := by
  rcases u with ⟨u | v, hv⟩ <;> simp only [mark, incident, coin, Sum.inl.injEq, Sum.inr.injEq]
  · apply reflect_delta_leaf
    simpa [combinedDegree, (hl u).choose_spec] using hv
  · apply reflect_delta_leaf
    simpa [combinedDegree, (hr v).choose_spec] using hv

private theorem to_base {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (u : Leaf left right) :
    ∃ s : ℕ, s ≤ 1 ∧ (halfStep left right)^[s] (mark hl hr u) =
      Sum.inl (delta (incident hl hr u.val)) := by
  rcases u with ⟨u | v, hv⟩
  · refine ⟨1, le_rfl, ?_⟩
    simp only [mark, incident, iterate_one, halfStep, Sum.inl.injEq]
    apply reflect_delta_leaf
    simpa [combinedDegree, (hl u).choose_spec] using hv
  · exact ⟨0, by decide, rfl⟩

private theorem leaf_bound {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    Fintype.card (Leaf left right) ≤ 2 := by
  apply at_most_two_marks (halfStep left right) (coin left right) (mark hl hr)
    (mark_injective hl hr) (half_mirror hl hr) (mark_fixed hl hr)
  intro a b
  obtain ⟨s, hs, ha⟩ := to_base hl hr a
  obtain ⟨t, ht, hb⟩ := to_base hl hr b
  obtain ⟨k, hk, hu⟩ := exact_pst hl hr h (incident hl hr a.val) (incident hl hr b.val)
  have he := even_steps left right k (delta (incident hl hr a.val))
  rw [hu] at he
  let n := 2*k - t
  have hnk : t + n = 2*k := by dsimp [n]; omega
  refine ⟨n + s, by dsimp [n]; omega, ?_⟩
  rw [iterate_add_apply, ha]
  apply (half_injective hl hr).iterate t
  rw [← iterate_add_apply, hnk, he, hb]

/-- Universal edge transfer forces all endpoint blocks to have size at most two. -/
theorem degree_at_most_two [Nonempty E] {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    (∀ u, degree left u ≤ 2) ∧ (∀ u, degree right u ≤ 2) := by
  classical
  let d := combinedDegree left right
  have hd (w : L ⊕ R) : 0 < d w := by
    rcases w with u | v
    · exact degree_pos left hl u
    · exact degree_pos right hr v
  have hs : ∑ w, d w = 2 * Fintype.card E := by
    simp [d, Fintype.sum_sum_type, combinedDegree, sum_degree, two_mul]
  have hleaves : (∑ w : L ⊕ R, if d w = 1 then 1 else 0 : ℕ) ≤ 2 := by
    have hh := leaf_bound hl hr h
    rw [← Finset.card_filter (fun w : L ⊕ R => d w = 1) Finset.univ]
    simpa only [Leaf, Fintype.card_subtype] using hh
  have hc := edge_count_lt hl hr h
  have allDeg (w : L ⊕ R) : d w ≤ 2 := by
    by_contra! hw
    have strict : (∑ _ : L ⊕ R, (2 : ℕ)) <
        ∑ u : L ⊕ R, (d u + if d u = 1 then 1 else 0) := by
      apply Finset.sum_lt_sum
      · intro u _
        have := hd u
        split <;> omega
      · exact ⟨w, mem_univ _, by split <;> omega⟩
    rw [Finset.sum_add_distrib, hs] at strict
    simp only [Finset.sum_const, card_univ, Fintype.card_sum, nsmul_eq_mul] at strict
    change (Fintype.card L + Fintype.card R) * 2 <
      2 * Fintype.card E + ∑ u, (if d u = 1 then 1 else 0) at strict
    omega
  exact ⟨fun u => allDeg (.inl u), fun v => allDeg (.inr v)⟩

private theorem reflect_sends_delta (side : E → V) (hs : Surjective side)
    (degree_bound : ∀ u, degree side u ≤ 2) (a : E) : ∃ b : E, reflect side (delta a) = delta b := by
  by_cases ha : degree side (side a) = 1
  · exact ⟨a, reflect_delta_leaf side a ha⟩
  have ht : degree side (side a) = 2 := by
    have := degree_pos side hs (side a)
    have := degree_bound (side a)
    omega
  obtain ⟨b, c, hbc, hf⟩ := Finset.card_eq_two.mp ht
  have ha_mem : a ∈ fiber side (side a) := by simp [fiber]
  have choose_partner : ∃ b : E, a ≠ b ∧ fiber side (side a) = {a, b} := by
    rw [hf] at ha_mem
    rcases Finset.mem_insert.mp ha_mem with hab | hac
    · subst a
      exact ⟨c, hbc, hf⟩
    · have hac' : a = c := Finset.mem_singleton.mp hac
      subst a
      exact ⟨b, hbc.symm, by simpa [Finset.pair_comm] using hf⟩
  obtain ⟨p, hap, hf'⟩ := choose_partner
  have hp : side p = side a := by
    have : p ∈ fiber side (side a) := by simp [hf']
    simpa [fiber] using this
  refine ⟨p, ?_⟩
  funext e
  by_cases hea : e = a
  · subst e
    simp [reflect, mass_delta, ht, delta, hap]
  by_cases hep : e = p
  · subst e
    simp [reflect, mass_delta, ht, hp, delta, hap.symm]
  have hue : side a ≠ side e := by
    intro eq
    have hin : e ∈ fiber side (side a) := by simp [fiber, eq]
    simp [hf', hea, hep] at hin
  simp [reflect, mass_delta, hue, delta, hea, hep]

/-- The thesis question in coordinate form. One time step already sends each
standard edge basis vector to a standard edge basis vector by a permutation. -/
theorem universal_forces_permutation [Nonempty E] {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    ∃ π : Equiv.Perm E, ∀ a : E, walk left right (delta a) = delta (π a) := by
  classical
  obtain ⟨hL, hR⟩ := degree_at_most_two hl hr h
  have sends (a : E) : ∃ b : E, walk left right (delta a) = delta b := by
    obtain ⟨c, hc⟩ := reflect_sends_delta right hr hR a
    obtain ⟨b, hb⟩ := reflect_sends_delta left hl hL c
    exact ⟨b, by simp [walk, hc, hb]⟩
  choose f hf using sends
  have finj : Injective f := by
    intro a b hab
    have hh := (hf a).trans ((congrArg delta hab).trans (hf b).symm)
    exact delta_injective <| (reflect_invol right hr).injective <|
      (reflect_invol left hl).injective hh
  exact ⟨Equiv.ofBijective f ⟨finj, Finite.surjective_of_injective finj⟩, hf⟩

/-- The one-step permutation has a single orbit on the entire finite edge set,
including the one-edge case. The exponent may depend on the two edges. -/
theorem universal_forces_transitive_permutation [Nonempty E] {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right) (h : UniversalPST left right) :
    ∃ π : Equiv.Perm E, (∀ a : E, walk left right (delta a) = delta (π a)) ∧
      ∀ a b : E, ∃ k : ℕ, (π : E → E)^[k] a = b := by
  obtain ⟨π, hπ⟩ := universal_forces_permutation hl hr h
  have iter (k : ℕ) (a : E) :
      (walk left right)^[k] (delta a) = delta ((π : E → E)^[k] a) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [iterate_succ_apply', ih, hπ]
  refine ⟨π, hπ, fun a b => ?_⟩
  obtain ⟨k, _, hk⟩ := exact_pst hl hr h a b
  exact ⟨k, delta_injective ((iter k a).symm.trans hk)⟩

private theorem block_permutation (side : E → V) (hs : Surjective side)
    (hd : ∀ v, degree side v ≤ 2) :
    ∃ A : Equiv.Perm E, Involutive (A : E → E) ∧
      (∀ e, reflect side (delta e) = delta (A e)) ∧
      ∀ e f, side e = side f → e = f ∨ A e = f := by
  choose f hf using reflect_sends_delta side hs hd
  have hi : Involutive f := by
    intro a
    apply delta_injective
    rw [← hf (f a), ← hf a, reflect_invol side hs]
  let A : Equiv.Perm E := hi.toPerm f
  refine ⟨A, hi, hf, fun a b he => ?_⟩
  by_cases heq : a = b
  · exact Or.inl heq
  right
  by_contra hn
  change f a ≠ b at hn
  have h := congrFun (hf a) b
  have hdeg : (degree side (side b) : ℂ) ≠ 0 := by exact_mod_cast (degree_pos side hs _).ne'
  simp [reflect, mass_delta, he, delta, hn.symm, Ne.symm heq, hdeg] at h

private theorem product_orbit_closed (A B : Equiv.Perm E)
    (hA : Involutive (A : E → E)) (hB : Involutive (B : E → E)) (e : E)
    (leaf : A e = e ∨ B e = e) :
    (∀ a, (A*B).SameCycle e a → (A*B).SameCycle e (A a)) ∧
    (∀ a, (A*B).SameCycle e a → (A*B).SameCycle e (B a)) := by
  let P := A*B
  have hb : B⁻¹ = B := Function.Involutive.symm_eq_self_of_involutive B hB
  have aa : A*A = 1 := by ext a; exact hA a
  have mirror : A*P*A⁻¹ = P⁻¹ := by
    dsimp [P]
    rw [← mul_assoc A A B, aa, one_mul, mul_inv_rev, hb]
  have anchor : P.SameCycle e (A e) := by
    rcases leaf with h | h
    · rw [h]
    · have hP : P e = A e := by simp [P, Equiv.Perm.mul_apply, h]
      rw [← hP]
      exact Equiv.Perm.SameCycle.rfl.apply_right
  have leftClosed (a : E) (h : P.SameCycle e a) : P.SameCycle e (A a) := by
    have hh := h.conj (g := A)
    rw [mirror] at hh
    exact anchor.trans hh.of_inv
  refine ⟨leftClosed, fun a h => ?_⟩
  have hc := leftClosed (P a) h.apply_right
  rw [show A (P a) = B a from hA (B a)] at hc
  exact hc

section SimpleGraphs

open SimpleGraph
open scoped Classical

/-- The ordinary undirected simple graph of the bipartite incidence relation. -/
def incidenceGraph (left : E → L) (right : E → R) : SimpleGraph (L ⊕ R) where
  Adj a b := match a,b with
    | .inl x,.inr y | .inr y,.inl x => ∃ e, left e = x ∧ right e = y
    | _,_ => False
  symm := ⟨by rintro (x|x) (y|y) h <;> exact h⟩
  loopless := ⟨by rintro (x|x) h <;> exact h⟩

private theorem neighbor_left (left : E → L) (right : E → R) (v : L) :
    (incidenceGraph left right).neighborFinset (.inl v) =
      (univ.filter (fun e => left e = v)).image (fun e => Sum.inr (α := L) (right e)) := by
  classical
  ext w
  rw [mem_neighborFinset]
  cases w <;> simp [incidenceGraph]

private theorem neighbor_right (left : E → L) (right : E → R) (v : R) :
    (incidenceGraph left right).neighborFinset (.inr v) =
      (univ.filter (fun e => right e = v)).image (fun e => Sum.inl (β := R) (left e)) := by
  classical
  ext w
  rw [mem_neighborFinset]
  cases w <;> simp [incidenceGraph, and_comm]

theorem degree_graph_left (left : E → L) (right : E → R)
    (hs : Injective (fun a => (left a, right a))) (v : L) :
    (incidenceGraph left right).degree (.inl v) = (univ.filter (fun e => left e = v)).card := by
  classical
  rw [← card_neighborFinset_eq_degree, neighbor_left, card_image_iff]
  intro a ha b hb h
  apply hs
  have hal : left a = v := (mem_filter.mp ha).2
  have hbl : left b = v := (mem_filter.mp hb).2
  exact Prod.ext (hal.trans hbl.symm) (Sum.inr.inj h)

theorem degree_graph_right (left : E → L) (right : E → R)
    (hs : Injective (fun a => (left a, right a))) (v : R) :
    (incidenceGraph left right).degree (.inr v) = (univ.filter (fun e => right e = v)).card := by
  classical
  rw [← card_neighborFinset_eq_degree, neighbor_right, card_image_iff]
  intro a ha b hb h
  apply hs
  have har : right a = v := (mem_filter.mp ha).2
  have hbr : right b = v := (mem_filter.mp hb).2
  exact Prod.ext (Sum.inl.inj h) (har.trans hbr.symm)

theorem edges_graph (left : E → L) (right : E → R)
    (hs : Injective (fun a => (left a, right a))) :
    Nat.card (incidenceGraph left right).edgeSet = Fintype.card E := by
  classical
  let g := incidenceGraph left right
  let edge : E → Sym2 (L ⊕ R) := fun a => s(Sum.inl (left a), Sum.inr (right a))
  have image : g.edgeFinset = univ.image edge := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet]
      cases u <;> cases v <;> simp [edge, g, incidenceGraph]
  have hinj : Injective edge := by
    intro a b h
    apply hs
    simpa [edge, Sym2.eq_iff] using h
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, show (incidenceGraph left right).edgeFinset =
    univ.image edge from image, card_image_of_injective _ hinj, card_univ]

theorem pathGraph_degree_le_two {n : ℕ} (v : Fin n) : (pathGraph n).degree v ≤ 2 := by
  classical
  let f : (pathGraph n).neighborSet v → Bool := fun a => decide (v.val < a.val.val)
  have hf : Injective f := by
    intro a b hh
    have ha := pathGraph_adj.mp a.property
    have hb := pathGraph_adj.mp b.property
    apply Subtype.ext
    apply Fin.ext
    change decide (v.val < a.val.val) = decide (v.val < b.val.val) at hh
    by_cases h₁ : v.val < a.val.val <;> by_cases h₂ : v.val < b.val.val <;>
      simp [h₁, h₂] at hh <;> omega
  simpa only [card_neighborSet_eq_degree, Fintype.card_bool] using Fintype.card_le_of_injective f hf

theorem finite_tree_of_degree_le_two_is_path {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hT : G.IsTree) (hd : ∀ v, G.degree v ≤ 2) :
    ∃ n : ℕ, Nonempty (G ≃g pathGraph n) := by
  classical
  let : Nonempty V := hT.connected.nonempty
  obtain ⟨s, t, p, hp, longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have closed (u v : V) (hu : u ∈ p.support) (hadj : G.Adj u v) : v ∈ p.support := by
    by_contra hv
    obtain ⟨k, hk, hkl⟩ := Walk.mem_support_iff_exists_getVert.mp hu
    subst u
    by_cases hk0 : k = 0
    · subst k
      have hstart : G.Adj v s := by simpa using hadj.symm
      have hlong := longest v t (p.cons hstart) ((Walk.cons_isPath_iff hstart p).mpr ⟨hp, hv⟩)
      simp at hlong
    by_cases hkL : k = p.length
    · subst k
      have hend : G.Adj t v := by simpa using hadj
      have hlong := longest s v (p.concat hend) (hp.concat hv hend)
      simp at hlong
    have hklt : k < p.length := by omega
    let a := p.getVert (k-1)
    let b := p.getVert (k+1)
    have ha : G.Adj (p.getVert k) a := by
      have eq : k-1+1=k := by omega
      simpa only [a, eq] using (p.adj_getVert_succ (i := k-1) (by omega)).symm
    have hb : G.Adj (p.getVert k) b := p.adj_getVert_succ hklt
    have hab : a ≠ b := by
      intro eq
      have q := hp.getVert_injOn (by change k-1 ≤ p.length; omega)
        (by change k+1 ≤ p.length; omega) eq
      omega
    have hav : a ≠ v := fun e => hv (e ▸ p.getVert_mem_support (k-1))
    have hbv : b ≠ v := fun e => hv (e ▸ p.getVert_mem_support (k+1))
    have sub : ({a, b, v} : Finset V) ⊆ G.neighborFinset (p.getVert k) := by
      intro x hx
      rw [mem_insert, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa only [mem_neighborFinset] using (by assumption)
    have hthree := Finset.card_le_card sub
    have hdeg := hd (p.getVert k)
    simp [hab, hav, hbv] at hthree
    omega
  have walkClosed {u v : V} (q : G.Walk u v) (hu : u ∈ p.support) : v ∈ p.support := by
    induction q with
    | nil => exact hu
    | cons h q ih => exact ih (closed _ _ hu h)
  have span : p.toSubgraph.IsSpanning := by
    intro w
    exact p.mem_verts_toSubgraph.mpr <| walkClosed (hT.connected s w).some p.start_mem_support
  let e := p.toSubgraph.spanningCoeEquivCoeOfSpanning span
  have hconn : p.toSubgraph.spanningCoe.Connected := e.connected_iff.mpr p.toSubgraph_connected
  have eq : p.toSubgraph.spanningCoe = G := le_antisymm p.toSubgraph.spanningCoe_le
    ((isTree_iff_minimal_connected.mp hT).2 hconn p.toSubgraph.spanningCoe_le)
  refine ⟨p.length+1, ?_⟩
  exact (congrArg (fun H : SimpleGraph V => Nonempty (H ≃g pathGraph (p.length + 1))) eq).mp
    ⟨e.trans hp.pathGraphIsoToSubgraph.symm⟩

private theorem every_edge_in_cycle {left : E → L} {right : E → R}
    (hc : (incidenceGraph left right).Connected) (P : Equiv.Perm E) (s : E)
    (lc : ∀ a b, P.SameCycle s a → left a = left b → P.SameCycle s b)
    (rc : ∀ a b, P.SameCycle s a → right a = right b → P.SameCycle s b) :
    ∀ a, P.SameCycle s a := by
  let marked : L ⊕ R → Prop
    | .inl x => ∃ e, P.SameCycle s e ∧ left e = x
    | .inr y => ∃ e, P.SameCycle s e ∧ right e = y
  have cross (u v : L ⊕ R) (h : (incidenceGraph left right).Adj u v) : marked u → marked v := by
    rcases u with u | u <;> rcases v with v | v
    · exact h.elim
    · obtain ⟨e, hx, hy⟩ := h
      rintro ⟨a, ha, hl⟩
      exact ⟨e, lc a e ha (hl.trans hx.symm), hy⟩
    · obtain ⟨e, hx, hy⟩ := h
      rintro ⟨a, ha, hr⟩
      exact ⟨e, rc a e ha (hr.trans hy.symm), hx⟩
    · exact h.elim
  have through {u v} (w : (incidenceGraph left right).Walk u v) (hu : marked u) : marked v := by
    induction w with
    | nil => exact hu
    | cons h _ ih => exact ih (cross _ _ h hu)
  intro a
  have base : marked (.inl (left s)) := ⟨s, Equiv.Perm.SameCycle.rfl, rfl⟩
  obtain ⟨b, hb, he⟩ := through (hc (.inl (left s)) (.inl (left a))).some base
  exact lc b a hb he

/-- On ordinary finite connected simple bipartite graphs, universal transfer is
equivalent to a graph isomorphism with a path. The simplicity hypothesis says
that the two endpoints determine each edge. -/
theorem universal_iff_path [Nonempty E] {left : E → L} {right : E → R}
    (hl : Surjective left) (hr : Surjective right)
    (hs : Injective (fun e => (left e, right e))) (hc : (incidenceGraph left right).Connected) :
    UniversalPST left right ↔ ∃ n : ℕ, Nonempty (incidenceGraph left right ≃g pathGraph n) := by
  classical
  let G := incidenceGraph left right
  have gl (u : L) : G.degree (.inl u) = degree left u := degree_graph_left left right hs u
  have gr (v : R) : G.degree (.inr v) = degree right v := degree_graph_right left right hs v
  constructor
  · intro h
    have edgeEq := edges_graph left right hs
    have bound := edge_count_lt hl hr h
    have ec := hc.card_vert_le_card_edgeSet_add_one
    have count : Nat.card (L ⊕ R) = Fintype.card L + Fintype.card R := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sum]
    rw [count, edgeEq] at ec
    have hT : G.IsTree := isTree_iff_connected_and_card.mpr
      ⟨hc, by simpa only [G, edgeEq, count] using (show Fintype.card E + 1 =
        Fintype.card L + Fintype.card R from by omega)⟩
    obtain ⟨ld, rd⟩ := degree_at_most_two hl hr h
    apply finite_tree_of_degree_le_two_is_path hT
    rintro (v | v)
    · rw [gl]
      exact ld v
    · rw [gr]
      exact rd v
  · rintro ⟨n, ⟨iso⟩⟩
    let init : E := Classical.choice inferInstance
    let : Nontrivial (L ⊕ R) := ⟨.inl (left init), .inr (right init), Sum.inl_ne_inr⟩
    have hn : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 (iso (.inl (left init)))
    have hT : G.IsTree := iso.isTree_iff.mpr (isTree_pathGraph.mpr hn)
    have degrees (u : L ⊕ R) : G.degree u ≤ 2 :=
      (iso.degree_eq u) ▸ pathGraph_degree_le_two (iso u)
    have ld (u : L) : degree left u ≤ 2 := gl u ▸ degrees (.inl u)
    have rd (v : R) : degree right v ≤ 2 := gr v ▸ degrees (.inr v)
    obtain ⟨A, hA, rA, fibersA⟩ := block_permutation left hl ld
    obtain ⟨B, hB, rB, fibersB⟩ := block_permutation right hr rd
    obtain ⟨u, hu⟩ := hT.exists_vert_degree_one_of_nontrivial
    have fixed : ∃ s : E, A s = s ∨ B s = s := by
      rcases u with u | u
      · obtain ⟨s, rfl⟩ := hl u
        exact ⟨s, Or.inl (delta_injective ((rA s).symm.trans
          (reflect_delta_leaf left s ((gl _).symm.trans hu))))⟩
      · obtain ⟨s, rfl⟩ := hr u
        exact ⟨s, Or.inr (delta_injective ((rB s).symm.trans
          (reflect_delta_leaf right s ((gr _).symm.trans hu))))⟩
    obtain ⟨s, leaf⟩ := fixed
    obtain ⟨closeA, closeB⟩ := product_orbit_closed A B hA hB s leaf
    let P := A*B
    have all (x : E) : P.SameCycle s x := by
      apply every_edge_in_cycle hc P s _ _ x
      · intro a b ha he
        rcases fibersA a b he with rfl | hab
        · exact ha
        · rw [← hab]
          exact closeA a ha
      · intro a b ha he
        rcases fibersB a b he with rfl | hab
        · exact ha
        · rw [← hab]
          exact closeB a ha
    have step (a : E) : walk left right (delta a) = delta (P a) := by
      rw [walk, rB, rA]
      rfl
    have iter (k : ℕ) (a : E) : (walk left right)^[k] (delta a) = delta ((P ^ k) a) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterate_succ_apply', ih, step, pow_succ']
        rfl
    intro a b
    obtain ⟨k, hk⟩ := ((all a).symm.trans (all b)).exists_nat_pow_eq
    exact ⟨k, 1, by simp, by simpa [hk] using iter k a⟩

end SimpleGraphs

#print axioms universal_forces_permutation
#print axioms universal_forces_transitive_permutation
#print axioms universal_iff_path

end
end BipartiteEdgeWalk
