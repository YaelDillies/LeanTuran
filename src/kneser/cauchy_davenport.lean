/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.additive.e_transform
import mathlib.algebra.group.defs
import mathlib.group_theory.min_order
import kneser.mathlib

/-!
# The Cauchy-Davenport theorem

This file proves a generalisation of the Cauchy-Davenport theorem to arbitrary groups.

## Main declarations

* `finset.min_le_card_mul`: A generalisation of the Cauchy-Davenport theorem to arbitrary groups.
* `monoid.is_torsion_free.card_add_card_sub_one_le_card_mul`: The Cauchy-Davenport theorem in
  torsion-free groups.
* `zmod.min_le_card_add`: The Cauchy-Davenport theorem.
* `finset.card_add_card_sub_one_le_card_mul`: The Cauchy-Davenport theorem in linear ordered
  cancellative semigroups.

## References

* Matt DeVos, *On a generalization of the Cauchy-Davenport theorem*

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

open finset function monoid mul_opposite order_dual subgroup
open_locale pointwise

variables {α : Type*}

/-! ### General case -/

section general
variables [group α] [decidable_eq α] {x y : finset α × finset α} {s t : finset α}

/-- The relation we induct along in the proof of Cauchy-Davenport theorem. `(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ * t₁| < |s₂ * t₂|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`. -/
@[to_additive "The relation we induct along in the proof of Cauchy-Davenport theorem.
`(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ + t₁| < |s₂ + t₂|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`."]
private def devos_mul_rel : finset α × finset α → finset α × finset α → Prop :=
prod.lex (<) (prod.lex (>) (<)) on λ x, ((x.1 * x.2).card, x.1.card + x.2.card, x.1.card)

@[to_additive]
lemma devos_mul_rel_iff :
  devos_mul_rel x y ↔ (x.1 * x.2).card < (y.1 * y.2).card ∨
    (x.1 * x.2).card = (y.1 * y.2).card ∧ y.1.card + y.2.card < x.1.card + x.2.card ∨
      (x.1 * x.2).card = (y.1 * y.2).card ∧ x.1.card + x.2.card = y.1.card + y.2.card ∧
        x.1.card < y.1.card :=
by simp [devos_mul_rel, prod.lex_iff, and_or_distrib_left]

@[to_additive] lemma devos_mul_rel_of_le (hmul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
  (hadd : y.1.card + y.2.card < x.1.card + x.2.card) :
  devos_mul_rel x y :=
devos_mul_rel_iff.2 $ hmul.lt_or_eq.imp_right $ λ h, or.inl ⟨h, hadd⟩

@[to_additive] lemma devos_mul_rel_of_le_of_le (hmul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
  (hadd : y.1.card + y.2.card ≤ x.1.card + x.2.card) (hone : x.1.card < y.1.card) :
  devos_mul_rel x y :=
devos_mul_rel_iff.2 $ hmul.lt_or_eq.imp_right $ λ h, hadd.gt_or_eq.imp (and.intro h) $
  λ h', ⟨h, h', hone⟩

@[to_additive]
lemma well_founded_on_devos_mul_rel :
  {x : finset α × finset α | x.1.nonempty ∧ x.2.nonempty}.well_founded_on
    (devos_mul_rel : finset α × finset α → finset α × finset α → Prop) :=
begin
  refine is_well_founded.wf.on_fun.well_founded_on.prod_lex_of_well_founded_on_fiber
    (λ n, set.well_founded_on.prod_lex_of_well_founded_on_fiber _ $
      λ n, is_well_founded.wf.on_fun.well_founded_on),
  exact is_well_founded.wf.on_fun.well_founded_on.mono' (λ x hx y hy, tsub_lt_tsub_left_of_le $
    add_le_add ((card_le_card_mul_right _ hx.1.2).trans_eq hx.2) $
      (card_le_card_mul_left _ hx.1.1).trans_eq hx.2),
end

/-- A generalisation of the **Cauchy-Davenport Theorem** to arbitrary groups. -/
@[to_additive "A generalisation of the **Cauchy-Davenport Theorem** to arbitrary groups."]
lemma finset.min_le_card_mul (hs : s.nonempty) (ht : t.nonempty) :
  min (min_order α) ↑(s.card + t.card - 1) ≤ (s * t).card :=
begin
  -- Set up the induction on `x := (s, t)` along the `devos_mul_rel` relation.
  set x := (s, t) with hx,
  clear_value x,
  simp only [prod.ext_iff] at hx,
  obtain ⟨rfl, rfl⟩ := hx,
  refine well_founded_on_devos_mul_rel.induction ⟨hs, ht⟩ _,
  clear_dependent x,
  rintro ⟨s, t⟩ ⟨hs, ht⟩ ih,
  simp only [min_le_iff, tsub_le_iff_right, prod.forall, set.mem_set_of_eq, and_imp,
    nat.cast_le] at *,
  -- If `t.card < s.card`, we're done by the induction hypothesis on `(t⁻¹, s⁻¹)`.
  obtain hts | hst := lt_or_le t.card s.card,
  { simpa [←mul_inv_rev, add_comm] using ih _ _ ht.inv hs.inv
      (devos_mul_rel_iff.2 $ or.inr $ or.inr $ by simpa [←mul_inv_rev, add_comm]) },
  -- If `s` is a singleton, then the result is trivial.
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  { simp [add_comm] },
  -- Else, we have `a, b ∈ s` distinct. So `g := b⁻¹ * a` is a non-identity element such that `s`
  -- intersects its right translate by `g`.
  obtain ⟨g, hg, hgs⟩ : ∃ g : α, g ≠ 1 ∧ (s ∩ op g • s).nonempty :=
    ⟨b⁻¹ * a, inv_mul_eq_one.not.2 hab.symm, _,
      mem_inter.2 ⟨ha, mem_smul_finset.2 ⟨_, hb, by simp⟩⟩⟩,
  -- If `s` is equal to its right translate by `g`, then it contains a nontrivial subgroup, namely
  -- the subgroup generated by `g`. So `s * t` has size at least the size of a nontrivial subgroup,
  -- as wanted.
  obtain hsg | hsg := eq_or_ne (op g • s) s,
  { have hS : (zpowers g : set α) ⊆ a⁻¹ • s,
    { refine forall_mem_zpowers.2 (@zpow_induction_right _ _ _ (∈ a⁻¹ • (s : set α))
        ⟨_, ha, inv_mul_self _⟩ (λ c hc, _) $ λ c hc, _),
      { rw [←hsg, coe_smul_finset, smul_comm],
        exact set.smul_mem_smul_set hc },
      { simp only,
        rwa [←op_smul_eq_mul, op_inv, ←set.mem_smul_set_iff_inv_smul_mem, smul_comm,
          ←coe_smul_finset, hsg] } },
    exact or.inl ((min_order_le_nat_card (zpowers_ne_bot.2 hg) $
      s.finite_to_set.smul_set.subset hS).trans $ with_top.coe_le_coe.2 $
      ((nat.card_mono s.finite_to_set.smul_set hS).trans_eq $ by simp).trans $
      card_le_card_mul_right _ ht) },
  -- Else, we can transform `s`, `t` to `s'`, `t'` and `s''`, `t''`, such that `(s', t')` and
  -- `(s'', t'')` are both strictly smaller than `(s, t)` according to `devos_mul_rel`.
  replace hsg : (s ∩ op g • s).card < s.card := card_lt_card ⟨inter_subset_left _ _, λ h, hsg $
    eq_of_superset_of_card_ge (h.trans $ inter_subset_right _ _) (card_smul_finset _ _).le⟩,
  replace aux1 := card_mono (mul_e_transform_left.fst_mul_snd_subset g (s, t)),
  replace aux2 := card_mono (mul_e_transform_right.fst_mul_snd_subset g (s, t)),
  -- If the left translate of `t` by `g⁻¹` is disjoint from `t`, then we're easily done.
  obtain hgt | hgt := disjoint_or_nonempty_inter t (g⁻¹ • t),
  { rw ←card_smul_finset g⁻¹ t,
    refine or.inr ((add_le_add_right hst _).trans _),
    rw ←card_union_eq hgt,
    exact (card_le_card_mul_left _ hgs).trans (le_add_of_le_left aux1) },
  -- Else, we're done by induction on either `(s', t')` or `(s'', t'')` depending on whether
  -- `|s| + |t| ≤ |s'| + |t'|` or `|s| + |t| < |s''| + |t''|`. One of those two inequalities must
  -- hold since `2 * (|s| + |t|) = |s'| + |t'| + |s''| + |t''|`.
  obtain hstg | hstg := le_or_lt_of_add_le_add (mul_e_transform.card g (s, t)).ge,
  { exact (ih _ _ hgs (hgt.mono inter_subset_union) $ devos_mul_rel_of_le_of_le
      aux1 hstg hsg).imp (with_top.coe_le_coe.2 aux1).trans'
      (λ h, hstg.trans $ h.trans $ add_le_add_right aux1 _) },
  { exact (ih _ _ (hgs.mono inter_subset_union) hgt $ devos_mul_rel_of_le aux2 hstg).imp
      (with_top.coe_le_coe.2 aux2).trans' (λ h, hstg.le.trans $ h.trans $ add_le_add_right aux2 _) }
end

/-- The **Cauchy-Davenport Theorem** for torsion-free groups. -/
@[to_additive "The **Cauchy-Davenport Theorem** for torsion-free groups."]
lemma monoid.is_torsion_free.card_add_card_sub_one_le_card_mul (h : is_torsion_free α)
  {s t : finset α} (hs : s.nonempty) (ht : t.nonempty) :
  s.card + t.card - 1 ≤ (s * t).card :=
by simpa only [h.min_order, min_eq_right, le_top, nat.cast_le] using finset.min_le_card_mul hs ht

end general

/-! ### $$ℤ/nℤ$$ -/

/-- The **Cauchy-Davenport Theorem**. -/
lemma zmod.min_le_card_add {p : ℕ} (hp : p.prime) {s t : finset (zmod p)} (hs : s.nonempty)
  (ht : t.nonempty) : min p (s.card + t.card - 1) ≤ (s + t).card :=
by simpa only [zmod.min_order_of_prime hp, min_le_iff, nat.cast_le]
  using finset.min_le_card_add hs ht

/-! ### Linearly ordered cancellative semigroups -/

/-- The **Cauchy-Davenport Theorem** for linearly ordered cancellative semigroups. -/
@[to_additive "The **Cauchy-Davenport Theorem** for linearly ordered additive cancellative
semigroups."]
lemma finset.card_add_card_sub_one_le_card_mul [linear_order α] [cancel_semigroup α]
  [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)] {s t : finset α}
  (hs : s.nonempty) (ht : t.nonempty) :
  s.card + t.card - 1 ≤ (s * t).card :=
begin
  suffices : (s * {t.min' ht}) ∩ ({s.max' hs} * t) = {s.max' hs * t.min' ht},
  { rw [←card_singleton_mul t (s.max' hs), ←card_mul_singleton s (t.min' ht),
    ←card_union_add_card_inter, ←card_singleton _, ←this, nat.add_sub_cancel],
    exact card_mono (union_subset (mul_subset_mul_left $ singleton_subset_iff.2 $
      min'_mem _ _) $ mul_subset_mul_right $ singleton_subset_iff.2 $ max'_mem _ _) },
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨mul_mem_mul (max'_mem _ _) $
    mem_singleton_self _, mul_mem_mul (mem_singleton_self _) $ min'_mem _ _⟩, _⟩,
  simp only [mem_inter, and_imp, mem_mul, mem_singleton, exists_and_distrib_left, exists_eq_left,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mul_left_inj],
  exact λ a' ha' b' hb' h, (le_max' _ _ ha').eq_of_not_lt
    (λ ha, ((mul_lt_mul_right' ha _).trans_eq' h).not_le $mul_le_mul_left' (min'_le _ _ hb') _),
end
