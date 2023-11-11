/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.image
import data.fintype.pi
import data.list.rdrop
import field_theory.chevalley_warning

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * n - 1` elements of `zmod n`, we can find `n`
elements of sum zero.

## Main declarations

* `zmod.exists_submultiset_eq_zero`: The Erdős–Ginzburg–Ziv theorem
-/

section
variables {α : Type*} [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
  [contravariant_class α α (+) (≤)]

lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b :=
by rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end

section
variables {α : Type*} [canonically_ordered_comm_semiring α] [has_sub α] [has_ordered_sub α]
  [is_total α (≤)] [contravariant_class α α (+) (≤)]

lemma mul_tsub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end

namespace list
variables {α : Type*} {l l' l₀ l₁ l₂ : list α} {a b : α} {m n : ℕ}

lemma cons_sublist_cons_iff' : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ :=
begin
  split,
  { rintro (_ | _),
    { exact or.inl ‹_› },
    { exact or.inr ⟨rfl, ‹_›⟩ } },
  { rintro (h | ⟨rfl, h⟩),
    { exact sublist_cons_of_sublist _ h },
    { rwa cons_sublist_cons_iff } }
end

attribute [simp] nil_subperm

lemma subperm_cons_self : l <+~ a :: l := ⟨l, perm.refl _, sublist_cons _ _⟩

@[simp] lemma subperm_nil : l <+~ [] ↔ l = [] :=
⟨λ h, length_eq_zero.1 $ le_bot_iff.1 h.length_le, by { rintro rfl, refl }⟩

lemma rtake_suffix (n : ℕ) (l : list α) : l.rtake n <:+ l := drop_suffix _ _

lemma length_rtake (n : ℕ) (l : list α) : (l.rtake n).length = min n l.length :=
(length_drop _ _).trans $ by rw [tsub_tsub_eq_min, min_comm]

@[simp] lemma take_reverse (n : ℕ) (l : list α) : l.reverse.take n = (l.rtake n).reverse :=
by rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_reverse (n : ℕ) (l : list α) : l.reverse.rtake n = (l.take n).reverse :=
by rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_rtake (n m) (l : list α) : (l.rtake m).rtake n = l.rtake (min n m) :=
by rw [rtake_eq_reverse_take_reverse, ←take_reverse, take_take, rtake_eq_reverse_take_reverse]

@[simp] lemma rdrop_append_rtake (n : ℕ) (l : list α) : l.rdrop n ++ l.rtake n = l :=
take_append_drop _ _

lemma suffix_iff_eq_rtake : l₁ <:+ l₂ ↔ l₁ = l₂.rtake (length l₁) :=
⟨λ h, append_left_cancel $
  (suffix_iff_eq_append.1 h).trans (rdrop_append_rtake _ _).symm,
 λ e, e.symm ▸ rtake_suffix _ _⟩

alias prefix_iff_eq_take ↔ is_prefix.eq_take _
alias suffix_iff_eq_rtake ↔ is_suffix.eq_rtake _

lemma exists_prefix_length_eq (hn : n ≤ l.length) : ∃ l', l' <+: l ∧ l'.length = n :=
⟨l.take n, take_prefix _ _, (length_take _ _).trans $ min_eq_left hn⟩

lemma exists_suffix_length_eq (hn : n ≤ l.length) : ∃ l', l' <:+ l ∧ l'.length = n :=
⟨l.rtake n, rtake_suffix _ _, (length_rtake _ _).trans $ min_eq_left hn⟩

lemma exists_sublist_length_eq (hn : n ≤ l.length) : ∃ l', l' <+ l ∧ l'.length = n :=
⟨l.take n, take_sublist _ _, (length_take _ _).trans $ min_eq_left hn⟩

end list

namespace multiset
variables {α : Type*} [decidable_eq α] {s t : multiset α} {n : ℕ}

lemma le_card_sub : s.card - t.card ≤ (s - t).card :=
tsub_le_iff_left.2 $ (card_mono le_add_tsub).trans_eq $ card_add _ _

end multiset

namespace nat

lemma prime_composite_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
  (prime : ∀ p : ℕ, p.prime → P p) (composite : ∀ a, 2 ≤ a → P a → ∀ b, 2 ≤ b → P b → P (a * b))
  (n : ℕ) : P n :=
begin
  refine induction_on_primes zero one _ _,
  rintro p (_ | _ | a) hp ha,
  { rwa mul_zero },
  { rw mul_one,
    exact prime _ hp },
  { exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha }
end

end nat

namespace subtype
variables {α : Type*} {p : α → Prop} {a b : {a // p a}}

lemma coe_ne_coe : (a : α) ≠ b ↔ a ≠ b := coe_inj.not

end subtype

namespace multiset
variables {α : Type*} {s : multiset α}

--TODO: Rename `multiset.coe_attach` to `multiset.attach_coe`
--TODO: Rename `multiset.coe_countp` to `multiset.countp_coe`

--TODO: Maybe change `multiset.attach` to make `multiset.coe_attach` refl?

end multiset

namespace nat
variables {a b : ℕ}

lemma eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b :=
begin
  obtain ⟨_ | _ | c, rfl⟩ := hdvd,
  { simpa using ha },
  { exact mul_one _ },
  { cases hlt.not_le ((mul_comm _ _).trans_le $ mul_le_mul_left' (one_lt_succ_succ _) _) }
end

end nat

namespace zmod
variables {p : ℕ} [fact (nat.prime p)]

lemma pow_card_sub_one (x : zmod p) : x ^ (p - 1) = if x ≠ 0 then 1 else 0 :=
begin
  split_ifs with hx,
  { exact pow_card_sub_one_eq_one hx },
  { simp [of_not_not hx, (fact.out p.prime).one_lt] }
end

end zmod

open finset mv_polynomial
open_locale big_operators

namespace zmod
variables {ι : Type*} {n p : ℕ} {s : finset ι} {f : ι → zmod p}

/-- The first multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₁ (p : ℕ) (s : finset ι) : mv_polynomial s (zmod p) := ∑ i, X i ^ (p - 1)

/-- The second multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₂ (f : ι → zmod p) (s : finset ι) : mv_polynomial s (zmod p) :=
∑ i : s, f i • X i ^ (p - 1)

variables {ι} [fact p.prime]

lemma total_degree_f₁_add_total_degree_f₂ :
  (f₁ p s).total_degree + (f₂ f s).total_degree < 2 * p - 1 :=
begin
  refine (add_le_add (total_degree_finset_sum _ _) $
    (total_degree_finset_sum _ _).trans $ finset.sup_mono_fun _).trans_lt _,
  swap,
  exact λ a ha, total_degree_smul_le _ _,
  simp only [total_degree_X_pow, ←two_mul],
  refine (mul_le_mul_left' finset.sup_const_le _).trans_lt _,
  rw [mul_tsub, mul_one],
  exact tsub_lt_tsub_left_of_le
    ((fact.out p.prime).two_le.trans $ le_mul_of_one_le_left' one_le_two) one_lt_two,
end

/-- The prime case of the **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * p - 1`
elements of `zmod p` contain `p` elements whose sum is zero. -/
private lemma aux (hs : s.card = 2 * p - 1) (f : ι → zmod p) :
  ∃ t ⊆ s, t.card = p ∧ ∑ i in t, f i = 0 :=
begin
  classical,
  haveI : ne_zero p := infer_instance,
  -- Let `N` be the number of common roots of our polynomials `f₁` and `f₂` (`f s ff` and `f s tt`).
  set N := fintype.card {x // eval x (f₁ p s) = 0 ∧ eval x (f₂ f s) = 0}
    with hN,
  -- Zero is a common root to `f₁` and `f₂`, so `N` is nonzero
  let zero_sol : {x // eval x (f₁ p s) = 0 ∧ eval x (f₂ f s) = 0} :=
    ⟨0, by simp [f₁, f₂, map_sum, (fact.out p.prime).one_lt]⟩,
  have hN₀ : 0 < N := @fintype.card_pos _ _ ⟨zero_sol⟩,
  have hs' : 2 * p - 1 = fintype.card s := by simp [hs],
  -- Chevalley-Warning gives us that `p ∣ n` because the total degrees of `f₁` and `f₂` are at most
  -- `p - 1`, and we have `2 * p - 1 > 2 * (p - 1)` variables.
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p
    (total_degree_f₁_add_total_degree_f₂.trans_eq hs'),
  -- Hence, `2 ≤ p ≤ N` and we can make a common root `x ≠ 0`.
  obtain ⟨x, hx⟩ := fintype.exists_ne_of_one_lt_card ((fact.out p.prime).one_lt.trans_le $
    nat.le_of_dvd hN₀ hpN) zero_sol,
  -- This common root gives us the required submultiset, namely the `a ∈ s` such that `x a ≠ 0`.
  refine ⟨(s.attach.filter $ λ a, x.1 a ≠ 0).map ⟨coe, subtype.coe_injective⟩, _, _, _⟩,
  sorry { simp [subset_iff],
    exact λ x hx _, hx },
  -- From `f₁ x = 0`, we get that `p` divides the number of `a` such that `x a ≠ 0`.
  {
    simp only [card_map, ←finset.filter_val, finset.card_val, function.comp_app, ←finset.map_val],
    refine nat.eq_of_dvd_of_lt_two_mul (finset.card_pos.2 _).ne' _
      ((finset.card_filter_le _ _).trans_lt _),
    -- This number is nonzero because `x ≠ 0`.
    sorry{ rw [←subtype.coe_ne_coe, function.ne_iff] at hx,
      exact hx.imp (λ a ha, mem_filter.2 ⟨finset.mem_attach _ _, ha⟩) },
    sorry{ rw [←char_p.cast_eq_zero_iff (zmod p), ←finset.sum_boole],
      simpa only [f₁, map_sum, zmod.pow_card_sub_one, map_pow, eval_X] using x.2.1 },
    -- And it is at most `2 * p - 1`, so it must be `p`.
    sorry{ rw [finset.card_attach, card_to_enum_finset, hs],
     exact tsub_lt_self (mul_pos zero_lt_two (fact.out p.prime).pos) zero_lt_one } },
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  sorry{ simpa only [f₂, map_sum, zmod.pow_card_sub_one, finset.sum_map_val, finset.sum_filter, smul_eval,
      map_pow, eval_X, mul_ite, mul_zero, mul_one] using x.2.2 }
end

--TODO: Rename `multiset.pairwise_nil` to `multiset.pairwise_zero`

/-- The **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * n - 1` elements of
`zmod n` contain `n` elements whose sum is zero. -/
lemma exists_subset_sum_eq_zero (f : ι → zmod n) (hs : 2 * n - 1 ≤ s.card) :
  ∃ t ≤ s, t.card = n ∧ ∑ i in t, f i = 0 :=
begin
  induction n using nat.prime_composite_induction with p hp,
  case zero { exact ⟨∅, empty_subset _, card_empty, sum_empty⟩ },
  case one { obtain ⟨t, ht, hn⟩ := exists_smaller_set _ _ hs, exact ⟨t, ht, hn, subsingleton.elim _ _⟩ },
  case prime : p hp
  { haveI := fact.mk hp,
    obtain ⟨t, hts, ht⟩ := exists_smaller_set _ _ hs,
    obtain ⟨u, hut, hu⟩ := aux ht f,
    exact ⟨u, hut.trans hts, hu⟩ },
  case composite : a ha iha b hb ihb
  { suffices : ∀ n ≤ 2 * b - 1, ∃ m : multiset (multiset $ zmod $ a * b), m.card = n ∧
      m.pairwise _root_.disjoint ∧ ∀ ⦃u : multiset $ zmod $ a * b⦄, u ∈ m →
        u.card = 2 * a + 1 ∧ u.sum ∈ add_subgroup.zmultiples (a : zmod $ a * b),
    {
      obtain ⟨m, hm⟩ := this _ le_rfl,
      sorry,
    },
    rintro n hn,
    induction n with n ih,
    { exact ⟨0, by simp⟩ },
    obtain ⟨m, hm⟩ := ih (nat.le_of_succ_le hn),
    -- have : 2 * a - 1 ≤ ((s - m.sum).map $ cast_hom (dvd_mul_right _ _) $ zmod a).card,
    -- { rw card_map,
    --   refine (le_tsub_of_add_le_left $ le_trans _ hs).trans le_card_sub,
    --   have : m.map multiset.card = repeat (2 * a - 1) n,
    --   {
    --     sorry
    --   },
    --   rw [map_multiset_sum, this, sum_repeat, ←le_tsub_iff_right, tsub_tsub_tsub_cancel_right,
    --     ←mul_tsub, ←mul_tsub_one],
    --   sorry,
    --   sorry,
    --   sorry,
    -- },
    sorry,
  }
end

end zmod
