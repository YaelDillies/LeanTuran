import mathlib.set_theory.cardinal.finite
import data.zmod.quotient

open function set subgroup submonoid

variables {α : Type*}

section left_cancel_monoid
variables [left_cancel_monoid α] {a : α}

-- @[simp, to_additive finite_multiples] lemma finite_powers :
--   (powers a : set α).finite ↔ is_of_fin_order a :=
-- ⟨λ h, of_not_not $ λ h', infinite_range_of_injective (injective_pow_iff_not_is_of_fin_order.2 h')
--   h, is_of_fin_order.finite_powers⟩

-- @[simp, to_additive infinite_zmultiples] lemma infinite_powers :
--   (powers a : set α).infinite ↔ ¬ is_of_fin_order a :=
-- finite_powers.not

end left_cancel_monoid

section group
variables [group α] {s : subgroup α} (a : α)

/-- See also `order_eq_card_zpowers`. -/
@[simp, to_additive nat.card_zmultiples "See also `add_order_eq_card_zmultiples`."]
lemma nat.card_zpowers : nat.card (zpowers a) = order_of a :=
begin
  have := nat.card_congr (mul_action.orbit_zpowers_equiv a (1 : α)),
  rwa [nat.card_zmod, orbit_subgroup_one_eq_self] at this,
end

variables {a}

@[simp, to_additive finite_zmultiples] lemma finite_zpowers :
  (zpowers a : set α).finite ↔ is_of_fin_order a :=
by simp [←order_of_pos_iff, ←nat.card_zpowers, nat.card_pos, ←set_like.coe_sort_coe,
  set.nonempty_of_nonempty_subtype, nat.card_pos_iff, set.finite_coe_iff]

@[simp, to_additive infinite_zmultiples] lemma infinite_zpowers :
  (zpowers a : set α).infinite ↔ ¬ is_of_fin_order a :=
finite_zpowers.not

alias finite_zpowers ↔ _ is_of_fin_order.finite_zpowers'

attribute [to_additive is_of_fin_add_order.finite_zmultiples'] is_of_fin_order.finite_zpowers'
attribute [protected] is_of_fin_add_order.finite_zmultiples' is_of_fin_order.finite_zpowers'

@[to_additive add_order_of_le_card]
lemma order_of_le_card (hs : (s : set α).finite) (ha : a ∈ s) : order_of a ≤ nat.card s :=
by { rw ←nat.card_zpowers, exact nat.card_mono hs (zpowers_le.2 ha) }

end group
