import set_theory.cardinal.finite
import mathlib.set_theory.cardinal.basic

open cardinal

namespace nat
variable {α : Type*}

@[simp] lemma card_eq_zero : nat.card α = 0 ↔ is_empty α ∨ infinite α :=
by simp [nat.card, mk_eq_zero_iff, aleph_0_le_mk_iff]

lemma card_ne_zero : nat.card α ≠ 0 ↔ nonempty α ∧ finite α := by simp [not_or_distrib]

lemma card_pos_iff : 0 < nat.card α ↔ nonempty α ∧ finite α :=
by simp [nat.card, mk_eq_zero_iff, mk_lt_aleph_0_iff]

@[simp] lemma card_pos [nonempty α] [finite α] : 0 < nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

-- TODO: Golf proof
-- lemma finite_of_card_ne_zero (h : nat.card α ≠ 0) : finite α := (card_ne_zero.1 h).2

lemma card_mono {s t : set α} (ht : t.finite) (h : s ⊆ t) : nat.card s ≤ nat.card t :=
to_nat_le_of_le_of_lt_aleph_0 ht.lt_aleph_0 $ mk_le_mk_of_subset h

end nat

namespace set
variables {α : Type*} {s : set α}

lemma infinite.card_eq_zero (hs : s.infinite) : nat.card s = 0 :=
@nat.card_eq_zero_of_infinite _ hs.to_subtype

end set
