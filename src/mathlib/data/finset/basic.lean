import data.finset.basic

variables {α : Type*} [decidable_eq α] {s t : finset α} {a : α}

namespace finset

alias attach_nonempty_iff ↔ _ nonempty.attach
attribute [protected] nonempty.attach

lemma insert_comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
coe_injective $ by { push_cast, exact set.insert_comm _ _ _ }

lemma disjoint_insert_erase (ha : a ∉ t) : disjoint (s.erase a) (insert a t) ↔ disjoint s t :=
by rw [disjoint_erase_comm, erase_insert ha]

lemma disjoint_erase_insert (ha : a ∉ s) : disjoint (insert a s) (t.erase a) ↔ disjoint s t :=
by rw [←disjoint_erase_comm, erase_insert ha]

end finset
