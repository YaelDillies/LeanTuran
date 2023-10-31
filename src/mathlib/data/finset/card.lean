import data.finset.card

namespace finset
variables {α : Type*} {s : finset α} {a : α}

@[simp] lemma one_le_card : 1 ≤ s.card ↔ s.nonempty := card_pos

end finset
