import order.partition.finpartition

open finset

namespace finpartition
variables {α : Type*} [decidable_eq α] {s t u : finset α} (P : finpartition s) {a : α}

lemma eq_of_mem_parts (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hat : a ∈ t) (hau : a ∈ u) : t = u :=
P.disjoint.elim ht hu $ not_disjoint_iff.2 ⟨a, hat, hau⟩

end finpartition
