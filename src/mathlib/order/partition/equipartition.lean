import order.partition.equipartition
import mathlib.data.set.equitable

namespace finpartition
variables {α : Type*} [decidable_eq α] {s : finset α} {P : finpartition s}

@[simp] lemma not_is_equipartition :
  ¬ P.is_equipartition ↔ ∃ (a ∈ P.parts) (b ∈ P.parts), finset.card b + 1 < finset.card a :=
set.not_equitable_on

end finpartition
