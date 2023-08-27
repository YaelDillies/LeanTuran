import data.set.equitable

namespace set
variables {α β : Type*} [linear_order β] [has_add β] [has_one β] {s : set α} {f : α → β}

@[simp] lemma not_equitable_on : ¬ s.equitable_on f ↔ ∃ (a ∈ s) (b ∈ s), f b + 1 < f a :=
by simp [equitable_on]

end set
