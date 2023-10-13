import data.finset.slice

variable {α : Type*}

namespace set

lemma sized_empty (r : ℕ) : (∅ : set (finset α)).sized r := λ s hs, hs.elim

end set
