import data.set.finite

namespace set
variables {α : Type*} [infinite α] {s : set α}

lemma finite.exists_not_mem (hs : s.finite) : ∃ a, a ∉ s :=
by { by_contra' h, exact infinite_univ (hs.subset $ λ a _, h _) }

end set

namespace finset
variables {α : Type*} [infinite α]

lemma exists_not_mem (s : finset α) : ∃ a, a ∉ s := s.finite_to_set.exists_not_mem

lemma exists_card : ∀ n : ℕ, ∃ s : finset α, s.card = n
| 0 := ⟨∅, card_empty⟩
| (n + 1) := begin
  classical,
  obtain ⟨s, rfl⟩ := exists_card n,
  obtain ⟨a, ha⟩ := s.exists_not_mem,
  exact ⟨insert a s, card_insert_of_not_mem ha⟩,
end

end finset
