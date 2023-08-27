import combinatorics.simple_graph.basic
import mathlib.order.partition.finpartition

open finset

namespace finpartition
variables {α : Type*} [fintype α] [decidable_eq α] {P : finpartition (univ : finset α)}
  {s t : finset α} {a b : α}

@[simps]
def multipartite_graph (P : finpartition (univ : finset α)) : simple_graph α :=
{ adj := λ a b, ∀ ⦃s⦄, s ∈ P.parts → a ∈ s → b ∉ s,
  symm := λ a b hab, by simpa only [imp_not_comm] using hab,
  loopless := λ a ha, by obtain ⟨s, hs, has⟩ := P.exists_mem (mem_univ a); exact ha hs has has }

instance : decidable_rel (multipartite_graph P).adj := λ a b, finset.decidable_dforall_finset

--if v and w are in distinct parts then they are adjacent
lemma multipartite_graph_adj_of_mem_parts (hs : s ∈ P.parts) (ht : t ∈ P.parts)
  (ha : a ∈ s) (hb : b ∈ t) : (multipartite_graph P).adj a b ↔ s ≠ t :=
begin
  refine ⟨_, λ hst u hu hau hbu, hst _⟩,
  { rintro hab rfl,
    exact hab hs ha hb },
  { rw [P.eq_of_mem_parts hs hu ha hau, P.eq_of_mem_parts ht hu hb hbu] }
end

end finpartition
