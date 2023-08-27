import combinatorics.simple_graph.clique

open finset

namespace simple_graph
variables {α : Type*} {G H : simple_graph α} {s : set α} {t : finset α} {a b : α} {m n : ℕ}

@[simp] lemma edge_set_eq_empty : G.edge_set = ∅ ↔ G = ⊥ := by rw [←edge_set_inj, edge_set_bot]

@[simp] lemma not_mem_neighbor_set_self : a ∉ G.neighbor_set a :=
(mem_neighbor_set _ _ _).not.2 $ G.loopless _

@[simp] lemma is_clique_empty (G : simple_graph α) : G.is_clique ∅ := set.pairwise_empty _
@[simp] lemma is_clique_singleton (G : simple_graph α) (a : α) : G.is_clique {a} :=
set.pairwise_singleton _ _

@[simp] lemma is_clique_insert :
  G.is_clique (insert a s) ↔ G.is_clique s ∧ ∀ b ∈ s, a ≠ b → G.adj a b :=
set.pairwise_insert_of_symmetric G.symm

@[simp] lemma is_clique_insert_of_not_mem (ha : a ∉ s) :
  G.is_clique (insert a s) ↔ G.is_clique s ∧ ∀ b ∈ s, G.adj a b :=
set.pairwise_insert_of_symmetric_of_not_mem G.symm ha

@[simp] lemma is_clique_pair : G.is_clique {a, b} ↔ a ≠ b → G.adj a b :=
set.pairwise_pair_of_symmetric G.symm

lemma is_clique.insert (hs : G.is_clique s) (h : ∀ b ∈ s, a ≠ b → G.adj a b) :
  G.is_clique (insert a s) :=
hs.insert_of_symmetric G.symm h

@[simp] lemma is_n_clique_empty : G.is_n_clique n ∅ ↔ n = 0 := by simp [is_n_clique_iff, eq_comm]
@[simp] lemma is_n_clique_singleton : G.is_n_clique n {a} ↔ n = 1 :=
by simp [is_n_clique_iff, eq_comm]

lemma is_n_clique.insert [decidable_eq α] {s : finset α} (hs : G.is_n_clique n s)
  (h : ∀ b ∈ s, G.adj a b) : G.is_n_clique (n + 1) (insert a s) :=
begin
  split,
  { push_cast,
    exact hs.1.insert (λ b hb _, h _ hb) },
  { rw [card_insert_of_not_mem (λ ha, (h _ ha).ne rfl), hs.2] }
end

@[simp] lemma clique_free_two : G.clique_free 2 ↔ G = ⊥ :=
begin
  classical,
  split,
  { simp_rw [←edge_set_eq_empty, set.eq_empty_iff_forall_not_mem, sym2.forall, mem_edge_set],
    exact λ h a b hab, h _ ⟨by simpa [hab.ne], card_doubleton hab.ne⟩ },
  { rintro rfl,
    exact clique_free_bot le_rfl }
end

/-- `G.clique_free_on s n` means that `G` has no `n`-cliques contained in `s`. -/
def clique_free_on (G : simple_graph α) (s : set α) (n : ℕ) : Prop :=
∀ ⦃t⦄, ↑t ⊆ s → ¬G.is_n_clique n t

lemma clique_free_on.subset (hst : s ⊆ t) (ht : G.clique_free_on t n) : G.clique_free_on s n :=
λ u hus, ht $ hus.trans hst

lemma clique_free_on.mono (hmn : m ≤ n) (hG : G.clique_free_on s m) : G.clique_free_on s n :=
begin
  rintro t hts ht,
  obtain ⟨u, hut, hu⟩ := t.exists_smaller_set _ (hmn.trans ht.card_eq.ge),
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.clique.subset hut, hu⟩,
end

lemma clique_free_on.anti (hGH : G ≤ H) (hH : H.clique_free_on s n) : G.clique_free_on s n :=
λ t hts ht, hH hts $ ht.mono hGH

@[simp] lemma clique_free_on_empty : G.clique_free_on ∅ n ↔ n ≠ 0 :=
by simp [clique_free_on, set.subset_empty_iff]

@[simp] lemma clique_free_on_singleton : G.clique_free_on {a} n ↔ 1 < n :=
by obtain _ | _ | n := n; simp [clique_free_on, set.subset_singleton_iff_eq]

@[simp] lemma clique_free_on_univ : G.clique_free_on set.univ n ↔ G.clique_free n :=
by simp [clique_free, clique_free_on]

protected lemma clique_free.clique_free_on (hG : G.clique_free n) : G.clique_free_on s n :=
λ t _, hG _

lemma clique_free_on_of_card_lt {s : finset α} (h : s.card < n) : G.clique_free_on s n :=
λ t hts ht, h.not_le $ ht.2.symm.trans_le $ card_mono hts

--TOOD: Restate using `simple_graph.indep_set` once we have it
@[simp] lemma clique_free_on_two : G.clique_free_on s 2 ↔ s.pairwise G.adjᶜ :=
begin
  classical,
  refine ⟨λ h a ha b hb _ hab, h _ ⟨by simpa [hab.ne], card_doubleton hab.ne⟩, _⟩,
  { push_cast,
    exact set.insert_subset.2 ⟨ha, set.singleton_subset_iff.2 hb⟩ },
  simp only [clique_free_on, is_n_clique_iff, card_eq_two, coe_subset, not_and, not_exists],
  rintro h t hst ht a b hab rfl,
  simp only [coe_insert, coe_singleton, set.insert_subset, set.singleton_subset_iff] at hst,
  refine h hst.1 hst.2 hab (ht _ _ hab); simp,
end

lemma clique_free_on.of_succ (hs : G.clique_free_on s (n + 1)) (ha : a ∈ s) :
  G.clique_free_on (s ∩ G.neighbor_set a) n :=
begin
  classical,
  refine λ t hts ht, hs _ (ht.insert $ λ b hb, (hts hb).2),
  push_cast,
  exact set.insert_subset.2 ⟨ha, hts.trans $ set.inter_subset_left _ _⟩,
end

end simple_graph
