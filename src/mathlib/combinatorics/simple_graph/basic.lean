import combinatorics.simple_graph.basic

/-!
I found dealing with the mathlib "induced" subgraph too painful (probably just too early in my
experience of lean)
-/

open set

variables {α β : Type*} {G H : simple_graph α} {s t : set α} {a b : α}

namespace simple_graph

@[simp] lemma disjoint_edge_finset [fintype G.edge_set] [fintype H.edge_set] :
  disjoint G.edge_finset H.edge_finset ↔ disjoint G H :=
by simp_rw [←finset.disjoint_coe, coe_edge_finset, disjoint_edge_set]

@[simp] lemma nonempty_edge_set : G.edge_set.nonempty ↔ G ≠ ⊥ :=
by rw [set.nonempty_iff_ne_empty, edge_set_eq_empty.ne]

@[simp] lemma edge_finset_eq_empty [fintype G.edge_set] : G.edge_finset = ∅ ↔ G = ⊥ :=
by rwa [←edge_finset_bot, edge_finset_inj]

@[simp] lemma nonempty_edge_finset [fintype G.edge_set] : G.edge_finset.nonempty ↔ G ≠ ⊥ :=
by rw [finset.nonempty_iff_ne_empty, edge_finset_eq_empty.ne]

@[simp] lemma delete_edges_edge_set (G H : simple_graph α) : G.delete_edges H.edge_set = G \ H :=
rfl

section ind

/-- Graph induced by s:finset α, defined to be a simple_graph α (so all vertices outside s have
empty neighborhoods). this is equivalent to  "spanning_coe (induce (s:set α) G)" as we prove below.
-/
def ind (G : simple_graph α) (s : set α) : simple_graph α :=
{ adj := λ a b, G.adj a b ∧ a ∈ s ∧ b ∈ s }

@[simp] lemma adj_ind : (G.ind s).adj a b ↔ G.adj a b ∧ a ∈ s ∧ b ∈ s := iff.rfl

@[simp] lemma ind_empty (G : simple_graph α) : G.ind ∅ = ⊥ := by ext; simp
@[simp] lemma ind_univ (G : simple_graph α) : G.ind univ = G := by ext; simp
@[simp] lemma ind_singleton (G : simple_graph α) (a : α) : G.ind {a} = ⊥ :=
by ext; simp; rintro h rfl; exact h.ne'
@[simp] lemma ind_inter (G : simple_graph α) (s t : set α) : G.ind (s ∩ t) = G.ind s ⊓ G.ind t :=
by ext; simp; tauto

@[simp] lemma spanning_coe_induce (G : simple_graph α) (s : set α) :
  spanning_coe (induce (s : set α) G) = G.ind s :=
by ext; simp [←and_assoc]; simp_rw [and_assoc, ←and_rotate]

/-- Induced subgraphs on disjoint sets meet in the empty graph. -/
lemma disjoint_ind (h : disjoint s t) : disjoint (G.ind s) (G.ind t) :=
by rw [disjoint_iff, ←ind_inter, disjoint_iff_inter_eq_empty.1 h, ind_empty]

end ind
end simple_graph
