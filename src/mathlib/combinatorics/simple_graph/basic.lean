import combinatorics.simple_graph.basic
import data.fun_like.fintype
import mathlib.logic.basic

variables {α β : Type*} {G H : simple_graph α} {s : set (sym2 α)}

namespace simple_graph

instance [subsingleton α] : unique (simple_graph α) :=
{ default := ⊥,
  uniq := λ G, by { ext a b, simp [subsingleton.elim a b]  } }

instance [nontrivial α] : nontrivial (simple_graph α) :=
⟨⟨⊥, ⊤, λ h, not_subsingleton α ⟨by simpa [ext_iff,function.funext_iff] using h⟩⟩⟩

@[simp] lemma disjoint_edge_set : disjoint G.edge_set H.edge_set ↔ disjoint G H :=
by rw [set.disjoint_iff, disjoint_iff_inf_le, ←edge_set_inf, ←edge_set_bot, ←set.le_iff_subset,
  order_embedding.le_iff_le]

@[simp] lemma disjoint_edge_finset [fintype G.edge_set] [fintype H.edge_set] :
  disjoint G.edge_finset H.edge_finset ↔ disjoint G H :=
by simp_rw [←finset.disjoint_coe, coe_edge_finset, disjoint_edge_set]

@[simp] lemma edge_set_eq_empty : G.edge_set = ∅ ↔ G = ⊥ := by rwa [←edge_set_bot, edge_set_inj]

@[simp] lemma nonempty_edge_set : G.edge_set.nonempty ↔ G ≠ ⊥ :=
by rw [set.nonempty_iff_ne_empty, edge_set_eq_empty.ne]

@[simp] lemma edge_finset_eq_empty [fintype G.edge_set] : G.edge_finset = ∅ ↔ G = ⊥ :=
by rwa [←edge_finset_bot, edge_finset_inj]

@[simp] lemma nonempty_edge_finset [fintype G.edge_set] : G.edge_finset.nonempty ↔ G ≠ ⊥ :=
by rw [finset.nonempty_iff_ne_empty, edge_finset_eq_empty.ne]

@[simp] lemma disjoint_from_edge_set : disjoint G (from_edge_set s) ↔ disjoint G.edge_set s :=
begin
  conv_rhs { rw ←set.diff_union_inter s {e : sym2 α | e.is_diag} },
  rw [←disjoint_edge_set, edge_set_from_edge_set, set.disjoint_union_right, and_iff_left],
  exact set.disjoint_left.2 (λ e he he', not_is_diag_of_mem_edge_set _ he he'.2),
end

@[simp] lemma from_edge_set_disjoint : disjoint (from_edge_set s) G ↔ disjoint s G.edge_set :=
by rw [disjoint.comm, disjoint_from_edge_set, disjoint.comm]

@[simp] lemma delete_edges_eq : G.delete_edges s = G ↔ disjoint G.edge_set s :=
by rw [delete_edges_eq_sdiff_from_edge_set, sdiff_eq_left, disjoint_from_edge_set]

@[simp] lemma delete_edges_edge_set (G H : simple_graph α) : G.delete_edges H.edge_set = G \ H :=
rfl

namespace hom

@[simp, norm_cast] lemma coe_id : ⇑(id : G →g G) = _root_.id := rfl

instance [subsingleton (α → β)] {H : simple_graph β} : subsingleton (G →g H) :=
fun_like.coe_injective.subsingleton

instance [is_empty α] {H : simple_graph β} : unique (G →g H) :=
{ default := ⟨is_empty_elim, is_empty_elim⟩,
  uniq := λ _, subsingleton.elim _ _ }

noncomputable instance [fintype α] [fintype β] {H : simple_graph β} : fintype (G →g H) :=
by classical; exact fun_like.fintype _

instance [finite α] [finite β] {H : simple_graph β} : finite (G →g H) := fun_like.finite _

end hom

/-- The graph homomorphism from a smaller graph to a bigger one. -/
def hom_of_le (h : G ≤ H) : G →g H := ⟨id, h⟩

@[simp, norm_cast] lemma coe_hom_of_le (h : G ≤ H) : ⇑(hom_of_le h) = id := rfl

namespace embedding

attribute [simp] map_adj_iff

@[simp] lemma coe_to_hom {H : simple_graph β} (f : G ↪g H) : ⇑f.to_hom = f := rfl

end embedding
end simple_graph
