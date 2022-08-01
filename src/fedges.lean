import data.nat.basic
import tactic.core
import data.finset.basic
import combinatorics.simple_graph.basic
import misc_finset

open finset nat 
namespace simple_graph

-- extremal graph theory studies finite graphs and we do a lot of counting so I naively thought I should 
-- prove some lemmas about (sub)graphs and edge_finsets..

-- main new def below "G.is_far H s" if by deleting at most s edges from G we obtain a subgraph of H 

section fedges
variables {t n : ℕ} 
variables {α : Type*} [fintype α][inhabited α][decidable_eq α]
{G H : simple_graph α}[decidable_rel G.adj][decidable_rel H.adj]
--include G H

-- G is a subgraph of H iff G.edge_finset is subset of H.edge_finset
lemma subgraph_edge_subset : G ≤ H ↔ G.edge_finset ⊆ H.edge_finset:=
begin
  split,{ intro gh, intros e he, obtain ⟨x,y⟩:=e, simp only [mem_edge_finset] at *, exact gh he},
  { intro gh,intros x y h, have :⟦(x,y)⟧∈ G.edge_set:=h, rw [← mem_edge_finset] at this, 
  have:= gh this, rwa mem_edge_finset at this,},
end
-- graphs (on same vertex set) are equal iff edge_finsets are equal
lemma eq_iff_edges_eq   : G=H ↔ G.edge_finset = H.edge_finset:= 
begin
  split, {intro eq, exact subset_antisymm (subgraph_edge_subset.mp (le_of_eq eq)) (subgraph_edge_subset.mp (le_of_eq eq.symm))},
  {intro eq, exact le_antisymm (subgraph_edge_subset.mpr (subset_of_eq eq)) (subgraph_edge_subset.mpr (subset_of_eq eq.symm))},  
end

-- a subgraph of the same size or larger is the same graph (... everything is finite)
lemma edge_eq_sub_imp_eq (hs: G≤ H) (hc: H.edge_finset.card ≤ G.edge_finset.card): G = H
:=eq_iff_edges_eq.mpr  (finset.eq_of_subset_of_card_le (subgraph_edge_subset.mp hs) hc)


-- the empty graph has no edges
lemma empty_has_no_edges :(⊥ : simple_graph α).edge_finset =∅:=
begin
  ext, obtain ⟨x,y⟩:=a, rw mem_edge_finset, simp only [not_mem_empty, iff_false],
  intro h, assumption,
end

-- a graph is the empty graph iff it has no edges
lemma empty_iff_edge_empty {G :simple_graph α} [decidable_rel G.adj] : G = ⊥  ↔ G.edge_finset=∅
:= by rwa [eq_iff_edges_eq, empty_has_no_edges]

-- meet of two graphs has edges given by intersection
lemma meet_edges_eq {G H :simple_graph α} [decidable_rel G.adj][decidable_rel H.adj] : (G⊓H).edge_finset =G.edge_finset ∩ H.edge_finset:=
begin
  ext,simp only [mem_edge_finset, mem_inter], induction a,{refl},{refl},
end

-- edge sets are disjoint iff meet is empty graph
lemma disjoint_edges_iff_meet_empty {G H :simple_graph α} [decidable_rel G.adj][decidable_rel H.adj] : disjoint G.edge_finset H.edge_finset ↔  G ⊓ H = ⊥:= 
begin
  rw [empty_iff_edge_empty, meet_edges_eq], exact disjoint_iff,
end

-- the subgraph formed by deleting edges (from edge_finset)
@[ext]
def del_fedges (G:simple_graph α) (S: finset (sym2 α))[decidable_rel G.adj]  :simple_graph α :={
adj:= G.adj \ sym2.to_rel S,
symm := λ a b, by simp [adj_comm, sym2.eq_swap] }

--deleting all the edges in H from G is G\H
lemma del_fedges_is_sdiff  (G H:simple_graph α) (S: finset (sym2 α))[decidable_rel G.adj][decidable_rel H.adj] :
 G.del_fedges H.edge_finset =G\H:=
begin
  ext,simp only [del_fedges, sdiff_adj, set.coe_to_finset, pi.sdiff_apply, sym2.to_rel_prop, mem_edge_set],
  refl,
end


-- now introduce a simple version of distance between graphs 

-- G.is_far s H iff there exists a finset of at most s edges such that G-S is a subgraph of H

def is_far (G H :simple_graph α) (s : ℕ) [decidable_rel G.adj][decidable_rel H.adj] 
:= ∃S:finset (sym2 α), ((G.del_fedges S) ≤ H) ∧ (S.card ≤ s)


lemma is_far_le (G H :simple_graph α) {s t : ℕ} (h:s≤t) [decidable_rel G.adj][decidable_rel H.adj]: 
G.is_far H s → G.is_far H t:=
begin
  intro h1, obtain ⟨S,hS1,hS2⟩:=h1,exact ⟨S,hS1,le_trans hS2 h⟩,
end

lemma is_far_trivial (G H :simple_graph α) (s : ℕ) [decidable_rel G.adj][decidable_rel H.adj]:
(G.edge_finset.card ≤ s) → G.is_far H s:=
begin
  intro h,  refine ⟨G.edge_finset,_,h⟩, rw del_fedges_is_sdiff, simp only [_root_.sdiff_self, bot_le],
  exact G.edge_finset,
end



-- if G is not the empty graph it contains an edge
lemma ne_bot_imp_edge : ¬G = ⊥ →  ∃e, e ∈ G.edge_set :=
begin
  rw empty_iff_edge_empty,rw eq_empty_iff_forall_not_mem ,push_neg, 
  simp only [mem_edge_finset, forall_exists_index], tauto,
end

end fedges


end simple_graph