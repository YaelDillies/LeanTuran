import combinatorics.simple_graph.clique
import mathlib.combinatorics.simple_graph.basic

open finset nat

namespace simple_graph
variables {α : Type*}  {G H : simple_graph α} {m n : ℕ}

-- main new def below "G.is_close H s" if by deleting at most s edges from G we obtain a subgraph of H
-- G.is_close s H iff there exists a finset of at most s edges such that G-S is a subgraph of H
def is_close (G H : simple_graph α) (n : ℕ) : Prop :=
∃ s : finset (sym2 α), G.delete_edges s ≤ H ∧ s.card ≤ n

lemma is_close_refl (G : simple_graph α) (n : ℕ) : G.is_close G n :=
⟨∅, delete_edges_le _ _, zero_le _⟩

lemma is_close_rfl : G.is_close G n := is_close_refl _ _

lemma is_close.mono (h : m ≤ n) : G.is_close H m → G.is_close H n :=
Exists.imp $ λ s, and.imp_right h.trans'

lemma is_close_trivial [fintype G.edge_set] (H :simple_graph α) (h : G.edge_finset.card ≤ n) :
  G.is_close H n :=
⟨G.edge_finset, by simp, h⟩

end simple_graph
