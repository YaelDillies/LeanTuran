import combinatorics.simple_graph.basic
import mathlib.algebra.indicator_function

open finset nat
open_locale big_operators

namespace simple_graph
variables {α : Type*} [fintype α] [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj]
  {s t : finset α} {a : α}

/-- Number of vertices of `s` adjacent to `a`. -/
def deg_on (s : finset α) (a : α) : ℕ := (s ∩ G.neighbor_finset a).card

lemma deg_on_mono (hst : s ⊆ t) (a : α) : G.deg_on s a ≤ G.deg_on t a :=
card_mono $ inter_subset_inter_right hst

@[simp] lemma deg_on_empty (a : α) : G.deg_on ∅ a = 0 := by simp [deg_on]

@[simp] lemma deg_on_univ (a : α) : G.deg_on univ a = G.degree a :=
by rw [deg_on, degree, univ_inter]

-- if s and t are disjoint then for any vertex a the deg_on add
lemma deg_on_union (h : disjoint s t) (a) : G.deg_on (s ∪ t) a = G.deg_on s a + G.deg_on t a :=
begin
  unfold deg_on,
  rw [←card_disjoint_union, ←inter_distrib_right],
  exact h.mono (inter_subset_left _ _) (inter_subset_left _ _),
end

-- edges from t to s\t equals edges from s\t to t
lemma sum_deg_on_comm (s t : finset α) : ∑ a in s, G.deg_on t a = ∑ a in t, G.deg_on s a :=
begin
  simp_rw [deg_on, card_eq_sum_ones, sum_inter_eq_sum_indicator],
  rw sum_comm,
  simp [set.indicator_apply, adj_comm],
end

end simple_graph
