import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators
--local
import nbhd_res


open finset nat 
open_locale big_operators 

namespace simple_graph

section clique_free_sets
variables {t n : ℕ} 
variables {α : Type*} (G : simple_graph α) [fintype α][nonempty α]{s : finset α}[decidable_eq α][decidable_rel G.adj]


-- restricted nbhd is the part of nbhd in A
include G
-- we will need the concept of a clique-free set of vertices in a graph rather than just clique-free graphs
-- A is a t-clique-free set of vertices in G
def clique_free_set (A : finset α) (s : ℕ): Prop:= ∀ B ⊆ A, ¬G.is_n_clique s B

--clique-free if too small
lemma clique_free_card_lt {A : finset α} {s: ℕ} (h: A.card <s): G.clique_free_set A s:=
begin
  rw clique_free_set,intros B hB,rw is_n_clique_iff,push_neg,intro h1,
  exact ne_of_lt (lt_of_le_of_lt (card_le_of_subset hB) h), 
end

--clique-free of empty (unless s=0)
lemma clique_free_empty {s : ℕ} (h: 0< s): G.clique_free_set ∅ s:=
begin
  have:=finset.card_empty, rw ← this at h, exact G.clique_free_card_lt h,
end

-- if G has no s-clique then nor does the univ 
lemma clique_free_graph_imp_set {s : ℕ} (h: G.clique_free s) :  G.clique_free_set univ s:=
begin
  revert h, contrapose,
  rw clique_free_set,push_neg,intro h, rw clique_free, push_neg,
  obtain ⟨B,h1,h2⟩:=h,  exact ⟨B,h2⟩,
end

-- base case for Erdos/Furedi proof:
-- if A has no 2-clique then restricted degrees are all zero 
-- i.e. A is an independent set

lemma two_clique_free {A: finset α} (hA : G.clique_free_set A 2) :  ∀v∈A, G.deg_res v A =0 :=
begin
  intros v hv, rw [deg_res,card_eq_zero], 
  contrapose hA,
  obtain ⟨w,hw⟩:=exists_mem_nempty G hA,
  cases hw with h1 h2, 
  have ne: v≠w := adj.ne h2,
  have c2 :card {v,w} =2:=card_doubleton ne,
  have :G.is_n_clique 2 {v,w},{
    rw [is_n_clique_iff, coe_insert, coe_singleton, is_clique_iff,set.pairwise_pair_of_symmetric],
    exact ⟨λh,h2,c2⟩,exact G.symm,},
  rw clique_free_set, push_neg,
  refine ⟨{v,w},_,this⟩, intros x hx,
  simp only [mem_insert, mem_singleton] at *,cases hx,{ rw hx,exact hv},{rw hx, exact h1},
end

-- sum of deg_res over an independent set (2-clique-free set) is 0
-- e (G.ind A)=0
lemma two_clique_free_sum {A: finset α} (hA : G.clique_free_set A 2) : ∑ v in A, G.deg_res v A = 0
:=sum_eq_zero (G.two_clique_free hA)


-- if A set is (t+2)-clique-free then any member vertex 
-- has restricted nbhd that is (t+1)-clique-free 
-- (just prove for any simple_graph α if  G is (t+2)-clique free then so is any nbhd of a vertex in G
-- then can apply it to G.ind A etc...
lemma t_clique_free {A: finset α} {v :α}(hA : G.clique_free_set A (t + 2)) (hv : v ∈ A) :
G.clique_free_set (G.nbhd_res v A) (t + 1):=
begin
  rw clique_free_set at *, 
  intros B hB, contrapose! hA,
  set C:= B ∪ {v} with hC,
  refine ⟨C,_,_⟩,{
  rw hC, apply union_subset (subset_trans hB (G.sub_res_nbhd_A v A)) _,
  simp only [hv, singleton_subset_iff]},
  rw is_n_clique_iff at *,
  refine ⟨_,_⟩,{
  rcases hA with ⟨cl,ca⟩, 
  rw [is_clique_iff, set.pairwise],
  intros x hx y hy hne,
  by_cases x=v,
    have yB : y∈ G.neighbor_finset v,{ 
      simp only [*, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, 
      mem_coe, eq_self_iff_true, true_or, ne.def] at *,
      cases hy,exfalso, exact hne hy.symm, 
      exact (mem_of_mem_inter_right (hB hy)),},
    rwa [h, ← mem_neighbor_finset G v],
    by_cases h2:  y=v,{
      rw h2, simp only [*, ne.def, not_false_iff, coe_union, coe_singleton, set.union_singleton,
      set.mem_insert_iff, eq_self_iff_true, mem_coe, true_or, false_or] at *,
      rw [adj_comm,  ← mem_neighbor_finset G v],
      exact mem_of_mem_inter_right (hB hx)},
    simp only [*, ne.def, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, 
    mem_coe, false_or, eq_self_iff_true] at *,
    exact cl hx hy hne},{
    have: 2=1+1:=by norm_num,
    rw [hC,this, ← add_assoc],
    convert card_union_eq _,{exact hA.2.symm},
    rw disjoint_singleton_right, 
    intros h, apply  (not_mem_res_nbhd G v A) (hB h)},
end


end clique_free_sets

end simple_graph
