import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import multipartite
import tactic.core
import turan1
import algebra.big_operators


open finset nat

open_locale big_operators 

namespace simple_graph


-- inductive step for Erdos proof: if A is (t.succ+2)-clique free then for any v ∈ A the restricted nbhd of v in A is (t+2)-clique-free
lemma t_clique_free {A: finset α} {v :α}(hA : G.clique_free_set A (t.succ + 2)) (hv : v ∈ A) :
G.clique_free_set (G.nbhd_res v A) (t + 2):=
begin
  rw clique_free_set at *,
  intros B hB, contrapose! hA,
  set C:= B ∪ {v} with hC,
  refine ⟨C,_,_⟩,
  rw hC, apply union_subset (subset_trans hB (G.sub_res_nbhd_A v A)) _,
  simp only [hv, singleton_subset_iff],
  rw is_n_clique_iff at *,
  refine ⟨_,_⟩, 
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
    by_cases h2:  y=v,
      rw h2, simp only [*, ne.def, not_false_iff, coe_union, coe_singleton, set.union_singleton,
      set.mem_insert_iff, eq_self_iff_true, mem_coe, true_or, false_or] at *,
      rw [adj_comm,  ← mem_neighbor_finset G v],
      exact mem_of_mem_inter_right (hB hx),
    simp only [*, ne.def, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, 
    mem_coe, false_or, eq_self_iff_true] at *,
    exact cl hx hy hne,
    rw [hC, nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc],
    convert card_union_eq _,-- rw is_n_clique_iff at hA, 
    exact hA.2.symm,
    rw disjoint_singleton_right , 
    intros h, apply  (not_mem_res_nbhd G v A) (hB h),
end

--- for any t and n there is a list of (t+1) nats summing to n whose sum of squares is n^2 - 2*Turan(t+1,n)
--- ie there is a partition of n into t+1 parts so that the multipartite graph on these parts has
--  t(t+1,n) edges 
lemma turan_list_lb (t n : ℕ) : ∃l:list ℕ, l.length = t+1 ∧ l.sum = n ∧ n^2 = (l.map (λi,i^2)).sum + 2*turan_numb t n:=
begin
  revert n,
  induction t with t ht,
  intro n, rw [zero_add,tn_simp',mul_zero],
  use [[n]],dsimp, simp only [eq_self_iff_true, list.sum_cons, list.sum_nil, add_zero, and_self] at *,
  intro n,  cases nat.eq_zero_or_pos n with hn0,
  rcases ht 0 with ⟨h0,h1,h2,h3⟩,
  rw [tn_simp,mul_zero,zero_pow (by norm_num:0<2)] at h3,
  use 0 :: h0,
  simp only [list.length, list.map, add_left_inj, list.sum_cons, zero_add, nat.nat_zero_eq_zero, zero_pow', ne.def, bit0_eq_zero,
  nat.one_ne_zero, not_false_iff, add_zero], rw [hn0,zero_pow (by norm_num:0<2),tn_simp,mul_zero,add_zero ],
  exact ⟨h1,h2,h3⟩,
  have ms:=succ_pred_eq_of_pos h,
  set m:=n.pred with hm,rw ← ms,
----inductive step, choose the correct size for the new (t+2)^{th} part
  choose b hb1 hb2 using (tn_max_mem t m m ((self_mem_range_succ m))),
  rcases ht b with ⟨l,l0,l1,l2⟩,
  use (m+1-b) :: l,
  split, simp only [*, list.length] at *,
  split, simp only [*, list.sum_cons, mem_range, eq_self_iff_true] at *, rw ← succ_eq_add_one, rw ms, 
  rw [← succ_eq_add_one, ms] at hb1,
  apply tsub_add_cancel_of_le (le_of_lt hb1),
  rw [ms], simp only [*, list.map, list.sum_cons, mem_range] at *,
  rw [← succ_eq_add_one ,ms] at *,
  rw [← hb2, mul_add, ← add_assoc, add_comm, add_assoc, ←l2],  
  nth_rewrite 0 ← (tsub_add_cancel_of_le (le_of_lt hb1)), ring,
end

end simple_graph