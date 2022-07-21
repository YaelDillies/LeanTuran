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