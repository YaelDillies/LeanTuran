import turan1


open finset nat mpartition

open_locale big_operators 

namespace simple_graph
variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][inhabited α]{s : finset α}
[decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]

--- If G is a simple_graph α that contains no K_{t+2} and has turan_numb (t (fintype.card α)) -s edges then 
-- by deleting at most s edges from G we obtain a subgraph of a complete (t+1)-partite graph (mp M)  
theorem furedi_stability : G.clique_free (t+2) → ∃ M: multi_part α, M.t=t ∧ M.A=univ ∧
G.edge_finset.card + ∑ i in range(t+1), (G.ind (M.P i)).edge_finset.card ≤ (mp M).edge_finset.card:=
begin
  intro h, obtain ⟨M,hA,ht,hs⟩:=G.furedi univ (G.clique_free_graph_imp_set h),
  refine ⟨M,ht,hA,_⟩,apply (mul_le_mul_left (by norm_num:0<2)).mp, rw [mul_add, mul_sum], simp only [deg_res_univ] at hs,
  rw  [← G.sum_degrees_eq_twice_card_edges,← (mp M).sum_degrees_eq_twice_card_edges],
  apply le_trans _ hs, apply add_le_add_left,  apply le_of_eq, apply sum_congr, rwa ht,
  intros i hi, rw ← ind_edge_count,
end 

--Now deduce Turan's theorem without worring about case of equality yet
theorem turan : G.clique_free (t+2) → G.edge_finset.card ≤ tn t (fintype.card α):=
begin
  intro h, obtain ⟨M,ht,hA,hc⟩:=G.furedi_stability h,
  have :=turan_max_edges M hA,rw ht at this,
  apply le_trans (le_of_add_le_left hc) this,
end

-- uniqueness? 
--- there are three places where G can fail to achieve equality in Furedi's stability theorem
-- 1) there are "internal" edges, ie edges inside a part of the (t+1)-partition  (counted in the LHS)
-- 2) the partition can fail to be balanced (and hence #edgesof mp M < turan_numb)
-- 3) the multipartite induced graph G ⊓ (mp M) may not be complete 
-- Clearly for equality in Furedi-Turan hybrid ie LHS of Furedi with RHS of Turan
-- need M is a balanced partition and G is multipartite (ie no internal edges)
-- could then prove in this case G ≤ (mp M) = T and hence G = T for equality.   


-- So we have e(G)+edges internal to the partiton ≤ edges of complete (t+1)-partite M
theorem furedi_stability' : G.clique_free (t+2) → ∃ M: multi_part α, M.t=t ∧ M.A=univ ∧
G.edge_finset.card + (G.ind_int_mp M).edge_finset.card ≤ (mp M).edge_finset.card:=
begin
  intro h, obtain⟨M,ht,hu,hle⟩:=G.furedi_stability h, rw ← ht at hle,rw ← G.int_ind_edge_sum hu at hle,
  exact ⟨M,ht,hu,hle⟩,
end

--now deduce case of equality in Turan's theorem
theorem turan_equality :  G.clique_free (t+2) ∧ G.edge_finset.card = tn t (fintype.card α)
 ↔  ∃ M:multi_part α, M.t=t ∧ M.A=univ ∧ turan_partition M ∧ G = mp M:=
begin
  split,{
  intro h,obtain ⟨M,ht,hu,hle⟩:=G.furedi_stability' h.1, rw h.2 at hle,
  refine ⟨M,ht,hu,_⟩, have tm:=turan_max_edges M hu, rw ht at tm, 
  have inz:(G.ind_int_mp M).edge_finset.card=0:= by linarith, rw card_eq_zero at inz,
  have inem: (G.ind_int_mp M)=⊥:=empty_iff_edge_empty.mpr inz,
  have dec:=G.self_eq_int_ext_mp hu,rw inem at dec, simp only [bot_sup_eq, left_eq_inf] at dec,
  have ieq:(mp M).edge_finset.card= tn t (fintype.card α):=by linarith, rw ← ht at ieq,
  refine ⟨turan_eq_imp M hu ieq,_⟩, rw ←  h.2 at tm,
  exact edge_eq_sub_imp_eq dec tm},
  { intro h, obtain ⟨M,ht,hu,iM,hG⟩:=h, 
    have hc:=G.mp_clique_free M ht hu,
    have ieq:=turan_imm_imp_eq M hu ht iM,  rw ← hG at hc, 
    refine ⟨hc,_⟩,
    have h2:=eq_iff_edges_eq.mp hG,
    have : G.edge_finset.card= (mp M).edge_finset.card,{simp only [*] at *},
    rwa ieq at this,},
end

-- the usual version of Furedi's stability theorem says:
-- if G is (K_t+2)-free and has (turan numb - s) edges
-- then we can make G (t+1)-partite by deleting at most s edges 
--


theorem furedi_stability_count {s:ℕ} : G.clique_free (t+2) → G.edge_finset.card = tn t (fintype.card α) - s → 
∃ M: multi_part α, M.t=t ∧ M.A=univ  ∧ G.is_far (mp M) s:=
begin
--
intros h1 h2, obtain ⟨M,ht,hA,hle⟩:=G.furedi_stability' h1,
refine ⟨M,ht,hA,_⟩, rw h2 at hle,
have tm:=turan_max_edges M hA, rw  ht at tm,
by_cases hs: s≤ tn t (fintype.card α),{
have ic:(G.ind_int_mp M).edge_finset.card ≤ s:= by linarith,
have id:=G.self_eq_int_ext_mp hA,
refine ⟨(G.ind_int_mp M).edge_finset,_,ic⟩, 
rw G.del_fedges_is_sdiff (G.ind_int_mp M),{ rw G.sdiff_with_int hA,
  by { intro, simp { contextual := tt } },},
  {exact (G.ind_int_mp M).edge_finset},},
  {have :G.edge_finset.card ≤s:=by linarith, 
    exact G.is_far_trivial (mp M) s (this)},
end



end simple_graph