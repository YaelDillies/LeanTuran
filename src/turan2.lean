import turan1


open finset nat mpartition

open_locale big_operators 

namespace simple_graph
variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][inhabited α]{s : finset α}
[decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]

--- If G is a simple_graph α that contains no K_{t+2} and has turan_numb (t (fintype.card α)) -s edges then 
-- by deleting at most s edges from G we obtain a subgraph of a complete (t+1)-partite graph (mp M)  


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