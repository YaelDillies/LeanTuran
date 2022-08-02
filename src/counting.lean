import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators

-- local imports
import fedges
import nbhd_res
import clique_free_sets
import misc_finset
import multipartite
import turanpartition
import induced

open finset nat turanpartition

open_locale big_operators 

namespace simple_graph

variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][nonempty α][decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]
include G



---for any (t+2)-clique free set there is a partition into B, a (t+1)-clique free set and A\B 
-- such that e(A)+e(A\B) ≤ e(B) + |B|(|A|-|B|) 
lemma furedi_help : ∀A:finset α, G.clique_free_set A (t+2) → ∃B:finset α, B ⊆ A ∧ G.clique_free_set B (t+1) ∧ 
∑v in A, G.deg_res v A + ∑ v in (A\B), G.deg_res v (A\B) ≤ ∑ v in B, G.deg_res v B + 2*B.card * (A\B).card:=
begin
  cases nat.eq_zero_or_pos t with ht,{
  intros A hA,rw ht at *, rw zero_add at *,
----- t = 0 need to check that ∅ is not a 1-clique. 
  refine ⟨∅,⟨empty_subset A,(G.clique_free_empty (by norm_num: 0 <1)),_⟩⟩,
  rw [sdiff_empty, card_empty, mul_zero,zero_mul, sum_empty, zero_add,G.two_clique_free_sum hA]},{
----- 0 < t case
  intros A hA, by_cases hnem: A.nonempty,{
    obtain ⟨x,hxA,hxM⟩:=G.exists_max_res_deg_vertex hnem, -- get a vert x of max res deg in A
    set hBA:= (G.sub_res_nbhd_A x A), 
    set B:=(G.nbhd_res x A) with hB,-- Let B be the res nbhd of the vertex x of max deg_A 
    refine ⟨B, ⟨hBA,(G.t_clique_free hA hxA),_⟩⟩,
    rw [G.deg_res_add_sum hBA, G.sum_sdf hBA B, add_assoc],
    rw [G.sum_sdf hBA (A\B),G.bip_count hBA,← G.deg_res_add_sum hBA ],
    rw ← hB, rw ← add_assoc, ring_nf,
    apply add_le_add_left _ (∑ v in B, G.deg_res v B ), 
    rw add_comm, rw add_assoc, nth_rewrite 1 add_comm,
    rw ← G.deg_res_add_sum hBA, ring_nf,rw mul_assoc,
    refine mul_le_mul' (by norm_num) _,
    apply le_trans (G.max_deg_res_sum_le (sdiff_subset A B)) _,
    rw [hxM,deg_res],},
    {rw not_nonempty_iff_eq_empty at hnem, 
    refine ⟨∅,⟨empty_subset A,(G.clique_free_empty (by norm_num: 0 <t+1)),_⟩⟩,
    rw [sdiff_empty, card_empty, mul_zero,zero_mul, sum_empty, zero_add,hnem,sum_empty],}},
end



-- Putting together the deg counts of G induced on a larger partition (M with C inserted).
-- Counting degrees sums over the parts of the larger partition is what you expect
-- ie e(G[M_0])+ .. +e(G[M_t])+e(G[C]) = e(G[M'_0])+...+e(G[M'_{t+1}])
lemma internal_count {M: multi_part α} {C : finset α} (h: disjoint M.A C):
 ∑ i in range(M.t+1),∑ v in (M.P i), G.deg_res v (M.P i) + ∑ v in C, G.deg_res v C  =
∑ i in range((insert M h).t+1), ∑ v in ((insert M h).P i), G.deg_res v ((insert M h).P i):=
begin
  simp [insert_t, insert_P,ite_not],
  have  ru:range((M.t+1)+1)=range(M.t+1) ∪ {M.t+1},{
    rw range_succ, rw union_comm, rw insert_eq _,},
  have nm:(M.t+1)∉(range(M.t+1)):=not_mem_range_self,
  have rd: disjoint (range(M.t+1)) {M.t+1}:= disjoint_singleton_right.mpr nm,
  rw [ru,sum_union rd],simp only [sum_singleton, eq_self_iff_true, if_true],
  apply (add_left_inj _).mpr, apply sum_congr rfl, intros k hk,
  have nm:(M.t+1)∉(range(M.t+1)):=not_mem_range_self,
  have kne: k≠M.t+1,{intro h',rw h' at hk, exact nm hk},
  apply sum_congr, split_ifs,{contradiction},{refl},{
  intros v hv,split_ifs,{contradiction},{refl}},
end

-- Furedi's stability theorem: (t+2)-clique-free set A implies there is a (t+1)-partition of A
-- such that edges in A + edges in parts (counted a second time) ≤ edges in the complete
-- (t+1)-partite graph on same partition
-- implies Turan once we have know how to maximize edges of a complete multi-partite graph
theorem furedi : ∀A:finset α, G.clique_free_set A (t+2) → ∃M:multi_part α, M.A=A ∧ M.t =t ∧ 
∑v in A, G.deg_res v A + ∑ i in range(M.t+1),∑ v in (M.P i), G.deg_res v (M.P i) ≤ ∑ v in A, (mp M).deg_res v A:=
begin
  induction t with t ht, {rw zero_add,
  intros A ha, use (default_M A 0), refine ⟨rfl,rfl,_⟩, rw G.two_clique_free_sum ha,
  rw zero_add, unfold default_M, dsimp,simp, apply sum_le_sum,
  intros x hx, rw G.two_clique_free ha x hx,exact zero_le _ },
  --- t.succ case
  {intros A ha, obtain⟨B,hBa,hBc,hBs⟩:=G.furedi_help A ha,  
  have hAsd:=union_sdiff_of_subset hBa,
  obtain ⟨M,Ma,Mt,Ms⟩:=ht B hBc,
  have dAB:disjoint M.A (A\B), {rw Ma, exact disjoint_sdiff,},
  set H: simple_graph α:= (mp (insert M dAB)),
  use (insert M dAB), refine ⟨_,_,_⟩,{  
  rw [insert_AB, Ma], exact union_sdiff_of_subset hBa}, {rwa [insert_t, Mt]},{
  --- so we now have the new partition and "just" need to check the degree sum bound..
  have mpc:=mp_count M dAB, rw [insert_AB, Ma , hAsd] at mpc,
  -- need to sort out the sum over parts in the larger graph
  rw ←  mpc, rw ← G.internal_count dAB, linarith},},
end

end simple_graph
