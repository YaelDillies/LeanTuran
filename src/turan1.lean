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
import mpartition
import induced


open finset nat mpartition

open_locale big_operators 

namespace simple_graph

variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][inhabited α]{s : finset α}
[decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]

include G
-- vertices in new part are adjacent to all old vertices
--- should have used lemmas from multipartite for this...
-- this says that the degree of any vertex in the new part equals the sum over the old parts
lemma mp_com (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∀ v ∈ C, (mp (insert M h)).deg_res v M.A=(M.A.card):=
begin
 intros v hv, rw deg_res, congr, ext,
 rw mem_res_nbhd,split,intro h, exact h.1,
 intros ha, refine ⟨ha,_⟩, rw mem_neighbor_finset, dsimp,
 obtain⟨j,hjr,hjm⟩ :=inv_part ha,
 use j,rw insert_t, 
 refine ⟨_,_,_⟩, {rw mem_range at *,linarith [hjr]}, {exact M.t+1},{use self_mem_range_succ _,
 split, {intro jc,rw jc at hjr, exact not_mem_range_self hjr},{right, rw insert_P,
 split_ifs,{exfalso, exact h_1 rfl},rw insert_P, refine ⟨hv,_⟩,split_ifs,{exact hjm},{
 push_neg at h_2,exfalso, rw h_2 at hjr,  exact not_mem_range_self hjr},},},
end


-- given two vertices in the old partition they are adjacent in the partition with 
-- C inserted iff they were already adjacent
lemma mp_old_adj (M :multi_part α) {C : finset α} {v w :α}(h: disjoint M.A C) : v∈ M.A → w ∈ M.A → ((mp M).adj v w ↔ (mp (insert M h)).adj v w):=
begin
  intros hv hw,
  split,{intro hins, obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,
  use k, rw insert_t,rw mem_range at *, refine ⟨(by linarith),l,_,lnek,_⟩,{ 
  rw mem_range,linarith [hlr]},{simp [insert_P],
  split_ifs,{exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr},
  {exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr},
  {exfalso,rw ← h_2 at hlr, exact lt_irrefl l hlr},
  {exact lkc},},},
  {intro hins, obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,rw insert_t at hkr,rw insert_t at hlr,
  refine ⟨k,_,l,_,lnek,_⟩,{ 
  rw mem_range at *,
  by_contra h', have :k=M.t+1:=by linarith [hkr,h],
  cases lkc,{ rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
  exact h vinb}, {rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
  exact h vinb},},{
  rw mem_range at *,
  by_contra h', have :l=M.t+1:=by linarith [hlr,h],
  cases lkc, {rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
  exact h vinb},{ rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
  exact h vinb},},{
  cases lkc, {rw [insert_P,insert_P] at lkc, split_ifs at lkc,{left, exact lkc},
  {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},
  {exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb},
  {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},},{
  rw [insert_P,insert_P] at lkc, split_ifs at lkc,{right, exact lkc},
  {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},
  {exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb},
  {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},},},},
end

-- previous lemma interpreted in terms of res nbhds 
lemma mp_old' (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).nbhd_res v M.A=(mp M).nbhd_res v M.A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  intros v hv,ext,split,{intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
  rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (H.mp_old_adj M h hv ha.1).mpr ha.2},{
  intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
  rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (H.mp_old_adj M h hv ha.1).mp ha.2},
end

-- .. and in terms of deg res
lemma mp_old (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).deg_res v M.A=(mp M).deg_res v M.A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  intros v hv, rw deg_res,rw deg_res,  rw H.mp_old' M h v hv,
end

-- so sum of deg res to old partition over old partition is unchanged
lemma mp_old_sum (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∑ v in M.A, (mp (insert M h)).deg_res v M.A= ∑ v in M.A,(mp M).deg_res v M.A
:=sum_congr rfl ((mp (insert M h)).mp_old M h)


-- vertices in the new part are not adjacent
lemma mp_ind (M : multi_part α) {v w :α} {C :finset α} (h: disjoint M.A C) : v∈C → w∈C →  ¬(mp (insert M h)).adj v w:=
begin
  intros hv hw,   have vin:= insert_P' M h v hv,
  have win:= insert_P' M h w hw,
  have :=self_mem_range_succ (M.t+1), rw ← insert_t M h at this,
  contrapose win,push_neg at win, exact not_nbhr_same_part this vin win,
end


-- so their deg res to the new part is zero
lemma mp_ind' (M : multi_part α) {C :finset α} (h: disjoint M.A C) : ∀v∈C,(mp (insert M h)).deg_res v C=0:=
begin
  intros v hv, rw deg_res, rw card_eq_zero, by_contra h', 
  obtain ⟨w,hw,adw⟩ :=(mp (insert M h)).exists_mem_nempty h', 
  exact (((mp (insert M h))).mp_ind M h hv hw) adw, 
end

-- so the sum of their deg res to new part is also zero i.e. e(C)=0
lemma mp_ind_sum (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∑ v in C, (mp (insert M h)).deg_res v C=0:=
begin
  simp only [sum_eq_zero_iff], intros x hx, exact (mp (insert M h)).mp_ind' M h x hx,
end

--- counting edges in multipartite graph  
--- if we add in a new part C then the sum of degrees over new vertex set
--  is sum over old + 2 edges in bipartite join
-- ie 2*e(M')=2*e(M)+2*e(M,C)
lemma mp_count (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∑v in M.A, (mp M).deg_res v M.A +2*(M.A.card)*C.card =
∑ v in (insert M h).A, (mp (insert M h)).deg_res v (insert M h).A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  simp  [ insert_AB], rw sum_union h, rw [H.deg_res_add_sum' h,H.deg_res_add_sum' h],
  rw [add_assoc ,H.mp_ind_sum M h,  add_zero,  H.bip_count' h.symm],
  rw [← sum_add_distrib, card_eq_sum_ones C, mul_sum,  H.mp_old_sum M h ,add_right_inj],
  apply sum_congr rfl, rw [(by norm_num: 2= 1+1),add_mul, one_mul, mul_one], intros x hx, rwa (H.mp_com M h x hx),
end


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
    rw [G.deg_res_add_sum hBA, G.sum_sdf hBA hBA, add_assoc],
    rw [G.sum_sdf hBA (sdiff_subset A B),G.bip_count hBA,← G.deg_res_add_sum hBA ],
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



-- if A is (t+2)-clique-free then there exists a (t+1)-partition of M of A so that 
-- e(A) +∑ i≤t, e(A_i) ≤ e(complete_multi_partite M)
-- (Note either A is contained in M or we need to remove edges from inside parts
-- so this implies that if e(A)=max e(M)-s then it can be made (t+1)-partite by
-- removing at most s edges)

-- counting degrees sums over the parts of the larger partition is what you expect
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
-- implies Turan once we have finished with max edges of complete multi-partite....
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
  have mpc:=H.mp_count M dAB, rw [insert_AB, Ma , hAsd] at mpc,
  -- need to sort out the sum over parts in the larger graph
  rw ←  mpc, rw ← G.internal_count dAB, linarith},},
end


-- Furedi stability result:
-- if G is K_{t+2}-free with vertex set α then there is a (t+1)-partition M of α
-- such that the e(G)+ ∑ i< t+1, e(G[M_i]) ≤ e(complete_multipartite M)
-- together with our bound on the number of edges in any complete multipartite graph 
---this easily implies Turan with equality iff G is a complete multipartite graph on a 
--- balanced partition (ie. a Turan graph)




--- should probably prove that any complete (t+1)-partite graph is (t+2)-clique free.
lemma mp_clique_free (M: multi_part α): M.t=t → M.A=univ →  (mp M).clique_free (t+2):=
begin
  intros ht hA, by_contra, unfold clique_free at h, push_neg at h,
  obtain ⟨S,hs1,hs2⟩:=h, rw is_clique_iff at hs1, 
  -- would now like to invoke the pigeonhole principle 
  -- have t+2 pigeons in t+1 classes so two in some class which are then non-adjacent...
  -- i did try to find this in mathlib but it was late so...
  suffices : ∃ i∈range(M.t +1),1 < (S∩(M.P i)).card,{
    obtain ⟨i,hi,hc⟩:=this,  rw [one_lt_card_iff] at hc,
    obtain ⟨a,b,ha,hb,ne⟩:=hc, rw mem_inter at *,
    have nadj:= not_nbhr_same_part' hi  ha.2 hb.2,
    exact nadj  (hs1 ha.1 hb.1 ne),},  
  by_contra, push_neg at h,
  have ub:(range(M.t+1)).sum (λi, (S∩ (M.P i)).card)≤ M.t+1,{
    nth_rewrite_rhs 0 ← card_range (M.t+1), nth_rewrite_rhs 0 card_eq_sum_ones,
    apply sum_le_sum h,}, nth_rewrite_rhs 0 ht at ub,
    have uni:=bUnion_parts M, rw hA at uni,
    have sin:=inter_univ S, rw [uni ,inter_bUnion] at sin,
    rw [← sin, card_bUnion] at hs2, linarith,
    intros x hx y hy ne,
    apply disj_of_disj_inter S S (M.disj x hx y hy ne), 
end



end simple_graph
