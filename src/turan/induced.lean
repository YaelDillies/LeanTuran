import algebra.smul_with_zero
import order.partition.finpartition
import turan.close

open nat set
open_locale big_operators

namespace simple_graph
variables {α : Type*} [decidable_eq α] {s : finset α}

-- -- would like to just define the bUnion of the induced graphs directly but can't figure out how to do this.
-- def edges_inside (P : finpartition s) : finset(sym2 α):=(range(M.t)).bUnion (λi, (G.ind (M.P i)).edge_finset)

-- --so counting edges inside M is same as summing of edges in induced parts (since parts are disjoint..)
-- lemma edge_mp_count {P : finpartition s} : (G.edges_inside M).card = ∑ i in range(M.t),(G.ind (M.P i)).edge_finset.card:=
-- begin
--  apply card_bUnion, intros i hi j hj hne, rw disjoint_edge_finset,exact G.empty_of_diff_parts hi hj hne,
-- end

-- -- if v w are adjacent in induced graph then they are adjacent in G
-- lemma ind_adj_imp {s :finset α} {v w :α} : (G.ind s).adj v w → G.adj v w:=λ h, h.1

-- -- if v w are adjacent in induced graph on s then they are both in s
-- lemma ind_adj_imp' {s :finset α} {v w :α} : (G.ind s).adj v w → v ∈ s ∧ w ∈ s:=λ h , h.2

-- --nbhd of v ∈ s in the graph induced by s is exactly the nbhd of v restricted to s
-- lemma ind_nbhd_mem {s : finset α} {v : α} : v∈ s → (G.ind s).neighbor_finset v =  s ∩ G.neighbor_finset v:=
-- begin
--   intros hv,unfold neighbor_finset nbhd_res, ext,
--   simp only [*, set.mem_to_finset, mem_neighbor_set, and_self] at *,
--   split,{intro ha, rw [mem_inter,set.mem_to_finset,mem_neighbor_set],exact ⟨ha.2.2,ha.1⟩},
--   {rw [mem_inter, set.mem_to_finset, mem_neighbor_set], tauto},
-- end

-- -- induced degree of  v ∈ s is deg res to s
-- lemma ind_deg_mem {s : finset α} {v : α} : v∈ s → (G.ind s).degree v= G.deg_on s v:=
-- begin
--   unfold degree deg_on,intros hv, congr,exact G.ind_nbhd_mem hv,
-- end

-- -- if v∉A then v has no neighbors in the induced graph G.ind s
-- lemma ind_nbhd_nmem {s : finset α} {v : α} : v∉A → ((G.ind s).neighbor_finset v) = ∅:=
-- begin
--   contrapose,  push_neg,intros h, obtain ⟨w,hw⟩:=nonempty.bex (nonempty_of_ne_empty h),
--   rw mem_neighbor_finset at hw, exact hw.2.1,
-- end

-- -- if v∉ s then (G.ind s).degree v is zero
-- lemma ind_deg_nmem {s : finset α} {v : α} : v∉A → (G.ind s).degree v=0:=
-- λ h, card_eq_zero.mpr (G.ind_nbhd_nmem h)

-- -- so degrees of v in the induced graph are deg_on s v or 0 depending on whether or not v ∈ s
-- lemma ind_deg {s :finset α}{v:α} : (G.ind s).degree v = ite (v∈A) (G.deg_on s v) (0):=
-- begin
--   unfold degree,
--   split_ifs,{unfold deg_on,congr, exact G.ind_nbhd_mem h},
--   {rw G.ind_nbhd_nmem h, apply card_eq_zero.mpr rfl},
-- end

-- -- finite support of G
-- def fsupport : finset α := univ.filter (λ v, 0 < G.degree v )

-- -- member of support iff degree >0
-- lemma mem_fsupport (v : α) : v ∈ G.fsupport ↔ 0 < G.degree v:=
-- begin
--   unfold fsupport,rw mem_filter, simp only [mem_univ, true_and],
-- end

-- lemma deg_fsupport (v : α) : G.degree v = ite (v∈ G.fsupport) (G.degree v) (0):=
-- begin
--   split_ifs, refl,rw mem_fsupport at h, linarith,
-- end

-- -- a vertex is in the fsupport of (G.ind s) only if it is in s
-- lemma mem_ind_fsupport {v : α} {s: finset α} : v ∈ (G.ind s).fsupport → v ∈ s:=
-- begin
--   rw (G.ind s).mem_fsupport v ,contrapose , push_neg, intros hv, rw G.ind_deg_nmem hv,
-- end

-- -- so when calculating any sum of degrees over a set can restrict to fsupport
-- lemma deg_sum_fsupport {s : finset α} : ∑ v in s, G.degree v = ∑ v in s.filter (λ v , v ∈ G.fsupport), G.degree v:=
-- begin
--   rw sum_filter, apply sum_congr rfl, intros x hx,exact G.deg_fsupport x,
-- end

-- -- so degree sum over α in the induced subgraph is same as sum of deg_on over s
-- -- both count 2*e(G[s])
-- lemma ind_deg_sum {s :finset α}: ∑v, (G.ind s).degree v = ∑v in s,(G.deg_on s v):=
-- begin
--   simp only [ind_deg], rw sum_ite,rw sum_const, rw smul_zero,rw add_zero, congr,
--   ext,rw mem_filter,simp only [mem_univ],tauto,
-- end

-- --induced subgraph is a subgraph
-- lemma ind_sub (s : finset α) : (G.ind s)≤ G:=  λ x y, G.ind_adj_imp

-- -- internal edges induced by parts of a partition M
-- -- I should have defined this as G \(⋃ (G.ind M.P i)) if I
-- -- could have made it work.. defining the bUnion operator for simple_graphs
-- -- was a step too far..

-- ---bipartite graph induced by a finset s
-- @[reducible]
-- def bipart (s :finset α) :simple_graph α :=
-- { adj:= λ v w, (G.adj v w) ∧ (v∈ s ∧ w ∉ s ∨ v∉ s ∧ w ∈ s),
--   symm :=begin intros x y hxy, rw adj_comm, tauto, end,
--   loopless :=by obviously,}

-- -- the bipartite graph induced by s (and Aᶜ) is the same as that induced by Aᶜ (and s = Aᶜᶜ)
-- lemma bipart_comp_eq_self {s : finset α} : (G.bipart s)=(G.bipart Aᶜ):=
-- begin
--   tidy; tauto
-- end

-- --induced subgraph on s meets bipartite induced subgraph e(s,Aᶜ) in empty graph
-- lemma empty_of_ind_bipart (s: finset α) : (G.ind s ⊔ G.ind Aᶜ) ⊓ G.bipart s = ⊥ :=
-- begin
--   ext, simp only [inf_adj, sup_adj,bot_adj, mem_compl], tauto,
-- end

-- -- Given s:finset α and G :simple_graph α we can partition G into G[s] G[Aᶜ] and G[s,Aᶜ]
-- lemma split_induced (s : finset α): G = (G.ind s ⊔ G.ind Aᶜ) ⊔  G.bipart s:=
-- begin
--   ext, simp only [sup_adj, mem_compl], tauto,
-- end

-- --- Edge counting: e(G[s])+e(G[Aᶜ])+e(G[s,Aᶜ])=e(G)
-- lemma edges_split_induced  (s : finset α):  (G.ind s).edge_finset.card + (G.ind Aᶜ).edge_finset.card
-- + (G.bipart s).edge_finset.card = G.edge_finset.card :=
-- begin
--   have:=G.split_induced s,
--   rw edge_finset_inj at this, rw this,
--   rw card_edges_add_of_meet_empty (G.empty_of_ind_bipart s), rw add_left_inj,
--   rwa card_edges_add_of_meet_empty (G.empty_of_ind_comp s),
-- end

-- -- v w adjacent in the bipartite graph given by s iff adj in bipartite graph given by Aᶜ (since they are the same graph..)
-- lemma bipart_comp_adj_iff {s : finset α} {v w :α} : (G.bipart s).adj v w ↔ (G.bipart Aᶜ).adj v w:=
-- begin
--   tidy; tauto,
-- end

-- -- nbhd of v ∈ s in the bipartite graph is the nbhd of v in G restricted to Aᶜ
-- lemma nbhd_bipart_mem {s : finset α} {v : α} (h: v∈ s) : (G.bipart s).neighbor_finset v = G.nbhd_res v Aᶜ:=
-- begin
--   ext, rw [mem_res_nbhd, mem_neighbor_finset,mem_neighbor_finset], tidy; tauto,
-- end

-- -- hence degree is deg_on v to Aᶜ
-- lemma deg_bipart_mem {s : finset α} {v : α} (h: v∈ s) : (G.bipart s).degree v = (G.deg_on s vᶜ):=
-- begin
--   unfold degree deg_on,
--   rwa nbhd_bipart_mem,
-- end

-- -- nbhd of v ∉ s in the bipartite graph is the nbhd of v in G restricted to s
-- lemma nbhd_bipart_not_mem {s : finset α} {v : α} (h: v ∉ s) :  (G.bipart s).neighbor_finset v = s ∩ G.neighbor_finset v:=
-- begin
--   ext, simp only [mem_res_nbhd, mem_neighbor_finset], tidy; tauto,
-- end

-- -- if v∉ s then in the bipartite graph deg v is the deg_on to s
-- lemma deg_bipart_not_mem {s : finset α} {v : α} (h: v ∉ s) :  (G.bipart s).degree v = G.deg_on s v:=
-- begin
--   unfold degree deg_on,rwa nbhd_bipart_not_mem,
-- end

-- -- degree of v ∈ s is degree in induced + degree in bipartite (ie count neighbour in s and Aᶜ)
-- lemma deg_eq_ind_add_bipart {s : finset α} {v : α} : ∀v∈A,  G.degree v= (G.ind s).degree v + (G.bipart s).degree v:=
-- begin
--   intros v hv,  rw G.deg_bipart_mem hv, rw G.ind_deg_mem hv, rw ← G.deg_on_univ,
--   exact G.deg_on_add (subset_univ s),
-- end

-- --ite to count edges from s to Aᶜ
-- lemma bipart_sum_ite {s : finset α}: ∑ v in s, (G.bipart s).degree v = ∑ v in s, ∑  w in Aᶜ, ite (G.adj v w) (1) (0):=
-- begin
--   apply sum_congr rfl, intros x hx, rw G.deg_bipart_mem hx, rw deg_on,rw nbhd_res,
--   rw card_eq_sum_ones, simp only [*, sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id],
--   congr,ext,rw mem_inter,rw mem_neighbor_finset,rw mem_filter,
-- end

-- -- sum of degrees over each part are equal in any induced bipartite graph
-- lemma bipart_sum_eq {s : finset α}: ∑ v in s, (G.bipart s).degree v = ∑ v in Aᶜ, (G.bipart s).degree v :=
-- begin
--   rw [G.bipart_sum_ite, sum_comm], apply sum_congr rfl, intros x hx, rw [compl_eq_univ_sdiff, mem_sdiff] at hx,
--   rw [G.deg_bipart_not_mem hx.2,  deg_on, nbhd_res, card_eq_sum_ones, sum_ite, sum_const,sum_const],
--   dsimp, rw [mul_one,  mul_zero,  add_zero, card_eq_sum_ones], apply sum_congr, ext,
--   rw [mem_inter,  mem_filter, mem_neighbor_finset,  adj_comm],
--   intros y hy,refl,
-- end

-- -- hence sum of degrees over one part counts edges once
-- lemma sum_deg_bipart_eq_edge_card {s : finset α} :∑ v in s, (G.bipart s).degree v = (G.bipart s).edge_finset.card :=
-- begin
--   apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw ← sum_degrees_eq_twice_card_edges,
--   rw [(by norm_num:2=1+1), add_mul, one_mul], nth_rewrite 0 G.bipart_sum_eq,
--   rw compl_eq_univ_sdiff, symmetry,
--   have:disjoint (univ\s) s := sdiff_disjoint,
--   rw ← sum_union this, rw sdiff_union_of_subset (subset_univ s),
-- end

-- --- in the induced graph only need to sum over s to count all edges twice
-- lemma sum_degrees_ind_eq_twice_card_edges {s : finset α} : ∑v in s, (G.ind s).degree v = 2*(G.ind s).edge_finset.card:=
-- begin
--   rw ← sum_degrees_eq_twice_card_edges, rw  ind_deg_sum, apply sum_congr rfl,
--   intros x hx, exact G.ind_deg_mem hx,
-- end

-- -- sum of degrees in s = twice number of edges in s + number of edges from s to Aᶜ
-- lemma sum_deg_ind_bipart {s : finset α} : ∑ v in s, G.degree v = 2*(G.ind s).edge_finset.card + (G.bipart s).edge_finset.card :=
-- begin
--   rw ← sum_degrees_ind_eq_twice_card_edges, rw ← sum_deg_bipart_eq_edge_card, rw ← sum_add_distrib,
--   apply sum_congr rfl,intros x hx, rwa G.deg_eq_ind_add_bipart x hx,
-- end

-- -- any nbhd is contained in the fsupport
-- lemma nbhd_sub_fsupport (v : α) :G.neighbor_finset v ⊆ G.fsupport :=
-- begin
--   intro x,rw [mem_neighbor_finset, mem_fsupport, degree, card_pos],
--   intro h, rw [adj_comm, ← mem_neighbor_finset] at h, exact ⟨v,h⟩,
-- end

-- -- Bound on max degree gives bound on edges of G in the following form:
-- --(Note this almost gives Mantel's theorem since in a K_3-free graph nbhds are independent)
-- lemma sum_deg_ind_max_nbhd {v : α} {s : finset α} (hm: G.degree v= G.max_degree) (hA: s=(G.neighbor_finset v)ᶜ) :
--  2*(G.ind s).edge_finset.card + (G.bipart s).edge_finset.card ≤   (G.fsupport.card - G.max_degree)*G.max_degree:=
-- begin
--   rw [← G.sum_deg_ind_bipart, G.deg_sum_fsupport, ← hm,  degree],
--   rw [sum_filter, sum_ite, sum_const, smul_zero, add_zero, ← card_sdiff (G.nbhd_sub_fsupport v)],
--   nth_rewrite 0 card_eq_sum_ones,rw [sum_mul, one_mul],
--   rw hA, rw [filter_mem_eq_inter, sdiff_eq_inter_compl, inter_comm],
--   refine sum_le_sum (λ x hx, _),
--   rw [← degree, hm],
--   exact G.degree_le_max_degree x,
-- end

-- -- The essential bound for Füredi's result:
-- -- e(G) + e(G[Γ(v)ᶜ]) ≤ (G.fsupport.card - Δ(G))*Δ(G) + e(G[Γ(v)])
-- lemma edge_bound_max_deg {v : α} {s : finset α} (hm: G.degree v= G.max_degree) (hA: s=(G.neighbor_finset v)ᶜ) :
--  G.edge_finset.card + (G.ind s).edge_finset.card ≤
--  (G.fsupport.card - G.max_degree)*G.max_degree + (G.ind Aᶜ).edge_finset.card:=
-- begin
--   rw ← G.edges_split_induced s, have:=G.sum_deg_ind_max_nbhd hm hA, linarith,
-- end

-- -- any "actual" clique consists of vertices in the support
-- lemma clique_sub_fsupport {t : ℕ} {S :finset α} (ht: 2 ≤ t) (h: G.is_n_clique t S) :
--   S ⊆ G.fsupport :=
-- begin
--   intros a ha, rw is_n_clique_iff at h,  have :(1 < S.card):= by linarith,
--   obtain ⟨b,hb,hne⟩:= exists_ne_of_one_lt_card this a,
--   rw ← mem_coe at *, have hadj:=h.1 hb ha hne, rw mem_coe, rw ← mem_neighbor_finset at hadj,
--   exact (G.nbhd_sub_fsupport b) hadj,
-- end

-- -- any t+2 clique of an induced graph is a subset of the induced set
-- lemma clique_ind_sub_ind {s S : finset α} (h: 2 ≤ t): (G.ind s).is_n_clique t S → S ⊆ s:=
-- begin
--   intros h1 a ha, exact G.mem_ind_fsupport (((G.ind s).clique_sub_fsupport h h1) ha),
-- end

-- -- if S a t-clique in a nbhd Γ(v) then inserting v gives a t-clique
-- lemma clique_insert_nbhr {t : ℕ} {S :finset α} {v : α} (hc: G.is_n_clique t S)
--   (hd: S ⊆ G.neighbor_finset v) :
--   G.is_n_clique t (insert v S) :=
-- begin
--    rw is_n_clique_iff at *, rw ← hc.2, have vnin:v∉S:=by apply set.not_mem_subset hd (G.not_mem_neighbor_finset_self v),
--    rw is_clique_iff at *, refine ⟨_,card_insert_of_not_mem vnin⟩, rw coe_insert,
--    refine set.pairwise.insert hc.1 _, intros b hb hj, rw [G.adj_comm b v, and_self,← mem_neighbor_finset], exact hd hb,
-- end

-- -- Now the other key lemma for Füredi's result:
-- -- If G is K_{t+3}-free then any nbhd induces a K_{t+2}-free graph
-- -- (Could replace t by t-1 below, since G K_2 free → nbhds all empty → graphs induced by nbhds empty → they are K_1 -free )
-- lemma clique_free_nbhd_ind {t : ℕ} {v : α} : G.clique_free (t+3) →  (G.ind (G.neighbor_finset v)).clique_free (t+2):=
-- begin
--   contrapose, unfold clique_free, push_neg, rintro ⟨S,hs⟩, use (insert v S),
--   have:=G.clique_insert_nbhr (⟨(is_clique.mono (G.ind_sub (G.neighbor_finset v)) hs.1),hs.2⟩) (G.clique_ind_sub_ind (by linarith) hs),
--   rwa [(by norm_num: 3=2+1),← add_assoc],
-- end

-- @[reducible]
-- def bUnion (P : finpartition s) : simple_graph α := {
-- adj:= λ v w, ∃i ∈ range(M.t), (G.ind (M.P i)).adj v w,
-- symm:= by obviously,
-- loopless:= by obviously,}

-- @[reducible]
-- def disJoin (P : finpartition s) : simple_graph α:={
-- adj:= λ v w , (G.adj v w) ∧ (∃ i ∈ range(M.t), v∈(M.P i) ∧w∈ (M.P i)),
-- symm:= by obviously,
-- loopless:= by obviously,}

-- -- the two versions of "union of induced disjoint parts" are the same
-- lemma bUnion_eq_disJoin_sum (P : finpartition s) : G.bUnion M = G.disJoin M:=
-- begin
--   ext,simp only [mem_range, exists_prop],split,
--   {rintro ⟨i,hi,ad,hx,hy⟩,exact ⟨ad,i,hi,hx,hy⟩},{rintro ⟨ad,i,hi,hx,hy⟩,exact ⟨i,hi,ad,hx,hy⟩},
-- end

-- -- edges inside M are the same as the edge_finset of bUnion M
-- lemma edges_inside_eq (P : finpartition s) : (G.bUnion M).edge_finset = (G.edges_inside M):=
-- begin
--   unfold edges_inside, ext, simp only [mem_edge_finset, mem_bUnion, mem_range, exists_prop],
--   unfold bUnion, induction a, work_on_goal 1 { cases a, dsimp at *, simp only [mem_range, exists_prop] at *, refl }, refl,
-- end

-- -- this is a subgraph of G
-- lemma disJoin_sub (P : finpartition s) : (G.disJoin M)≤ G:=λ _ _ h, h.1

-- -- G with the internal edges removed is G ⊓ (mp M)
-- lemma sdiff_with_int {P : finpartition s} (h: M.s =univ)  : G\(G.disJoin M) = G⊓(mp M):=
-- begin
--   ext x y,dsimp,
--   have hx: x∈ M.s:=by {rw h, exact mem_univ x},
--   have hy: y∈ M.s:=by {rw h, exact mem_univ y},
--   obtain ⟨i,hi,hx1⟩:=inv_part hx,
--   obtain ⟨j,hj,hy1⟩:=inv_part hy,
--   split,{
--     rintro ⟨hadj,h2⟩,refine ⟨hadj,_⟩, push_neg at h2, have h3:=h2 hadj,
--     specialize h3 i hi hx1,
--     refine mp_imp_adj hi hj hx1 hy1 _,
--     intro ne,rw ne at h3, exact h3 hy1,},{
--     rintro ⟨hadj,h2⟩, refine ⟨hadj,_⟩, push_neg, intros hadj' i hi hx hy,
--     exact not_nbhr_same_part hi hx h2 hy },
-- end

-- -- G is the join of the edges induced by the parts and those in the complete
-- -- multipartite graph M on α
-- lemma self_eq_disJoin_ext_mp {M :finpartition s} (h: M.s=univ) : G = (G.disJoin M) ⊔ (G⊓(mp M)):=
-- begin
--   rw ← G.sdiff_with_int h,simp only [sup_sdiff_self_right, right_eq_sup], exact G.disJoin_sub M,
-- end

-- -- Given M and v,w vertices with v ∈ M.P i and w ∈ M.s then v,w are adjacent in
-- -- the "internal induced subgraph"  iff they are adjacent in the graph induced on M.P i
-- lemma disJoin_edge_help {M :finpartition s} {v w : α} {i : ℕ}: i ∈ range(M.t) → v ∈ (M.P i) →  w ∈ M.s →
-- ((G.disJoin M).adj v w ↔ (G.ind (M.P i)).adj v w):=
-- begin
--   intros hi hv hw, obtain ⟨j,hj,hw⟩:=inv_part hw,dsimp,
--   by_cases i=j,{
--       split, {intros h1,rw ←h at hw,exact ⟨h1.1,hv,hw⟩},
--       {intros h1, cases h1, exact ⟨h1_left,i,hi,h1_right⟩},},
--   { split,{intros h1, cases h1 with h2 h3, exfalso, rcases h3 with ⟨k, hkr, hk⟩,
--   have ieqk:=uniq_part hi hkr hv hk.1,have jeqk:=uniq_part hj hkr hw hk.2,
--   rw ← jeqk at ieqk, exact h ieqk},
--   {intros h1, exfalso, exact uniq_part' hi hj h h1.2.2 hw}, },
-- end

-- --same as above but for degrees and assuming M covers all of α
-- lemma disJoin_edge_help' {M :finpartition s} (h: M.s=univ) {v w:α}{i:ℕ}: i∈ range(M.t) → v ∈ (M.P i) →
-- (G.disJoin M).degree v = (G.ind (M.P i)).degree v:=
-- begin
--   intros hi hv, unfold degree, apply congr_arg _, ext,
--   have :=mem_univ a,rw ← h at this, have:=G.disJoin_edge_help  hi hv this,
--   rwa [mem_neighbor_finset,mem_neighbor_finset],
-- end

-- -- so sum of degrees in internal subgraph is sum over induced subgraphs on parts of sum of degrees
-- lemma disJoin_deg_sum {M :finpartition s} (h: M.s=univ) :
--  ∑v,(G.disJoin M).degree v =  ∑  i in range(M.t), ∑ v, (G.ind (M.P i)).degree v:=
-- begin
-- have :=bUnion_parts M, rw ← h,nth_rewrite 0 this,
--  rw sum_bUnion (pair_disjoint M),
--  refine sum_congr rfl _,
--  intros i hi, rw (sdiff_part hi), rw sum_union (sdiff_disjoint),
--  have :∑x in M.s\(M.P i),(G.ind (M.P i)).degree x =0,{
--   apply sum_eq_zero,intros x hx, rw mem_sdiff at hx, exact G.ind_deg_nmem hx.2,},
--   rw this,rw zero_add, apply sum_congr rfl _, intros x hx, apply (G.disJoin_edge_help' h) hi hx, exact x,
-- end

-- -- number of edges in the subgraph induced inside all parts is the sum of those induced in each part
-- lemma disJoin_edge_sum {M :finpartition s} (h: M.s=univ) :
-- (G.disJoin M).edge_finset.card =  ∑  i in range(M.t), (G.ind (M.P i)).edge_finset.card:=
-- begin
--   apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw mul_sum,
--   simp only [← sum_degrees_eq_twice_card_edges], exact G.disJoin_deg_sum h,
-- end

-- --counting edges in induced parts is (almost) the same as summing restricted degrees...
-- lemma ind_edge_count {s : finset α}: ∑  v in s, G.deg_on s v = 2* ((G.ind s).edge_finset.card ) :=
-- begin
--   rw [← sum_degrees_eq_twice_card_edges,G.ind_deg_sum],
-- end

end simple_graph
