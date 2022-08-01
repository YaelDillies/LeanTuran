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


open finset nat mpartition

open_locale big_operators 

namespace simple_graph

variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][inhabited α]{s : finset α}
[decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]



include G


-- I found dealing with the mathlib "induced" subgraph too painful (probably just too early in my experience of lean)
-- Graph induced by A:finset α, defined to be a simple_graph α (so all vertices outside A have empty neighborhoods)
-- this is basically the same as spanning_coe (induce (A:set α) G) 
@[ext,reducible]
def ind (A : finset α) : simple_graph α :={
  adj:= λ x y, G.adj x y ∧ x ∈ A ∧ y ∈ A, 
  symm:=
  begin
    intros x y hxy, rw adj_comm, tauto, 
  end,
  loopless:= by obviously}
@[ext,reducible]

def bipart (A :finset α) :simple_graph α :=
{ adj:= λ v w, (G.adj v w) ∧ ((v∈ A ∧ w ∉ A) ∨ (v∉ A ∧ w ∈ A)),
  symm :=begin intros x y hxy, rw adj_comm, tauto, end,
  loopless :=by obviously,
}


-- why is this so messy to prove? (presumably it isn't..)
lemma ind_eq_coe_induced (A : finset α) : spanning_coe (induce (A:set α) G) = (G.ind A):=
begin
  ext, simp only [map_adj, comap_adj, function.embedding.coe_subtype, set_coe.exists, mem_coe, subtype.coe_mk, exists_prop],
  split, {rintros ⟨a,h1,b,h2,h3,h4,h5⟩,rw [←h4,←h5], exact ⟨h3,h1,h2⟩},
  {rintros ⟨h,h1,h2⟩, exact ⟨x,h1,x_1,h2,h,rfl,rfl⟩,},
end

-- Given A:finset α and G :simple_graph α we can partition G into G[A] G[Aᶜ] and G[A,Aᶜ]  
lemma split (A : finset α): G = G.ind A ⊔ G.ind Aᶜ ⊔  G.bipart A:=
begin
  ext, simp only [sup_adj, mem_compl], tauto,
end

-- induced subgraphs on disjoint sets meet in the empty graph
lemma empty_of_disjoint_ind {A B: finset α} (h : disjoint A B): G.ind A ⊓ G.ind B = ⊥ :=
begin
ext , simp only [inf_adj, bot_adj], split, {rintro ⟨⟨_,h1,_⟩,⟨_,h2,_⟩⟩, exact h (mem_inter.mpr ⟨h1,h2⟩)},
{tauto},
end


-- different parts of a multi_part induce graphs that meet in the empty graph
lemma empty_of_diff_parts {M : multi_part α} {i j : ℕ}(hi: i∈range(M.t+1)) (hj: j∈range(M.t+1)) (hne:i≠j): G.ind (M.P i) ⊓ G.ind (M.P j)=⊥
:=G.empty_of_disjoint_ind (M.disj i hi j hj hne)


--induced subgraph on A meets bipartite induced subgraph e(A,Aᶜ) in empty graph
lemma empty_of_bipart_ind {A: finset α} : G.ind A ⊓ G.bipart A = ⊥ :=
begin
  ext, simp only [inf_adj, bot_adj], tauto,
end

-- would like to just define the bUnion of the induced graphs directly but can't figure out how to do this.
@[ext]
def edges_inside (M : multi_part α) : finset(sym2 α):=(range(M.t+1)).bUnion (λi, (G.ind (M.P i)).edge_finset)


--so counting edges inside M is same as summing of edges in induced parts (since parts are disjoint..)
lemma edge_mp_count {M : multi_part α} : (G.edges_inside M).card = ∑ i in range(M.t+1),(G.ind (M.P i)).edge_finset.card:=
begin
 apply card_bUnion, intros i hi j hj hne, rw disjoint_edges_iff_meet_empty,exact G.empty_of_diff_parts hi hj hne,
end

-- if v w are adjacent in induced graph then they are adjacent in G
lemma ind_adj_imp {A :finset α} {v w :α} : (G.ind A).adj v w → G.adj v w:=λ h, h.1

-- if v w are adjacent in induced graph on A then they are both in A
lemma ind_adj_imp' {A :finset α} {v w :α} : (G.ind A).adj v w → v ∈ A ∧ w ∈ A:=λ h , h.2

--nbhd of v ∈ A in the graph induced by A is exactly the nbhd of v restricted to A
lemma ind_nbhd_mem {A : finset α} {v : α} : v∈ A → (G.ind A).neighbor_finset v =  G.nbhd_res v A:=
begin
  intros hv,unfold neighbor_finset nbhd_res, ext, 
  simp only [*, set.mem_to_finset, mem_neighbor_set, and_self] at *,  
  split,{intro ha, rw [mem_inter,set.mem_to_finset,mem_neighbor_set],exact ⟨ha.2.2,ha.1⟩},
  {rw [mem_inter, set.mem_to_finset, mem_neighbor_set], tauto},
end

-- if G is not the empty graph it contains an edge
lemma ne_bot_imp_edge : ¬G = ⊥ →  ∃e, e ∈ G.edge_set :=
begin
  rw empty_iff_edge_empty,rw eq_empty_iff_forall_not_mem ,push_neg, 
  simp only [mem_edge_finset, forall_exists_index], tauto,
end



-- if v∉A then v has no neighbors in the induced graph G.ind A
lemma ind_nbhd_nmem {A : finset α} {v : α} : v∉A → ((G.ind A).neighbor_finset v) = ∅:=
begin 
  contrapose,  push_neg,intros h, obtain ⟨w,hw⟩:=nonempty.bex (nonempty_of_ne_empty h),
  rw mem_neighbor_finset at hw, exact hw.2.1, 
end

-- if v∉ A then (G.ind A).degree v is zero
lemma ind_deg_nmem {A : finset α} {v : α} : v∉A → (G.ind A).degree v=0:=
λ h, card_eq_zero.mpr (G.ind_nbhd_nmem h)

-- so degrees of v in the induced graph are deg_res v A or 0 depending on whether or not v ∈ A
lemma ind_deg {A :finset α}{v:α} : (G.ind A).degree v = ite (v∈A) (G.deg_res v A) (0):=
begin
  unfold degree,
  split_ifs,{unfold deg_res,congr, exact G.ind_nbhd_mem h},
  {rw G.ind_nbhd_nmem h, apply card_eq_zero.mpr rfl},
end

-- so degree sum over α in the induced subgraph is same as sum of deg_res over A
-- both count 2*e(G[A])
lemma ind_deg_sum {A :finset α}: ∑v, (G.ind A).degree v = ∑v in A,(G.deg_res v A):=
begin
  simp only [ind_deg], rw sum_ite,rw sum_const, rw smul_zero,rw add_zero, congr,
  ext,rw mem_filter,simp only [mem_univ],tauto,
end

--induced subgraph is a subgraph
lemma ind_sub {A : finset α} : (G.ind A)≤ G:=  λ x y, G.ind_adj_imp 


-- internal edges induced by parts of a partition M
-- I should have defined this as G \(⋃ (G.ind M.P i)) if I 
-- could have made it work.. defining the bUnion operator for simple_graphs
-- was a step too far..

@[ext,reducible]
def bUnion (M: multi_part α) : simple_graph α := {
adj:= λ v w, ∃i ∈ range(M.t+1), (G.ind (M.P i)).adj v w,
symm:= by obviously,
loopless:= by obviously,}

@[ext,reducible]
def ind_int_mp (M: multi_part α) : simple_graph α:={
adj:= λ v w , (G.adj v w) ∧ (∃ i ∈ range(M.t+1), v∈(M.P i) ∧w∈ (M.P i)),
symm:= by obviously, 
loopless:= by obviously,}

-- the two versions of "union of induced disjoint parts" are the same
lemma bUnion_eq_ind_int_mp_sum (M : multi_part α) : G.bUnion M = G.ind_int_mp M:=
begin
  ext,simp only [mem_range, exists_prop],split,
  {rintros ⟨i,hi,ad,hx,hy⟩,exact ⟨ad,i,hi,hx,hy⟩},{rintros ⟨ad,i,hi,hx,hy⟩,exact ⟨i,hi,ad,hx,hy⟩},
end

-- edges inside M are the same as the edge_finset of bUnion M
lemma edges_inside_eq (M : multi_part α) : (G.bUnion M).edge_finset = (G.edges_inside M):=
begin
  unfold edges_inside, ext, simp only [mem_edge_finset, mem_bUnion, mem_range, exists_prop],
  unfold bUnion, induction a, work_on_goal 1 { cases a, dsimp at *, simp only [mem_range, exists_prop] at *, refl }, refl,
end

-- this is a subgraph of G
lemma ind_int_mp_sub (M : multi_part α) : (G.ind_int_mp M)≤ G:=λ _ _ h, h.1


-- G with the internal edges removed is G ⊓ (mp M)
lemma sdiff_with_int {M: multi_part α} (h: M.A =univ)  : G\(G.ind_int_mp M) = G⊓(mp M):=
begin
  ext x y,dsimp, 
  have hx: x∈ M.A:=by {rw h, exact mem_univ x},
  have hy: y∈ M.A:=by {rw h, exact mem_univ y},
  obtain ⟨i,hi,hx1⟩:=inv_part hx,
  obtain ⟨j,hj,hy1⟩:=inv_part hy,
  split,{
    rintros ⟨hadj,h2⟩,refine ⟨hadj,_⟩, push_neg at h2, have h3:=h2 hadj,
    specialize h3 i hi hx1,
    refine mp_imp_adj hi hj hx1 hy1 _,
    intro ne,rw ne at h3, exact h3 hy1,},{
    rintros ⟨hadj,h2⟩, refine ⟨hadj,_⟩, push_neg, intros hadj' i hi hx hy,
    exact not_nbhr_same_part hi hx h2 hy },
end
-- G is the join of the edges induced by the parts and those in the complete 
-- multipartite graph M on α

lemma self_eq_int_ext_mp {M :multi_part α} (h: M.A=univ) : G = (G.ind_int_mp M) ⊔ (G⊓(mp M)):=
begin
  rw ← G.sdiff_with_int h,simp only [sup_sdiff_self_right, right_eq_sup], exact G.ind_int_mp_sub M,
end

-- Given M and v,w vertices with v ∈ M.P i and w ∈ M.A then v,w are adjacent in 
-- the "internal induced subgraph"  iff they are adjacent in the graph induced on M.P i
lemma int_edge_help {M :multi_part α} {v w : α} {i : ℕ}: i ∈ range(M.t+1) → v ∈ (M.P i) →  w ∈ M.A →
((G.ind_int_mp M).adj v w ↔ (G.ind (M.P i)).adj v w):=
begin
  intros hi hv hw, obtain ⟨j,hj,hw⟩:=inv_part hw,dsimp, 
  by_cases i=j,{
      split, {intros h1,rw ←h at hw,exact ⟨h1.1,hv,hw⟩},
      {intros h1, cases h1, exact ⟨h1_left,i,hi,h1_right⟩},}, 
  { split,{intros h1, cases h1 with h2 h3, exfalso, rcases h3 with ⟨k, hkr, hk⟩,
  have ieqk:=uniq_part hi hkr hv hk.1,have jeqk:=uniq_part hj hkr hw hk.2,
  rw ← jeqk at ieqk, exact h ieqk},
  {intros h1, exfalso, exact uniq_part' hi hj h h1.2.2 hw}, },
end

--same as above but for degrees and assuming M covers all of α
lemma int_edge_help' {M :multi_part α} (h: M.A=univ) {v w:α}{i:ℕ}: i∈ range(M.t+1) → v ∈ (M.P i) → 
(G.ind_int_mp M).degree v = (G.ind (M.P i)).degree v:=
begin
  intros hi hv, unfold degree, apply congr_arg _, ext,
  have :=mem_univ a,rw ← h at this, have:=G.int_edge_help  hi hv this,
  rwa [mem_neighbor_finset,mem_neighbor_finset],
end


-- so sum of degrees in internal subgraph is sum over induced subgraphs on parts of sum of degrees
lemma int_ind_deg_sum {M :multi_part α} (h: M.A=univ) :
 ∑v,(G.ind_int_mp M).degree v =  ∑  i in range(M.t+1), ∑ v, (G.ind (M.P i)).degree v:=
begin
have :=bUnion_parts M, rw ← h,nth_rewrite 0 this,
 rw sum_bUnion (pair_disjoint M),
 refine sum_congr rfl _,
 intros i hi, rw (sdiff_part hi), rw sum_union (sdiff_disjoint), 
 have :∑x in M.A\(M.P i),(G.ind (M.P i)).degree x =0,{
  apply sum_eq_zero,intros x hx, rw mem_sdiff at hx, exact G.ind_deg_nmem hx.2,},
  rw this,rw zero_add, apply sum_congr rfl _, intros x hx, apply (G.int_edge_help' h) hi hx, exact x,
end


-- number of edges in the subgraph induced inside all parts is the sum of those induced in each part
lemma int_ind_edge_sum {M :multi_part α} (h: M.A=univ) :
(G.ind_int_mp M).edge_finset.card =  ∑  i in range(M.t+1), (G.ind (M.P i)).edge_finset.card:=
begin
  apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw mul_sum,
  simp only [← sum_degrees_eq_twice_card_edges], exact G.int_ind_deg_sum h,
end

--counting edges in induced parts is (almost) the same as summing restricted degrees...
lemma ind_edge_count {A : finset α}: ∑  v in A, G.deg_res v A = 2* ((G.ind A).edge_finset.card ) :=
begin
  rw [← sum_degrees_eq_twice_card_edges,G.ind_deg_sum],
end



-- restricted degree additive over partition of A into B ∪ A\B
-- this is daft, it would work for any function defined on A 
lemma sum_sdf {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A):
 ∑ v in A, G.deg_res v C = ∑v in B, G.deg_res v C + ∑ v in A\B, G.deg_res v C:=
begin
  nth_rewrite 0 ← union_sdiff_of_subset hB, exact sum_union (disjoint_sdiff),
end

-- restricted deg over A = restricted deg over B + restricted deg over A\B
lemma deg_res_add  {v : α} {A B : finset α} (hB: B ⊆ A): G.deg_res v A=  G.deg_res v B +  G.deg_res v (A\B):=
begin
  simp [deg_res,nbhd_res], nth_rewrite 0 ← union_sdiff_of_subset hB, 
  rw inter_distrib_right B (A\B) _,
  exact card_disjoint_union (sdiff_inter_disj A B _),
end

-- sum version of previous lemma
lemma deg_res_add_sum {A B C : finset α} (hB: B ⊆ A) : ∑ v in C, G.deg_res v A=  ∑ v in C, G.deg_res v B+  ∑ v in C,G.deg_res v (A\B):=
begin
  rw ← sum_add_distrib, exact sum_congr rfl (λ _ _ , G.deg_res_add hB),
end

-- if A and B are disjoint then for any vertex v the deg_res add
lemma deg_res_add'  {v : α} {A B : finset α} (h: disjoint A B): G.deg_res v (A∪B)=  G.deg_res v A +  G.deg_res v B:=
begin
  simp [deg_res,nbhd_res],  rw inter_distrib_right,
  exact card_disjoint_union (disj_of_inter_disj _ _ h),
end
 
-- sum version of previous lemma
lemma deg_res_add_sum' {A B C: finset α} (h: disjoint A B) : ∑ v in C, G.deg_res v (A ∪ B) = ∑ v in C, G.deg_res v A +∑ v in C, G.deg_res v B:=
begin
  rw ← sum_add_distrib, exact sum_congr rfl (λ _ _ , G.deg_res_add' h),
end

-- counting edges exiting B via ite helper, really just counting edges in e(B,A\B)
lemma bip_count_help {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in B, ∑ w in A\B, ite (G.adj v w) 1 0:=
begin
  simp only [deg_res_ones], congr,ext x, simp only [sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id], 
  congr, ext, rwa [mem_res_nbhd,mem_filter,mem_neighbor_finset],
end

-- edges from B to A\B equals edges from A\B to B
lemma bip_count {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in A\B, G.deg_res v B:=
begin
  rw G.bip_count_help hB,
  have:=sdiff_sdiff_eq_self hB,
  conv { to_rhs,congr, skip,rw ← this,},
  rw [G.bip_count_help (sdiff_subset A B),this,sum_comm],
  congr, ext y, congr,ext x, 
  split_ifs,{refl},{exfalso, rw adj_comm at h, exact h_1 h}, 
  {exfalso, rw adj_comm at h, exact h h_1},{refl},
end

-- same but between any pair of disjoint sets rather tha B⊆A and A\B
lemma bip_count_help' {A B : finset α}  (hB: disjoint A B ) : ∑ v in B, G.deg_res v A = ∑ v in B, ∑ w in A, ite (G.adj v w) 1 0:=
begin
  simp only [deg_res_ones], congr,ext x, simp only [sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id], 
  congr, ext, rwa [mem_res_nbhd,mem_filter,mem_neighbor_finset],
end

-- edges from A to B (disjoint) equals edges from B to A
lemma bip_count' {A B : finset α} (hB: disjoint A B ) : ∑ v in B, G.deg_res v A = ∑ v in A, G.deg_res v B:=
begin
  rw G.bip_count_help' hB, rw G.bip_count_help' hB.symm,rw sum_comm, congr,
  ext y, congr,ext x, 
  split_ifs,{refl},{exfalso, rw adj_comm at h, exact h_1 h}, 
  {exfalso, rw adj_comm at h, exact h h_1},{refl},
end

-- sum of res_res_deg ≤ sum of res_deg 
lemma sum_res_le {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A): ∑ v in C, G.deg_res v B ≤ ∑ v in C, G.deg_res v A :=
begin
  apply sum_le_sum _,
  intros i hi, 
  rw [deg_res,deg_res], apply card_le_of_subset _,
  intros x hx, rw [mem_res_nbhd] at *,
  exact ⟨hB hx.1, hx.2⟩,
end


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

end simple_graph
