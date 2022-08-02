import combinatorics.simple_graph.basic
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators

--local
import turanpartition
import multipartite
import nbhd_res
import fedges

open finset nat turanpartition
open_locale big_operators 
namespace simple_graph
section ind
variables {t n : ℕ} 
variables {α : Type*} (G H : simple_graph α)[fintype α][nonempty α]{s : finset α}
[decidable_eq α][decidable_rel G.adj][decidable_rel H.adj]



-- I found dealing with the mathlib "induced" subgraph too painful (probably just too early in my experience of lean)

-- Graph induced by A:finset α, defined to be a simple_graph α (so all vertices outside A have empty neighborhoods)
-- this is equvialent to  "spanning_coe (induce (A:set α) G)" as we prove below.

@[ext,reducible]
def ind (A : finset α) : simple_graph α :={
  adj:= λ x y, G.adj x y ∧ x ∈ A ∧ y ∈ A, 
  symm:=
  begin
    intros x y hxy, rw adj_comm, tauto, 
  end,
  loopless:= by obviously}


-- why is this so messy to prove? (presumably it isn't..)
lemma ind_eq_coe_induced {A : finset α} : spanning_coe (induce (A:set α) G) = (G.ind A):=
begin
  ext, simp only [map_adj, comap_adj, function.embedding.coe_subtype, set_coe.exists, mem_coe, subtype.coe_mk, exists_prop],
  split, {rintros ⟨a,h1,b,h2,h3,h4,h5⟩,rw [←h4,←h5], exact ⟨h3,h1,h2⟩},
  {rintros ⟨h,h1,h2⟩, exact ⟨x,h1,x_1,h2,h,rfl,rfl⟩,},
end


-- induced subgraphs on disjoint sets meet in the empty graph
lemma empty_of_disjoint_ind {A B: finset α} (h : disjoint A B): G.ind A ⊓ G.ind B = ⊥ :=
begin
ext , simp only [inf_adj, bot_adj], split, {rintro ⟨⟨_,h1,_⟩,⟨_,h2,_⟩⟩, exact h (mem_inter.mpr ⟨h1,h2⟩)},
{tauto},
end


-- different parts of a multi_part induce graphs that meet in the empty graph
lemma empty_of_diff_parts {M : multi_part α} {i j : ℕ}(hi: i∈range(M.t+1)) (hj: j∈range(M.t+1)) (hne:i≠j): 
G.ind (M.P i) ⊓ G.ind (M.P j) = ⊥ := G.empty_of_disjoint_ind (M.disj i hi j hj hne)



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




lemma ind_deg_mem {A : finset α} {v : α} : v∈ A → (G.ind A).degree v= G.deg_res v A:=
begin
  unfold degree deg_res,intros hv, congr,exact G.ind_nbhd_mem hv,
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



-- finite support of G
def fsupport : finset α := univ.filter (λ v, 0 < G.degree v )

-- member of support iff degree >0
lemma mem_fsupport (v : α) : v ∈ G.fsupport ↔ 0 < G.degree v:=
begin
  unfold fsupport,rw mem_filter, simp only [mem_univ, true_and],
end


lemma deg_fsupport (v : α) : G.degree v = ite (v∈ G.fsupport) (G.degree v) (0):=
begin
  split_ifs, refl,rw mem_fsupport at h, linarith,
end


-- a vertex is in the fsupport of (G.ind A) only if it is in A
lemma mem_ind_fsupport (v : α) {A: finset α} : v ∈ (G.ind A).fsupport → v ∈ A:=
begin
  rw (G.ind A).mem_fsupport v ,contrapose , push_neg, intros hv, rw G.ind_deg_nmem hv,
end

lemma deg_sum_fsupport {A : finset α} : ∑ v in A, G.degree v = ∑ v in A.filter (λ v , v ∈ G.fsupport), G.degree v:=
begin 
  rw sum_filter, apply sum_congr rfl, intros x hx,exact G.deg_fsupport x,
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

---bipartite graph induced by a finset A 
@[ext,reducible]
def bipart (A :finset α) :simple_graph α :=
{ adj:= λ v w, (G.adj v w) ∧ (v∈ A ∧ w ∉ A ∨ v∉ A ∧ w ∈ A),
  symm :=begin intros x y hxy, rw adj_comm, tauto, end,
  loopless :=by obviously,}

-- the bipartite graph induced by A (and Aᶜ) is the same as that induced by Aᶜ (and A = Aᶜᶜ)
lemma bipart_comp_eq_self {A : finset α} : (G.bipart A)=(G.bipart Aᶜ):=
begin
  tidy; tauto
end


-- v w adjacent in the bipartite graph given by A iff adj in bipartite graph given by Aᶜ (since they are the same graph..)
lemma bipart_comp_adj_iff {A : finset α} {v w :α} : (G.bipart A).adj v w ↔ (G.bipart Aᶜ).adj v w:=
begin
  tidy; tauto,
end

-- nbhd of v ∈ A in the bipartite graph is the nbhd of v in G restricted to Aᶜ
lemma nbhd_bipart_mem {A : finset α} {v : α} (h: v∈ A) : (G.bipart A).neighbor_finset v = G.nbhd_res v Aᶜ:=
begin
  ext, rw [mem_res_nbhd, mem_neighbor_finset,mem_neighbor_finset], tidy; tauto,
end

-- hence degree is deg_res v to Aᶜ
lemma deg_bipart_mem {A : finset α} {v : α} (h: v∈ A) : (G.bipart A).degree v = (G.deg_res v Aᶜ):=
begin
  unfold degree deg_res,rwa nbhd_bipart_mem,
end


-- nbhd of v ∉ A in the bipartite graph is the nbhd of v in G restricted to A
lemma nbhd_bipart_not_mem {A : finset α} {v : α} (h: v ∉ A) :  (G.bipart A).neighbor_finset v = G.nbhd_res v A:=
begin
  ext, simp only [mem_res_nbhd, mem_neighbor_finset], tidy; tauto,
end


-- if v∉ A then in the bipartite graph deg v is the deg_res to A
lemma deg_bipart_not_mem {A : finset α} {v : α} (h: v ∉ A) :  (G.bipart A).degree v = G.deg_res v A:=
begin
  unfold degree deg_res,rwa nbhd_bipart_not_mem,
end


-- degree of v ∈ A is degree in induced + degree in bipartite (ie count neighbour in A and Aᶜ)
lemma deg_eq_ind_add_bipart {A : finset α} {v : α} : ∀v∈A,  G.degree v= (G.ind A).degree v + (G.bipart A).degree v:=
begin
  intros v hv,  rw G.deg_bipart_mem hv, rw G.ind_deg_mem hv, rw ← G.deg_res_univ,
  exact G.deg_res_add (subset_univ A),
end

--ite to count edges from A to Aᶜ
lemma bipart_sum_ite {A : finset α}: ∑ v in A, (G.bipart A).degree v = ∑ v in A, ∑  w in Aᶜ, ite (G.adj v w) (1) (0):=
begin
  apply sum_congr rfl, intros x hx, rw G.deg_bipart_mem hx, rw deg_res,rw nbhd_res,
  rw card_eq_sum_ones, simp only [*, sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id],
  congr,ext,rw mem_inter,rw mem_neighbor_finset,rw mem_filter,
end


-- sum of degrees over each part are equal in any induced bipartite graph
lemma bipart_sum_eq {A : finset α}: ∑ v in A, (G.bipart A).degree v = ∑ v in Aᶜ, (G.bipart A).degree v :=
begin
  rw [G.bipart_sum_ite, sum_comm], apply sum_congr rfl, intros x hx, rw [compl_eq_univ_sdiff, mem_sdiff] at hx,
  rw [G.deg_bipart_not_mem hx.2,  deg_res, nbhd_res, card_eq_sum_ones, sum_ite, sum_const,sum_const],
  dsimp, rw [mul_one,  mul_zero,  add_zero, card_eq_sum_ones], apply sum_congr, ext,
  rw [mem_inter,  mem_filter, mem_neighbor_finset,  adj_comm], 
  intros y hy,refl,
end


-- hence sum of degrees over one part counts edges once
lemma sum_deg_bipart_eq_edge_card {A : finset α} :∑ v in A, (G.bipart A).degree v = (G.bipart A).edge_finset.card :=
begin
  apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw ← sum_degrees_eq_twice_card_edges,
  rw [(by norm_num:2=1+1), add_mul, one_mul], nth_rewrite 0 G.bipart_sum_eq,
  rw compl_eq_univ_sdiff, symmetry, 
  have:disjoint (univ\A) A := sdiff_disjoint,
  rw ← sum_union this, rw sdiff_union_of_subset (subset_univ A),
end

--- in the induced graph only need to sum over A to count all edges twice 
lemma sum_degrees_ind_eq_twice_card_edges {A : finset α} : ∑v in A, (G.ind A).degree v = 2*(G.ind A).edge_finset.card:=
begin
  rw ← sum_degrees_eq_twice_card_edges, rw  ind_deg_sum, apply sum_congr rfl, 
  intros x hx, exact G.ind_deg_mem hx,
end

-- sum of degrees in A = twice number of edges in A + number of edges from A to Aᶜ
lemma sum_deg_ind_bipart {A : finset α} : ∑ v in A, G.degree v = 2*(G.ind A).edge_finset.card + (G.bipart A).edge_finset.card :=
begin
  rw ← sum_degrees_ind_eq_twice_card_edges, rw ← sum_deg_bipart_eq_edge_card, rw ← sum_add_distrib,
  apply sum_congr rfl,intros x hx, rwa G.deg_eq_ind_add_bipart x hx, 
end


-- any nbhd is contained in the fsupport
lemma nbhd_sub_fsupport (v : α) :G.neighbor_finset v ⊆ G.fsupport :=
begin
  intro x,rw mem_neighbor_finset,rw mem_fsupport, rw degree,rw card_pos, intro h, tidy,
end 


-- should have been an easy lemma (finsets not graphs) but couldn't find it: A ⊆ B → Aᶜ ∩ B = B\A
lemma comp_nbhd_int_supp_eq_sdiff (v : α) :(G.neighbor_finset v)ᶜ ∩  G.fsupport = G.fsupport \(G.neighbor_finset v):=
begin
  have h:=G.nbhd_sub_fsupport v, 
  rw compl_eq_univ_sdiff, ext, rw [mem_sdiff,mem_inter,mem_sdiff],simp_rw mem_univ, tauto, 
end

-- so bound on max degree gives bound on edges of G in the following form:
--(Note this almost gives Mantel's theorem since in a K_3-free graph nbhds are independent)
lemma sum_deg_ind_max_nbhd' {v : α} {A : finset α} (h: G.degree v= G.max_degree) (hA: A=(G.neighbor_finset v)ᶜ) :
 2*(G.ind A).edge_finset.card + (G.bipart A).edge_finset.card ≤   (G.fsupport.card - G.max_degree)*G.max_degree:=
begin
  rw [← G.sum_deg_ind_bipart, G.deg_sum_fsupport, ← h,  degree],
  rw [sum_filter, sum_ite, sum_const, smul_zero, add_zero, ← card_sdiff (G.nbhd_sub_fsupport v)],
  nth_rewrite 0 card_eq_sum_ones,rw [sum_mul, one_mul],
  rw hA, rw [filter_mem_eq_inter,  G.comp_nbhd_int_supp_eq_sdiff v],
  apply sum_le_sum,
  rw [← degree, h], intros x hx, exact G.degree_le_max_degree x,
end


lemma sum_deg_ind_max_nbhd {v : α} {A : finset α} (h: G.degree v= G.max_degree) (hA: A=(G.neighbor_finset v)ᶜ) :
 2*(G.ind A).edge_finset.card + (G.bipart A).edge_finset.card ≤   (fintype.card α - G.max_degree)*G.max_degree:=
begin
  rw [← G.sum_deg_ind_bipart,  ← h,  degree, ← card_univ,   ← card_sdiff (subset_univ _)],
  nth_rewrite 0 card_eq_sum_ones, rw [sum_mul, one_mul, ← compl_eq_univ_sdiff , ← hA],
  apply sum_le_sum, intros x hx,   rw [← degree, h],
  exact G.degree_le_max_degree x
end


--induced subgraph on A meets bipartite induced subgraph e(A,Aᶜ) in empty graph
lemma empty_of_bipart_ind {A: finset α} : G.ind A ⊓ G.bipart A = ⊥ :=
begin
  ext, simp only [inf_adj, bot_adj], tauto,
end

-- Given A:finset α and G :simple_graph α we can partition G into G[A] G[Aᶜ] and G[A,Aᶜ]  
lemma split {A : finset α}: G = G.ind A ⊔ G.ind Aᶜ ⊔  G.bipart A:=
begin
  ext, simp only [sup_adj, mem_compl], tauto,
end




@[ext,reducible]
def bUnion (M: multi_part α) : simple_graph α := {
adj:= λ v w, ∃i ∈ range(M.t+1), (G.ind (M.P i)).adj v w,
symm:= by obviously,
loopless:= by obviously,}

@[ext,reducible]
def disJoin (M: multi_part α) : simple_graph α:={
adj:= λ v w , (G.adj v w) ∧ (∃ i ∈ range(M.t+1), v∈(M.P i) ∧w∈ (M.P i)),
symm:= by obviously, 
loopless:= by obviously,}


-- the two versions of "union of induced disjoint parts" are the same
lemma bUnion_eq_disJoin_sum (M : multi_part α) : G.bUnion M = G.disJoin M:=
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
lemma disJoin_sub (M : multi_part α) : (G.disJoin M)≤ G:=λ _ _ h, h.1


-- G with the internal edges removed is G ⊓ (mp M)
lemma sdiff_with_int {M: multi_part α} (h: M.A =univ)  : G\(G.disJoin M) = G⊓(mp M):=
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
lemma self_eq_disJoin_ext_mp {M :multi_part α} (h: M.A=univ) : G = (G.disJoin M) ⊔ (G⊓(mp M)):=
begin
  rw ← G.sdiff_with_int h,simp only [sup_sdiff_self_right, right_eq_sup], exact G.disJoin_sub M,
end

-- Given M and v,w vertices with v ∈ M.P i and w ∈ M.A then v,w are adjacent in 
-- the "internal induced subgraph"  iff they are adjacent in the graph induced on M.P i
lemma disJoin_edge_help {M :multi_part α} {v w : α} {i : ℕ}: i ∈ range(M.t+1) → v ∈ (M.P i) →  w ∈ M.A →
((G.disJoin M).adj v w ↔ (G.ind (M.P i)).adj v w):=
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
lemma disJoin_edge_help' {M :multi_part α} (h: M.A=univ) {v w:α}{i:ℕ}: i∈ range(M.t+1) → v ∈ (M.P i) → 
(G.disJoin M).degree v = (G.ind (M.P i)).degree v:=
begin
  intros hi hv, unfold degree, apply congr_arg _, ext,
  have :=mem_univ a,rw ← h at this, have:=G.disJoin_edge_help  hi hv this,
  rwa [mem_neighbor_finset,mem_neighbor_finset],
end


-- so sum of degrees in internal subgraph is sum over induced subgraphs on parts of sum of degrees
lemma disJoin_deg_sum {M :multi_part α} (h: M.A=univ) :
 ∑v,(G.disJoin M).degree v =  ∑  i in range(M.t+1), ∑ v, (G.ind (M.P i)).degree v:=
begin
have :=bUnion_parts M, rw ← h,nth_rewrite 0 this,
 rw sum_bUnion (pair_disjoint M),
 refine sum_congr rfl _,
 intros i hi, rw (sdiff_part hi), rw sum_union (sdiff_disjoint), 
 have :∑x in M.A\(M.P i),(G.ind (M.P i)).degree x =0,{
  apply sum_eq_zero,intros x hx, rw mem_sdiff at hx, exact G.ind_deg_nmem hx.2,},
  rw this,rw zero_add, apply sum_congr rfl _, intros x hx, apply (G.disJoin_edge_help' h) hi hx, exact x,
end


-- number of edges in the subgraph induced inside all parts is the sum of those induced in each part
lemma disJoin_edge_sum {M :multi_part α} (h: M.A=univ) :
(G.disJoin M).edge_finset.card =  ∑  i in range(M.t+1), (G.ind (M.P i)).edge_finset.card:=
begin
  apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw mul_sum,
  simp only [← sum_degrees_eq_twice_card_edges], exact G.disJoin_deg_sum h,
end

--counting edges in induced parts is (almost) the same as summing restricted degrees...
lemma ind_edge_count {A : finset α}: ∑  v in A, G.deg_res v A = 2* ((G.ind A).edge_finset.card ) :=
begin
  rw [← sum_degrees_eq_twice_card_edges,G.ind_deg_sum],
end





end ind




end simple_graph