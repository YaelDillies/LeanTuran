import combinatorics.simple_graph.basic
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators

--local
import mpartition
import multipartite
import nbhd_res
import fedges

open finset nat mpartition
open_locale big_operators 
namespace simple_graph
section ind
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
  loopless :=by obviously,}


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





end ind




end simple_graph