import combinatorics.simple_graph.basic
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators


--local
import misc_finset

open finset nat 
open_locale big_operators 
namespace simple_graph

-- When counting edges in graphs we often want to consider subgraphs induced by a set of vertices
-- or subgraphs between two (possibly disjoint) sets of vertices 
-- For this purpose we introduce the restricted neighbourhood a vertex to a finset.
-- this is G.nbhd_res v A = A ∩ G.neighbor_finset v

-- the restricted nbhd of a set of vertices
section nbhd_res
variables {t n : ℕ} 
variables {α : Type*} (G : simple_graph α) [fintype α][inhabited α]{s : finset α}[decidable_eq α][decidable_rel G.adj]


-- restricted nbhd is the part of nbhd in A
include G
@[ext]
def nbhd_res (v : α) (A : finset α) : finset α := A ∩ G.neighbor_finset v 

-- restriction of degree to A
def deg_res (v : α) (A : finset α) : ℕ:= (G.nbhd_res v A).card

-- restricting to univ is no restriction at all
lemma deg_res_univ (v : α) : G.deg_res v univ = G.degree v:=
begin
  rw [deg_res,degree], congr, rw [nbhd_res,univ_inter],
end

-- we only define this over A restricted to A (could be broader)
-- max deg res is zero if A is empty
-- could replace this with (G.ind A).max_degree
def max_deg_res (A :finset α) : ℕ :=option.get_or_else (A.image (λ v, G.deg_res v A)).max 0


-- if A.nonempty then there is a vertex of max_deg_res A
lemma exists_max_res_deg_vertex  {A :finset α} (hA: A.nonempty) :
  ∃ v∈A, G.max_deg_res A  = G.deg_res v A :=
begin
  have neim: (A.image (λ v, G.deg_res v A)).nonempty:=nonempty.image hA _,
  obtain ⟨t, ht⟩ := max_of_nonempty neim,
  have ht₂ := mem_of_max ht,
  simp only [pi.coe_nat, nat.cast_id, exists_prop, nonempty.image_iff, mem_image] at *,
  rcases ht₂ with ⟨a,ha1, ha2⟩,
  refine ⟨a, _⟩,
  rw [max_deg_res, ht,option.get_or_else_coe],
  exact ⟨ha1,ha2.symm⟩,
end



-- The max_deg_res over A is at least the deg_res of any particular vertex in A. 
lemma deg_res_le_max_deg_res  {v : α} {A : finset α} (hvA: v ∈ A) : G.deg_res v A ≤ G.max_deg_res A :=
begin
  have hA: A.nonempty:=⟨v,hvA⟩,
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.deg_res v A) hvA),
  have := finset.le_max_of_mem (mem_image_of_mem _ hvA) ht,
  rwa [max_deg_res,ht],  
end


-- bound on sum of deg_res given max deg_res (also a bound on e(C) for C ⊆ A)
-- or equiv if C ⊆ A then 2*e(G[C])+e(G[C,A\C])≤ (G.ind A).max_degree * |C|
lemma max_deg_res_sum_le {A C : finset α} (hC: C ⊆ A) : ∑ v in C, G.deg_res v A ≤ (G.max_deg_res A)*(C.card):=
begin
  rw [card_eq_sum_ones, mul_sum, mul_one],
  apply sum_le_sum _, intros i hi, exact G.deg_res_le_max_deg_res (hC hi),
end

-- restricted degree to A is sum of ones over each neighbour of v in A
lemma deg_res_ones (v : α) (A : finset α) : G.deg_res v A = ∑ x in G.nbhd_res v A, 1:=card_eq_sum_ones _

--- if the restricted nbhd is non-empty then v has a neighbor in A
lemma exists_mem_nempty {v :α} {A : finset α} (hA:  ¬(G.nbhd_res v A) = ∅ ): ∃ w∈A, G.adj v w :=
begin
  rw nbhd_res at hA, contrapose! hA,
  rw eq_empty_iff_forall_not_mem,
  intros x hx, rw [mem_inter, mem_neighbor_finset] at hx, 
  exact hA x hx.1 hx.2, 
end

-- member of the restricted nhd iff in nbhd and in A
lemma mem_res_nbhd (v w : α) (A : finset α) : w ∈ G.nbhd_res v A ↔ w ∈ A ∧ w ∈ G.neighbor_finset v
:=by rwa [nbhd_res,mem_inter]

-- v is not a neighbor of itself
lemma not_mem_nbhd (v : α)  : v ∉ G.neighbor_finset v :=
begin
 rw mem_neighbor_finset, exact G.loopless v,
end

-- nor is v a restricted neighbor of itself
lemma not_mem_res_nbhd (v : α) (A :finset α) : v ∉ G.nbhd_res v A :=
begin
  rw mem_res_nbhd,push_neg,intro h, exact G.not_mem_nbhd v,
end

-- restricted nbhd is contained in A
lemma sub_res_nbhd_A (v : α) (A : finset α) : G.nbhd_res v A ⊆ A:=
begin
  intro x, rw mem_res_nbhd,intro h, exact h.1,
end

-- restricted nbhd of member is stictly contained in A
lemma ssub_res_nbhd_of_mem {v : α} {A : finset α} (h: v ∈ A) : G.nbhd_res v A ⊂ A
:=(ssubset_iff_of_subset (G.sub_res_nbhd_A v A)).mpr ⟨v,h,G.not_mem_res_nbhd v A⟩

-- restricted nbhd contained in nbhd
lemma sub_res_nbhd_N (v : α)(A : finset α) : G.nbhd_res v A ⊆ G.neighbor_finset v:=
begin
  intro _, rw mem_res_nbhd, intro h, exact h.2,
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


end nbhd_res

end simple_graph
