import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import turan2
import tactic.core
import algebra.big_operators
open finset fintype nat

open_locale big_operators 

namespace simple_graph

variables {t n : ℕ} 

variables {α : Type*} (G : simple_graph α)[fintype α][inhabited α]{s : finset α}[decidable_eq α] [decidable_rel G.adj]

lemma turan_bd (s : ℕ) {A B :finset α} (hA: A.nonempty) (hB: B⊆A) (hB': B⊂ A): turan_numb s B.card + B.card * (A\B).card ≤ turan_numb s.succ A.card:=
begin
  have : A.card = B.card +(A\B).card,{
    convert card_disjoint_union _, exact (union_sdiff_of_subset hB).symm , apply sdiff_disjoint.symm,},
  rw add_comm at this, 
  obtain ⟨c,hc⟩:=nat.exists_eq_succ_of_ne_zero (ne_of_gt (finset.card_pos.mpr hA)), 
  rw [hc, nat.succ_eq_add_one] at this,
  convert tn_le s B.card _ _,
  exact (tsub_eq_of_eq_add this).symm,
  rw [mem_range,  ← nat.succ_eq_add_one, ← hc],
  exact card_lt_card hB',
end

lemma sdiff_inter_disj (A B C:finset α) : disjoint (B ∩ C)  (A\B ∩ C):=
begin
 have d1:disjoint (B ∩ C) (A\(B ∩ C)):= sdiff_disjoint.symm,
 convert disjoint_of_subset_right _ d1,
 intros x hx, rw mem_inter at hx,
 rw [mem_sdiff,mem_inter] at *, push_neg, refine ⟨hx.1.1,_⟩, intro hb, exfalso, exact hx.1.2 hb,
end


-- basic structure for complete (t+1)-partite graph on α
structure multi_part :=
(t : ℕ) (A: finset α)
(P: ℕ → finset α)
(uni: A = (range(t+1)).bUnion (λi , P i))
(disj: ∀i∈ range(t+1),∀j∈ range(t+1), i≠j → disjoint (P i) (P j)) 
(deg_sum: ℕ:= A.card^2 - ∑ i in range(t+1), ((P i).card)^2)


-- degree sum of complete multiparite graph = |A|^2-∑ |A_i|^2 
--def deg_sum_multi_part  (M : multi_part) : ℕ := (M.A.card)^2 - ∑ i in range(M.t+1), ((M.P i).card)^2
def extend_M  {B : finset α} {M : multi_part} (h: disjoint B M.A): multi_part :={
  t:=M.t+1,
  A:=B ∪ M.A,
  P:=begin intro i, exact ite (i≠M.t+1) (M.P i) (B), end,
  uni:= begin
    rw range_succ, rw [bUnion_insert],rw M.uni, split_ifs, contradiction,
    ext,rw [mem_union,mem_union,mem_bUnion,mem_bUnion],
    split,intro h, cases h with hb hP,left, exact hb,right, 
    obtain ⟨a1, H, H2⟩:=hP, use [a1,H],split_ifs, exact H2,   
    push_neg at h_2, exfalso, rw h_2 at H, exact not_mem_range_self H,
    intros h,cases h with hb hP,left, exact hb,right, 
    obtain ⟨a1, H, H2⟩:=hP,split_ifs at H2, use [a1,H, H2],
    push_neg at h_2, exfalso, rw h_2 at H, exact not_mem_range_self H,
  end,
  disj:= begin
    intros i hi j hj ne, split_ifs, exact M.disj i hi j hj ne,
  sorry,
  end,
  deg_sum:= begin


  sorry,
  end,}



include G
-- res nbhd is part of nbhd in A
@[ext]def nbhd_res (v : α) (A : finset α) : finset α := A ∩ G.neighbor_finset v 

-- restriction of degree to A
def deg_res (v : α) (A : finset α) : ℕ:= (G.nbhd_res v A).card

-- restricting to univ is no restriction at all
lemma deg_res_univ (v : α) : G.deg_res v univ = G.degree v:=
begin
  rw [deg_res,degree], congr, rw [nbhd_res,univ_inter],
end

-- max deg res is zero if A is empty
def max_deg_res (A :finset α) : ℕ :=
begin
  exact option.get_or_else (A.image (λ v, G.deg_res v A)).max 0
end

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

-- bound on sum of res_deg given max res deg
lemma max_deg_res_sum_le {A C : finset α} (hC: C ⊆ A) : ∑ v in C, G.deg_res v A ≤ (G.max_deg_res A)*(C.card):=
begin
  rw finset.card_eq_sum_ones, rw [mul_sum,mul_one],
  apply sum_le_sum _, intros i hi, exact G.deg_res_le_max_deg_res (hC hi),
end

-- restricted degree to A is sum of 1 over each neighbour of v in A
lemma deg_res_ones (v : α) (A : finset α) : G.deg_res v A = ∑ x in G.nbhd_res v A, 1:=
begin
  rw deg_res, exact card_eq_sum_ones _,
end

--- if the restricted nbhd is non-empty then v has a neighbor in A
lemma exists_mem_nempty {v :α} {A : finset α} (hA:  ¬(G.nbhd_res v A) = ∅ ): ∃ w∈A, G.adj v w :=
begin
  rw nbhd_res at hA, contrapose! hA,
  rw eq_empty_iff_forall_not_mem,intros x hx, rw [mem_inter, mem_neighbor_finset] at hx, 
  exact hA x hx.1 hx.2, 
end

-- member of the restricted nhd iff in nbhd and in A
lemma mem_res_nbhd (v w : α) (A : finset α) : w ∈ G.nbhd_res v A ↔ w ∈ A ∧ w ∈ G.neighbor_finset v:=
begin
  rw [nbhd_res,mem_inter], 
end

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
lemma ssub_res_nbhd_of_mem {v : α} {A : finset α} (h: v ∈ A) : G.nbhd_res v A ⊂ A:=
begin
  exact (ssubset_iff_of_subset (G.sub_res_nbhd_A v A)).mpr  ⟨v,h,G.not_mem_res_nbhd v A⟩,
end

-- restricted nbhd contained in nbhd
lemma sub_res_nbhd_N (v : α)(A : finset α) : G.nbhd_res v A ⊆ G.neighbor_finset v:=
begin
  intro x, rw mem_res_nbhd, intro h, exact h.2,
end

-- A is a t-clique free set of vertices in G
def clique_free_set (A : finset α) (s : ℕ): Prop:= ∀ B ⊆ A, ¬G.is_n_clique s B

-- if G has no s-clique then nor does the univ 
lemma clique_free_graph_imp_set {s : ℕ} (h: G.clique_free s) :  G.clique_free_set univ s:=
begin
  revert h, contrapose,
  rw clique_free_set,push_neg,intro h, rw clique_free, push_neg,
  obtain ⟨B,h1,h2⟩:=h,
  exact ⟨B,h2⟩,
end

-- base case for Erdos proof:
-- if A has no 2-clique then restricted degrees are all zero 
-- i.e. A is an independent set
lemma two_clique_free {A: finset α} (hA : G.clique_free_set A 2) :  ∀v∈A, G.deg_res v A =0 :=
begin
  intros v hv, rw [deg_res,finset.card_eq_zero], 
  contrapose! hA,
  obtain ⟨w,hw⟩:=exists_mem_nempty G hA,
  cases hw with h1 h2, 
  have ne: v≠w := adj.ne h2,
  have c2 :card {v,w} =2:=card_doubleton ne,
  have :G.is_n_clique 2 {v,w},{
    rw [is_n_clique_iff, coe_insert, coe_singleton, is_clique_iff,set.pairwise_pair_of_symmetric],
    exact ⟨λh,h2,c2⟩,exact G.symm,},
  rw clique_free_set, push_neg,
  refine ⟨{v,w},_,this⟩, intros x hx,
  simp only [mem_insert, mem_singleton] at *,cases hx, rw hx,exact hv,rw hx, exact h1,
end

-- inductive step: if A is (t.succ+2)-clique free then for any v ∈ A the restricted nbhd of v in A is (t+2)-clique-free
lemma t_clique_free {A: finset α} {v :α}(hA : G.clique_free_set A (t.succ + 2)) (hv : v ∈ A) :
G.clique_free_set (G.nbhd_res v A) (t + 2):=
begin
  rw clique_free_set at *,
  intros B hB, contrapose! hA,
  set C:= B ∪ {v} with hC,
  refine ⟨C,_,_⟩,
  rw hC, apply union_subset (subset_trans hB (G.sub_res_nbhd_A v A)) _,
  simp only [hv, singleton_subset_iff],
  rw is_n_clique_iff at *,
  refine ⟨_,_⟩, 
  rcases hA with ⟨cl,ca⟩, 
  rw [is_clique_iff, set.pairwise],
  intros x hx y hy hne,
  by_cases x=v,
    have yB : y∈ G.neighbor_finset v,{ 
      simp only [*, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, 
      mem_coe, eq_self_iff_true, true_or, ne.def] at *,
      cases hy,exfalso, exact hne hy.symm, 
      exact (mem_of_mem_inter_right (hB hy)),},
    rwa [h, ← mem_neighbor_finset G v],
    by_cases h2:  y=v,
      rw h2, simp only [*, ne.def, not_false_iff, coe_union, coe_singleton, set.union_singleton,
      set.mem_insert_iff, eq_self_iff_true, mem_coe, true_or, false_or] at *,
      rw [adj_comm,  ← mem_neighbor_finset G v],
      exact mem_of_mem_inter_right (hB hx),
    simp only [*, ne.def, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, 
    mem_coe, false_or, eq_self_iff_true] at *,
    exact cl hx hy hne,
    rw [hC, nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc],
    convert card_union_eq _,-- rw is_n_clique_iff at hA, 
    exact hA.2.symm,
    rw disjoint_singleton_right , 
    intros h, apply  (not_mem_res_nbhd G v A) (hB h),
end

-- restricted degree additive over partition of A into B ∪ A\B
lemma sum_sdf {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A): ∑ v in A, G.deg_res v C = ∑v in B, G.deg_res v C + ∑ v in A\B, G.deg_res v C:=
begin
  nth_rewrite 0 ← union_sdiff_of_subset hB, exact sum_union (disjoint_sdiff),
end


-- restricted deg over A = restricted deg over B + restricted deg over A\B
lemma deg_res_add  {v : α} {A B : finset α} (hB: B ⊆ A) (hv: v ∈ A): G.deg_res v A=  G.deg_res v B +  G.deg_res v (A\B):=
begin
  simp [deg_res,nbhd_res], nth_rewrite 0 ← union_sdiff_of_subset hB, 
  convert card_disjoint_union _,
  exact inter_distrib_right B (A\B) _,
  exact sdiff_inter_disj A B _,
end

-- restricted deg add sum
lemma deg_res_add_sum {A B C : finset α} (hB: B ⊆ A) (hC: C ⊆ A) : ∑ v in C, G.deg_res v A=  ∑ v in C, G.deg_res v B+  ∑ v in C,G.deg_res v (A\B):=
begin
  rw ← sum_add_distrib, apply finset.sum_congr rfl _, intros x hx, exact G.deg_res_add hB (hC hx),
end

-- counting edges exiting B via ite helper
lemma bip_count_help {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in B, ∑ w in A\B, ite (G.adj v w) 1 0:=
begin
  simp only [deg_res_ones], congr,ext x, simp only [sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id], 
  congr, ext, rw [mem_res_nbhd,mem_filter,mem_neighbor_finset],
end

-- edges from B to A\B equals edges from A\B to B
lemma bip_count {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in A\B, G.deg_res v B:=
begin
  rw G.bip_count_help hB,
  have: A\(A\B)=B:=sdiff_sdiff_eq_self hB,
  conv { to_rhs,congr, skip,rw ← this,},
  rw [G.bip_count_help (sdiff_subset A B),this,sum_comm],
  congr, ext y, congr,ext x, 
  split_ifs,refl,exfalso, rw adj_comm at h, exact h_1 h, 
  exfalso, rw adj_comm at h, exact h h_1,refl,
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

-- main theorem basically erdos proof of degree majorisation of (t+2)-clique-free graph by (t+1)-partite graph
theorem erdos_simple : ∀A:finset α, G.clique_free_set A (t+2) → ∑ v in A,G.deg_res v A ≤ 2*(turan_numb t A.card):=
begin
  induction t with s hs, intros A hA,
  rw [tn_simp',mul_zero], rw zero_add at hA, 
  have := G.two_clique_free hA, 
  rwa [nonpos_iff_eq_zero, sum_eq_zero_iff], 
  -- s.succ case 
  intros A hA, 
  by_cases hnem: A.nonempty,{
    obtain ⟨x,hxA,hxM⟩:=G.exists_max_res_deg_vertex hnem, -- get a vert x of max res deg in A
    -- Let B be the res nbhd of the vertex x of max deg_A 
    set B:= (G.nbhd_res x A), 
    have hBA: B⊆ A:=(G.sub_res_nbhd_A x A), -- B is contained in A
    -- split sum of deg_A using both (1) deg_A v = deg_B v + deg_(A\B) v and (2) the partition: A = B ∪ (A\B)
    -- have ∑ v ∈ A, deg_A v = ∑ v ∈ B, deg_B v + ∑ v ∈ A\B, deg_B v + ∑ v ∈ A, deg_(A\B) v
    rw [G.deg_res_add_sum hBA (subset_refl A),G.sum_sdf hBA hBA, add_assoc],
    -- apply inductive hyp to ∑ v ∈ B, deg_B v using the fact that 
    -- res nbhd of x to B = is (s+2)-clique free (since A is (s.succ+2)-clique free)
    apply add_le_of_add_le_right _ (hs (G.nbhd_res x A) (G.t_clique_free hA hxA)),
    -- use ∑ v ∈ A, deg_(A\B) v = ∑ v ∈ A\B, deg_A v
    rw [G.sum_sdf hBA (sdiff_subset A B),G.bip_count hBA,← G.deg_res_add_sum hBA (sdiff_subset A B)],
    nth_rewrite 1 add_comm, rw ← add_assoc,
    -- the next line is a strict overestimate if A\B contains any edges
    -- since we replace ∑ v ∈ A\B, deg_B v by ∑ v ∈ A\B, deg_A v (i.e. we add in ∑ v∈ A\B, deg_(A\B) v) 
    apply add_le_of_add_le_left _ (G.sum_res_le hBA (sdiff_subset A B)),
    ring_nf, rw ← mul_add, refine mul_le_mul' _ _, refl,
    -- now overestimate by assuming all v ∈ A\B have max deg (i.e. assuming G[A\B,B] is complete bipartite )
    apply add_le_of_add_le_left _ (G.max_deg_res_sum_le (sdiff_subset A B)), 
    rw [hxM,nbhd_res],
    -- use our bound on Turan numbers 
    exact turan_bd s hnem hBA (G.ssub_res_nbhd_of_mem hxA),},
    -- ¬ A.nonempty ie A = ∅
  { rw not_nonempty_iff_eq_empty at hnem, 
    rw [hnem,finset.card_empty,turan_numb, mul_zero,finset.sum_empty],},
end


-- in terms of edges this says that for any subset A of vertices of a  (t+2)-clique free graph
-- there is a (t+1)-multipartite complete graph M=[A_0,...,A_t] on A such that
-- e(A) + ∑ i≤t, e(A_i) ≤ e(M)
-- Since e(M) ≤ T(t+1 ,|A|) this implies that for A containing T(t+1, |A|)-s edges 
-- this implies that A can be made (t+1)-partite by removing at most s edges (those in the parts A_i)
theorem furedi_stability  : ∀A:finset α, G.clique_free_set A (t+2) → ∃ M:multi_part, M.t=t ∧ M.A = A ∧
 ∑ v in A, G.deg_res v A + ∑  i in range(t+1), ∑ x in M.P i, G.deg_res x (M.P i) ≤ M.deg_sum:=
begin
   induction t with s hs, intros A hA,

sorry,sorry,


end



-- usual-ish statement of turan upper bound
theorem turan_ub : G.clique_free (t+2) → G.edge_finset.card ≤ turan_numb t (card α):=
begin
  intro h,
  have sdG:= G.erdos_simple univ (G.clique_free_graph_imp_set h),
  simp only [deg_res_univ] at sdG,
  rwa [sum_degrees_eq_twice_card_edges,card_univ,mul_le_mul_left] at sdG, by norm_num,
end

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
  


-- make a multipartite graph from a list ℕ that is guaranteed to sum to n
def multipartite {l : list ℕ} (hn: l.sum =n) : simple_graph (fin n):={
adj:=
begin
  set sl: list ℕ:= l.scanl (+) 0,  ---take the list and convert it into intervals e.g [2,2,3,3] -> [0,2,4,7,10]
  intros x y, -- 0 ≤ x,y ≤ n-1 (ie fin n) are adjacent if x and y lie in different intervals
  exact (sl.take_while (λa, a<x)) ≠  (sl.take_while (λa, a<y)),-- eg x=3 y=8 have [0,2] ≠ [0,2,4,7] so adj x y
end,
symm:= by obviously,
loopless:= by obviously,}





---- given a graph on a subset of α can form the bipartite join with rest of α
--- don't currently use this but could to define a complete multipartite graph on α
def bip_join {A : finset α} (H: simple_graph A) : simple_graph α:={
adj:=
begin
  set F:=spanning_coe H,
  intros x y, exact F.adj x y ∨ (x∈ A ∧ y ∈ univ\A) ∨ (x ∈ univ\A ∧ y ∈ A), 
end,
symm:=
begin
  simp only [map_adj, function.embedding.coe_subtype, set_coe.exists, subtype.coe_mk, exists_and_distrib_right,
  exists_eq_right_right, exists_eq_right, mem_sdiff, mem_univ, true_and] at *, 
  intros x y hxy,
  obtain ⟨x1,x2,h1⟩:=hxy,
  use [x2,x1], rwa adj_comm,
  cases hxy with h1 h2,right,right, exact ⟨h1.2,h1.1⟩,
  right,left, exact ⟨h2.2,h2.1⟩,
end,
loopless:= by obviously,}

end simple_graph