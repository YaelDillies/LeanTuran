import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import turan2
import tactic.core
import algebra.big_operators
open finset fintype

open_locale big_operators 
namespace simple_graph
variables {t n : ℕ} 
variables {α : Type*} (G : simple_graph α)[fintype α][inhabited α]{s : finset α}[decidable_eq α] [decidable_rel G.adj]
lemma turan_bd (s : ℕ) {A B :finset α} (hA: A.nonempty) (hB: B⊆A) (hB': B⊂ A): turan_numb s B.card + B.card * (A\B).card ≤ turan_numb s.succ A.card:=
begin
  have : A.card = B.card +(A\B).card,{
    convert card_disjoint_union _, exact (union_sdiff_of_subset hB).symm , apply sdiff_disjoint.symm,
  },
  rw add_comm at this, 
  have Ac':A.card ≠0 := ne_of_gt (finset.card_pos.mpr hA),
  obtain ⟨c,hc⟩:=nat.exists_eq_succ_of_ne_zero Ac', rw hc at this, rw nat.succ_eq_add_one at this,
  convert tn_le s B.card _ _,
  exact (tsub_eq_of_eq_add this).symm,
  rw [mem_range,  ← nat.succ_eq_add_one, ← hc],
  exact card_lt_card hB',
end

include G
-- res nbhd is part of nbhd in A
@[ext]def nbhd_res (v : α) (A : finset α) : finset α := A ∩ G.neighbor_finset v 

-- restriction of degree to A
def deg_res (v : α) (A : finset α) : ℕ:= (G.nbhd_res v A).card

lemma deg_res_univ (v : α) : G.deg_res v univ = G.degree v:=
begin
  rw [deg_res,degree], congr, rw [nbhd_res,univ_inter],
end

lemma deg_res_eq_card_of_ss {A B: finset α} {v :α} (hB2: B=G.nbhd_res v A) : G.deg_res v A= B.card:=
begin
  rw [deg_res,hB2],
end

-- max deg res is zero if A is empty
def max_deg_res (A :finset α): ℕ :=
begin
  exact option.get_or_else (A.image (λ v, G.deg_res v A)).max 0
end

-- if A.nonempty then there is a vertex of max_deg_res A
lemma exists_max_res_deg_vertex  {A :finset α}(hA: A.nonempty) :
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

/-- The max_deg_res over A is at least the deg_res of any particular vertex in A. -/
lemma deg_res_le_max_deg_res  {v : α} {A : finset α} (hvA: v ∈ A) : G.deg_res v A ≤ G.max_deg_res A :=
begin
  have hA: A.nonempty:=⟨v,hvA⟩,
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.deg_res v A) hvA),
  have := finset.le_max_of_mem (mem_image_of_mem _ hvA) ht,
  rwa [max_deg_res,ht],  
end

-- bound on sum of res_deg given max res deg
lemma max_deg_res_sum_le {A C : finset α} (hC: C⊆A) : ∑ v in C, G.deg_res v A ≤ (G.max_deg_res A)*(C.card):=
begin
  rw finset.card_eq_sum_ones, rw [mul_sum,mul_one],
  apply sum_le_sum _, intros i hi, exact G.deg_res_le_max_deg_res (hC hi),
end

-- restricted degree to A is sum of 1 over each neighbour of v in A
lemma deg_res_ones (v : α) (A : finset α) : G.deg_res v A= ∑ x in G.nbhd_res v A, 1:=
begin
  rw deg_res, exact card_eq_sum_ones _,
end

--- if the restricted nbhd is non-empty then v has a neighbor in A
lemma exists_mem_nempty {v :α} {A :finset α} (hA:  ¬(G.nbhd_res v A) = ∅ ): ∃ w∈A, G.adj v w :=
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
lemma not_mem_nbhd (v : α)  : v∉ G.neighbor_finset v :=
begin
 rw mem_neighbor_finset, exact G.loopless v,
end
-- nor is v a restricted neighbor of itself
lemma not_mem_res_nbhd (v : α) (A :finset α) : v∉ G.nbhd_res v A :=
begin
  rw mem_res_nbhd,push_neg,intro h, exact G.not_mem_nbhd v,
end
-- restricted nbhd contained in A
lemma sub_res_nbhd_A (v : α)(A : finset α) : G.nbhd_res v A ⊆ A:=
begin
  intro x, rw mem_res_nbhd,intro h, exact h.1,
end
-- restricted nbhd contained in nbhd
lemma sub_res_nbhd_N (v : α)(A : finset α) : G.nbhd_res v A ⊆ G.neighbor_finset v:=
begin
  intro x, rw mem_res_nbhd,intro h, exact h.2,
end

-- A is a t-clique free set of vertices in G
def clique_free_set (A : finset α) (s: ℕ): Prop:= ∀B⊆A, ¬G.is_n_clique s B

lemma clique_free_graph_imp_set {s:ℕ} (h: G.clique_free s) :  G.clique_free_set univ s:=
begin
  revert h,
  contrapose,
  rw clique_free_set,push_neg,intro h, rw clique_free, push_neg,
  obtain ⟨B,h1,h2⟩:=h,
  use B, exact h2,
end

-- base case for Erdos proof: if A has no 2-clique then the restricted degrees are all zero
lemma two_clique_free {A: finset α}(hA : G.clique_free_set A 2) :  ∀v∈A, G.deg_res v A =0 :=
begin
  intros v hv, rw deg_res, contrapose! hA,
  simp only [finset.card_eq_zero] at hA, 
  obtain ⟨w,hw⟩:=exists_mem_nempty G hA,
  cases hw with h1 h2, 
  have ne: v≠w := adj.ne h2,
  have c2 :card {v,w} =2:=card_doubleton ne,
  have :G.is_n_clique 2 {v,w},
    rw is_n_clique_iff, simp only [coe_insert, coe_singleton], rw is_clique_iff,split,
    rw set.pairwise_pair_of_symmetric,
    intro h,exact h2, exact G.symm, exact c2,
  rw clique_free_set, push_neg,use {v,w},split, 
  work_on_goal 1 { intros a ᾰ, dsimp at *, simp at *, cases ᾰ, work_on_goal 1 { induction ᾰ, assumption }, induction ᾰ, assumption }, assumption,
end

-- inductive step: if A is (t.succ+2)-clique free then for any v ∈ A the restricted nbhd of v in A is (t+2)-clique-free
lemma t_clique_free {A: finset α}{v :α}(hA : G.clique_free_set A (t.succ+2)) (hv : v∈A) :
G.clique_free_set (G.nbhd_res v A) (t+2):=
begin
  rw clique_free_set,
  intros B hB, contrapose! hA,
  rw clique_free_set,push_neg,
  set C:= B ∪ {v} with hC,
  have ct:  C.card = t.succ +2,{
    rw hC, rw nat.succ_eq_add_one,rw add_assoc,rw add_comm 1, rw ← add_assoc,
    convert card_union_eq _, rw is_n_clique_iff at hA, exact hA.2.symm,
    rw disjoint_singleton_right , 
    simp only [eq_self_iff_true] at *,
    intros h, apply  (not_mem_res_nbhd G v A) (hB h),},
  have BA: B⊆ A:= subset_trans hB (G.sub_res_nbhd_A v A),
  use C, split,
  rw hC, apply union_subset BA _,
  simp only [hv, singleton_subset_iff],
  rw is_n_clique_iff at *,
  cases hA with cl ca, 
  split, rw is_clique_iff, rw set.pairwise,
  intros x hx y hy hne,
  by_cases x=v,
    have yB : y∈ G.neighbor_finset v, 
      rw hC at *,
      simp only [*, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, mem_coe, eq_self_iff_true,
      true_or, ne.def] at *,
      cases hy,exfalso, exact hne hy.symm, 
      exact (mem_of_mem_inter_right (hB hy)),
    rw h, rwa ← mem_neighbor_finset G v,
    by_cases h2:  y=v,
      rw h2, simp only [*, ne.def, not_false_iff, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, eq_self_iff_true,
      mem_coe, true_or, false_or] at *,
      rw adj_comm,
      rw ← mem_neighbor_finset G v,
      exact mem_of_mem_inter_right (hB hx),
    simp only [*, ne.def, coe_union, coe_singleton, set.union_singleton, set.mem_insert_iff, mem_coe, false_or, eq_self_iff_true] at *,
    exact cl hx  hy hne,
  exact ct,
end

-- restricted degree additive over partition of A into B ∪ A\B
lemma sum_sdf {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A): ∑ v in A, G.deg_res v C = ∑v in B, G.deg_res v C + ∑ v in A\B, G.deg_res v C:=
begin
  nth_rewrite 0 ← union_sdiff_of_subset hB,
  exact sum_union (disjoint_sdiff),
end

-- restricted deg over A = restricted deg over B + restricted deg over A\B
lemma deg_res_add  {v:α}{A B : finset α} (hB: B ⊆ A) (hv: v ∈ A): G.deg_res v A=  G.deg_res v B+  G.deg_res v (A\B):=
begin
 simp [deg_res,nbhd_res], nth_rewrite 0 ← union_sdiff_of_subset hB, 
 convert card_disjoint_union _,ext, simp only [union_sdiff_self_eq_union, mem_inter, mem_union, mem_neighbor_finset, mem_sdiff] at *, tauto,
 apply_instance, intros a ᾰ, dsimp at *, simp at *, cases ᾰ, cases ᾰ_right, cases ᾰ_right_right, cases ᾰ_right_right_left, solve_by_elim,
end

-- restricted deg add sum
lemma deg_res_add_sum {A B C : finset α} (hB: B ⊆ A) (hC: C⊆ A) : ∑ v in C, G.deg_res v A=  ∑ v in C, G.deg_res v B+  ∑ v in C,G.deg_res v (A\B):=
begin
  rw ← sum_add_distrib, apply finset.sum_congr rfl _, intros x hx, exact G.deg_res_add hB (hC hx),
end

-- counting edges exiting B via ite helper
lemma bip_count_help {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in B, ∑ w in A\B,ite (G.adj v w) 1 0:=
begin
  simp only [deg_res_ones], congr,ext x, simp  [deg_res_ones],congr, ext, 
  rw [mem_res_nbhd,mem_filter,mem_neighbor_finset],
end

-- edges from B to A\B equals edges from A\B to B
lemma bip_count {A B : finset α} (hB: B ⊆ A) : ∑ v in B, G.deg_res v (A\B) = ∑ v in A\B, G.deg_res v B:=
begin
  rw G.bip_count_help hB,
  have: A\(A\B)=B:=sdiff_sdiff_eq_self hB,
  conv { to_rhs,congr, skip,rw ← this,},
  rw [G.bip_count_help (sdiff_subset A B),this],
  rw sum_comm, congr, ext y, congr,ext x, 
  split_ifs,refl,exfalso, rw adj_comm at h, exact h_1 h, 
  exfalso, rw adj_comm at h, exact h h_1,refl,
end

-- sum of res_res_deg ≤ sum of res_deg 
lemma sum_res_le {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A): ∑ v in C, G.deg_res v B ≤ ∑v in C, G.deg_res v A :=
begin
  apply sum_le_sum _,
  intros i hi, 
  rw [deg_res,deg_res], apply card_le_of_subset _,
  intros x hx, rw [mem_res_nbhd] at *,
  exact ⟨hB hx.1, hx.2⟩,
end

-- main theorem basically erdos proof of degree majorisation of (t+2)-clique-free graph by (t+1)-partite graph
theorem erdos : ∀A:finset α, G.clique_free_set A (t+2) → ∑v in A,G.deg_res v A ≤ 2*(turan_numb t A.card):=
begin
  induction t with s hs,
  intros A hA,
  rw tn_simp', 
  rw mul_zero, rw zero_add at hA, 
  have two: ∀v∈A, G.deg_res v A= 0:= G.two_clique_free hA,
  simp only [nonpos_iff_eq_zero, sum_eq_zero_iff], exact two, 
  intros A hA, 
  dsimp at *, 
  by_cases hnem: A.nonempty,{
    obtain ⟨x,hxA,hxM⟩:=G.exists_max_res_deg_vertex hnem,
    have hBc :G.clique_free_set (G.nbhd_res x A) (s+2):=G.t_clique_free hA hxA,
    specialize hs (G.nbhd_res x A) hBc,
    set B: finset α := (G.nbhd_res x A) with hBd, 
    have hBA: B⊆ A:=(G.sub_res_nbhd_A x A),
    rw [G.deg_res_add_sum hBA (subset_refl A),G.sum_sdf hBA hBA, add_assoc],
    apply add_le_of_add_le_right _ hs,
    rw [G.sum_sdf hBA (sdiff_subset A B),G.bip_count hBA,← G.deg_res_add_sum hBA (sdiff_subset A B)],
    nth_rewrite 1 add_comm,
    rw ← add_assoc,
    have over:=G.sum_res_le hBA (sdiff_subset A B),
    apply add_le_of_add_le_left _ over,
    ring_nf, rw ← mul_add,
    refine mul_le_mul' _ _, refl,
    have maxbd:=G.max_deg_res_sum_le (sdiff_subset A B),
    apply add_le_of_add_le_left _ maxbd, rw hxM,
    rw G.deg_res_eq_card_of_ss  hBd,
    have BssA: B⊂A,{
      convert (ssubset_iff_of_subset hBA).mpr _,
      use x, split , exact hxA,
      rw hBd, exact G.not_mem_res_nbhd x A, 
    },
    exact turan_bd s hnem hBA BssA,},
    -- ¬ A.nonempty ie A = ∅
  {  rw not_nonempty_iff_eq_empty at hnem, 
    rw [hnem,finset.card_empty,turan_numb, mul_zero,finset.sum_empty],},
end

-- usual-ish statement of turan upper bound
theorem turan_ub : G.clique_free (t+2) → G.edge_finset.card ≤ turan_numb t (card α):=
begin
  intro h,
  have ucf:=G.clique_free_graph_imp_set h,
  have sdG:= G.erdos univ ucf,
  simp [deg_res_univ] at sdG,
  rw sum_degrees_eq_twice_card_edges at sdG, rw card_univ at sdG, rwa [mul_le_mul_left] at sdG, by norm_num,
end

end simple_graph