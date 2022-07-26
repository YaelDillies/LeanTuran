import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import multipartite
import tactic.core
import turan1
import algebra.big_operators


open finset nat

open_locale big_operators 

namespace simple_graph
-- t_n t n is the maximum number of edges in a (t+2)-clique free graph of order n
-- or equivalently the maximum numb of edges in a complete (t+1)-partite graph order n
-- or equivalently .... 
def t_n : ℕ → ℕ → ℕ:=
begin
  intros t n,
  set a:= n/(t+1),--- size of a small part
  set b:= n-(t+1)*a,-- number of large parts
  exact (a^2)*nat.choose(t+1-b)(2)+a*(a+1)*b*(t+1-b)+((a+1)^2)*nat.choose(b)(2),
end


--variables {t n : ℕ} 
-- turan_numb t n is max numb of edges in an n vertex t+1 partite graph 
---what about 0-partite? sorry not going there...
def turan_numb : ℕ → ℕ → ℕ
| _       0 := 0
| 0       _ := 0
| (t+1) (n+1) :=option.get_or_else ((range(n+1)).image(λa, turan_numb t a + a*(n+1-a))).max 0 


lemma tn_simp (t :ℕ): turan_numb t 0 = 0 := by cases t;refl

lemma tn_simp' (n :ℕ): turan_numb 0 n = 0 := by cases n;refl

--the turan number is the maximum of the lhs below 
lemma tn_le (t c n : ℕ) (h: c ∈ range (n+1)): turan_numb t c +c*(n+1-c) ≤ turan_numb (t+1) (n+1):=
begin
  obtain ⟨x, hx : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have := finset.le_max_of_mem (mem_image_of_mem _ h) hx,
  rw [turan_numb, hx], apply le_trans this,refl,
end

-- obtain the optimal choice of size of new part in turan graph T (t+1)(n+1)
lemma tn_max_mem (t c n : ℕ) (h: c∈ range (n+1)) : ∃ b ∈ range(n+1), turan_numb t b +b*(n+1-b) = turan_numb (t+1) (n+1):=
begin
  obtain ⟨i, hi : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have := mem_of_max  hi,
  rw mem_image at this,
  rcases this with ⟨b,hbr,hbm⟩,
  use [b,hbr],
  rw [turan_numb, hi, hbm],refl,
end


variables {t n : ℕ} 
variables {α : Type*} (G : simple_graph α)[fintype α][inhabited α]{s : finset α}[decidable_eq α][decidable_rel G.adj]

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
    rw [G.deg_res_add_sum hBA ,G.sum_sdf hBA hBA, add_assoc],
    -- apply inductive hyp to ∑ v ∈ B, deg_B v using the fact that 
    -- res nbhd of x to B = is (s+2)-clique free (since A is (s.succ+2)-clique free)
    apply add_le_of_add_le_right _ (hs (G.nbhd_res x A) (G.t_clique_free hA hxA)),
    -- use ∑ v ∈ A, deg_(A\B) v = ∑ v ∈ A\B, deg_A v
    rw [G.sum_sdf hBA (sdiff_subset A B),G.bip_count hBA,← G.deg_res_add_sum hBA ],
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



-- usual-ish statement of turan upper bound
theorem turan_ub : G.clique_free (t+2) → G.edge_finset.card ≤ turan_numb t (fintype.card α):=
begin
  intro h,
  have sdG:= G.erdos_simple univ (G.clique_free_graph_imp_set h),
  simp only [deg_res_univ] at sdG,
  rwa [sum_degrees_eq_twice_card_edges,card_univ,mul_le_mul_left] at sdG, by norm_num,
end





-- t_n t n is the maximum number of edges in a (t+2)-clique free graph of order n
-- or equivalently the maximum numb of edges in a complete (t+1)-partite graph order n
-- or equivalently .... 
def t_n : ℕ → ℕ → ℕ:=
begin
  intros t n,
  set a:= n/(t+1),--- size of a small part
  set b:= n-(t+1)*a,-- number of large parts
  exact (a^2)*nat.choose(t+1-b)(2)+a*(a+1)*b*(t+1-b)+((a+1)^2)*nat.choose(b)(2),
end


--variables {t n : ℕ} 
-- turan_numb t n is max numb of edges in an n vertex t+1 partite graph 
---what about 0-partite? sorry not going there...
def turan_numb : ℕ → ℕ → ℕ
| _       0 := 0
| 0       _ := 0
| (t+1) (n+1) :=option.get_or_else ((range(n+1)).image(λa, turan_numb t a + a*(n+1-a))).max 0 


lemma tn_simp (t :ℕ): turan_numb t 0 = 0 := by cases t;refl

lemma tn_simp' (n :ℕ): turan_numb 0 n = 0 := by cases n;refl

--the turan number is the maximum of the lhs below 
lemma tn_le (t c n : ℕ) (h: c ∈ range (n+1)): turan_numb t c +c*(n+1-c) ≤ turan_numb (t+1) (n+1):=
begin
  obtain ⟨x, hx : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have := finset.le_max_of_mem (mem_image_of_mem _ h) hx,
  rw [turan_numb, hx], apply le_trans this,refl,
end

-- obtain the optimal choice of size of new part in turan graph T (t+1)(n+1)
lemma tn_max_mem (t c n : ℕ) (h: c∈ range (n+1)) : ∃ b ∈ range(n+1), turan_numb t b +b*(n+1-b) = turan_numb (t+1) (n+1):=
begin
  obtain ⟨i, hi : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have := mem_of_max  hi,
  rw mem_image at this,
  rcases this with ⟨b,hbr,hbm⟩,
  use [b,hbr],
  rw [turan_numb, hi, hbm],refl,
end


-- inductive step for Erdos proof: if A is (t.succ+2)-clique free then for any v ∈ A the restricted nbhd of v in A is (t+2)-clique-free
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
    rw [G.deg_res_add_sum hBA ,G.sum_sdf hBA hBA, add_assoc],
    -- apply inductive hyp to ∑ v ∈ B, deg_B v using the fact that 
    -- res nbhd of x to B = is (s+2)-clique free (since A is (s.succ+2)-clique free)
    apply add_le_of_add_le_right _ (hs (G.nbhd_res x A) (G.t_clique_free hA hxA)),
    -- use ∑ v ∈ A, deg_(A\B) v = ∑ v ∈ A\B, deg_A v
    rw [G.sum_sdf hBA (sdiff_subset A B),G.bip_count hBA,← G.deg_res_add_sum hBA ],
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


-- usual-ish statement of turan upper bound
theorem turan_ub : G.clique_free (t+2) → G.edge_finset.card ≤ turan_numb t (fintype.card α):=
begin
  intro h,
  have sdG:= G.erdos_simple univ (G.clique_free_graph_imp_set h),
  simp only [deg_res_univ] at sdG,
  rwa [sum_degrees_eq_twice_card_edges,card_univ,mul_le_mul_left] at sdG, by norm_num,
end



end simple_graph