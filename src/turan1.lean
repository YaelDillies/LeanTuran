import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import multipartite
import mpartition
import tactic.core
import algebra.big_operators


open finset nat mpartition

open_locale big_operators 

namespace simple_graph
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

lemma sdiff_inter_disj (A B C:finset α) : disjoint (B ∩ C)  (A\B ∩ C):=
begin
 have d1:disjoint (B ∩ C) (A\(B ∩ C)):= sdiff_disjoint.symm,
 convert disjoint_of_subset_right _ d1,
 intros x hx, rw mem_inter at hx,
 rw [mem_sdiff,mem_inter] at *, push_neg, refine ⟨hx.1.1,_⟩, intro hb, exfalso, exact hx.1.2 hb,
end




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


lemma clique_free_card_lt {A : finset α} {s: ℕ} (h: A.card <s): G.clique_free_set A s:=
begin
  rw clique_free_set,intros B hB,rw is_n_clique_iff,push_neg,intro h1,
  apply ne_of_lt (lt_of_le_of_lt (card_le_of_subset hB) h), 
end

lemma clique_free_empty {s : ℕ} (h: 0< s): G.clique_free_set ∅ s:=
begin
  have:=finset.card_empty, rw ← this at h, exact G.clique_free_card_lt h,
end


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
  intros v hv, rw [deg_res,card_eq_zero], 
  contrapose hA,
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

-- sum of degrees over an independent set (2-clique-free set) is 0
lemma two_clique_free_sum {A: finset α} (hA : G.clique_free_set A 2) : ∑ v in A, G.deg_res v A = 0:=
begin
  rw sum_eq_zero_iff, exact G.two_clique_free hA,
end


-- if A set is (t+2)-clique-free then any member vertex 
-- has restricted nbhd that is (t+1)-clique-free 
lemma t_clique_free {A: finset α} {v :α}(hA : G.clique_free_set A (t + 2)) (hv : v ∈ A) :
G.clique_free_set (G.nbhd_res v A) (t + 1):=
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
    have: 2=1+1:=by norm_num,
    rw [hC,this, ← add_assoc],
    convert card_union_eq _,  exact hA.2.symm,
    rw disjoint_singleton_right, 
    intros h, apply  (not_mem_res_nbhd G v A) (hB h),
end


-- restricted degree additive over partition of A into B ∪ A\B
lemma sum_sdf {A B C: finset α} (hB: B ⊆ A) (hC: C ⊆ A):
 ∑ v in A, G.deg_res v C = ∑v in B, G.deg_res v C + ∑ v in A\B, G.deg_res v C:=
begin
  nth_rewrite 0 ← union_sdiff_of_subset hB, exact sum_union (disjoint_sdiff),
end


-- restricted deg over A = restricted deg over B + restricted deg over A\B
lemma deg_res_add  {v : α} {A B : finset α} (hB: B ⊆ A): G.deg_res v A=  G.deg_res v B +  G.deg_res v (A\B):=
begin
  simp [deg_res,nbhd_res], nth_rewrite 0 ← union_sdiff_of_subset hB, 
  convert card_disjoint_union _,
  exact inter_distrib_right B (A\B) _,
  exact sdiff_inter_disj A B _,
end

lemma deg_res_add'  {v : α} {A B : finset α} (h: disjoint A B): G.deg_res v (A∪B)=  G.deg_res v A +  G.deg_res v B:=
begin
  simp [deg_res,nbhd_res],  
  convert card_disjoint_union _,
  exact inter_distrib_right _ _ _,
  have da:A∩G.neighbor_finset v⊆A:=inter_subset_left _ _,
  have db:B∩G.neighbor_finset v⊆B:=inter_subset_left _ _,
  apply disjoint_of_subset_left da, exact disjoint_of_subset_right db h,
end
 
lemma deg_res_add_sum' {A B C: finset α} (h: disjoint A B) : ∑ v in C, G.deg_res v (A ∪ B) = ∑ v in C, G.deg_res v A +∑ v in C, G.deg_res v B:=
begin
 rw ← sum_add_distrib, apply finset.sum_congr rfl _, intros x hx, exact G.deg_res_add' h ,
end

-- restricted deg add sum
lemma deg_res_add_sum {A B C : finset α} (hB: B ⊆ A) : ∑ v in C, G.deg_res v A=  ∑ v in C, G.deg_res v B+  ∑ v in C,G.deg_res v (A\B):=
begin
  rw ← sum_add_distrib, apply finset.sum_congr rfl _, intros x hx, exact G.deg_res_add hB ,--(hC hx),
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

lemma bip_count_help' {A B : finset α}  (hB: disjoint A B ) : ∑ v in B, G.deg_res v A = ∑ v in B, ∑ w in A, ite (G.adj v w) 1 0:=
begin
  simp only [deg_res_ones], congr,ext x, simp only [sum_const, algebra.id.smul_eq_mul, mul_one, sum_boole, cast_id], 
  congr, ext, rw [mem_res_nbhd,mem_filter,mem_neighbor_finset],
end

-- edges from A to B (disjoint) equals edges from B to A
lemma bip_count' {A B : finset α} (hB: disjoint A B ) : ∑ v in B, G.deg_res v A = ∑ v in A, G.deg_res v B:=
begin
  rw G.bip_count_help' hB, rw G.bip_count_help' hB.symm,rw sum_comm, congr,
  ext y, congr,ext x, 
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


-- vertices in new part are adjacent to all old vertices
--- should have used lemmas from multipartite for this...
lemma mp_com (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∀v∈C, (mp (insert M h)).deg_res v M.A=(M.A.card):=
begin
 intros v hv, rw deg_res, congr, ext,
 rw mem_res_nbhd,split,intro h, exact h.1,
 intros ha, refine ⟨ha,_⟩, rw mem_neighbor_finset, dsimp,
 obtain⟨j,hjr,hjm⟩ :=inv_part ha,
 use j,rw insert_t, 
 refine ⟨_,_,_⟩, rw mem_range at *,linarith [hjr], exact M.t+1, use self_mem_range_succ _,
 split, intro jc,rw jc at hjr, exact not_mem_range_self hjr,right, rw insert_P,
 split_ifs,exfalso, exact h_1 rfl,rw insert_P, refine ⟨hv,_⟩,split_ifs,exact hjm,
 push_neg at h_2,exfalso, rw h_2 at hjr,  exact not_mem_range_self hjr,
end




lemma mp_old_adj (M :multi_part α) {C : finset α} {v w :α}(h: disjoint M.A C) : v∈ M.A → w ∈ M.A → ((mp M).adj v w ↔ (mp (insert M h)).adj v w):=
begin
  intros hv hw,
  split,intro hins,   obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,
  use k, rw insert_t,rw mem_range at *, refine ⟨_,_,_,_,_⟩, linarith, exact l,
  rw mem_range,linarith [hlr],exact lnek, simp [insert_P],
  split_ifs,exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr,
  exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr,
  exfalso,rw ← h_2 at hlr, exact lt_irrefl l hlr,
  exact lkc,
  intro hins, obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,rw insert_t at hkr,rw insert_t at hlr,
  refine ⟨k,_,l,_,lnek,_⟩, 
  rw mem_range at *,
  by_contra h', have :k=M.t+1:=by linarith [hkr,h],
  cases lkc, rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
  exact h vinb, rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
  exact h vinb,
  rw mem_range at *,
  by_contra h', have :l=M.t+1:=by linarith [hlr,h],
  cases lkc, rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
  exact h vinb, rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
  exact h vinb,
  cases lkc, rw [insert_P,insert_P] at lkc, split_ifs at lkc,left, exact lkc,
  exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb,
  exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb,
  exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb,
  rw [insert_P,insert_P] at lkc, split_ifs at lkc,right, exact lkc,
  exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb,
  exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb,
  exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb,
end


lemma mp_old' (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).nbhd_res v M.A=(mp M).nbhd_res v M.A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  intros v hv,ext,split,intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
  rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (H.mp_old_adj M h hv ha.1).mpr ha.2,
  intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
  rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (H.mp_old_adj M h hv ha.1).mp ha.2,
end

lemma mp_old (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).deg_res v M.A=(mp M).deg_res v M.A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  intros v hv, rw deg_res,rw deg_res,  rw H.mp_old' M h v hv,
end

lemma mp_ind (M : multi_part α) {v w :α} {C :finset α} (h: disjoint M.A C) : v∈C → w∈C →  ¬(mp (insert M h)).adj v w:=
begin
  intros hv hw,   have vin:= insert_P' M h v hv,
  have win:= insert_P' M h w hw,
  have :=self_mem_range_succ (M.t+1), rw ← insert_t M h at this,
  contrapose win,push_neg at win, exact not_nhbr_same_part this vin win,
end

lemma mp_ind' (M : multi_part α) {C :finset α} (h: disjoint M.A C) : ∀v∈C,(mp (insert M h)).deg_res v C=0:=
begin
  intros v hv, rw deg_res, rw card_eq_zero, by_contra h', 
  obtain ⟨w,hw,adw⟩ :=(mp (insert M h)).exists_mem_nempty h',exact (((mp (insert M h))).mp_ind M h hv hw) adw, 
end

lemma mp_ind_sum (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∑ v in C, (mp (insert M h)).deg_res v C=0:=
begin
  simp only [sum_eq_zero_iff], intros x hx, exact (mp (insert M h)).mp_ind' M h x hx,
end

lemma mp_old_sum (M :multi_part α) {C : finset α} (h: disjoint M.A C) :∑ v in M.A, (mp (insert M h)).deg_res v M.A= ∑ v in M.A,(mp M).deg_res v M.A:=
begin
  set H: simple_graph α:= (mp (insert M h)), apply sum_congr rfl,exact (H.mp_old M h),
end
--- counting edges in multipartite graph  
--- if we add in a new part C then the sum of degrees over new vertex set
--  is sum over old + 2 edges in bipartite join

lemma mp_count (M : multi_part α) {C :finset α} (h: disjoint M.A C) :∑v in M.A, (mp M).deg_res v M.A +2*(M.A.card)*C.card =
∑ v in (insert M h).A, (mp (insert M h)).deg_res v (insert M h).A:=
begin
  set H: simple_graph α:= (mp (insert M h)),
  simp  [ insert_AB], rw sum_union h, rw [H.deg_res_add_sum' h,H.deg_res_add_sum' h],
  rw add_assoc, rw H.mp_ind_sum M h, rw add_zero, rw H.bip_count' h.symm,
  rw ← sum_add_distrib, rw card_eq_sum_ones C,rw mul_sum, rw H.mp_old_sum M h,
  rw [add_right_inj],apply sum_congr rfl, 
  rw (by norm_num: 2= 1+1),rw add_mul,  rw one_mul,rw mul_one, intros x hx, rwa (H.mp_com M h x hx),
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





---for any (t+2)-clique free set there is a partition into B, a (t+1)-clique free set and A\B 
-- such that e(A)+e(A\B) ≤ e(B) + |B|(|A|-|B|) 

lemma furedi_help : ∀A:finset α, G.clique_free_set A (t+2) → ∃B:finset α, B ⊆ A ∧ G.clique_free_set B (t+1) ∧ 
∑v in A, G.deg_res v A + ∑ v in (A\B), G.deg_res v (A\B) ≤ ∑ v in B, G.deg_res v B + 2*B.card * (A\B).card:=
begin
  cases nat.eq_zero_or_pos t with ht,
  intros A hA,rw ht at *, rw zero_add at *,
----- t = 0 need to check that ∅ is not a 1-clique. 
  refine ⟨∅,⟨empty_subset A,(G.clique_free_empty (by norm_num: 0 <1)),_⟩⟩,
  rw [sdiff_empty, card_empty, mul_zero,zero_mul, sum_empty, zero_add,G.two_clique_free_sum hA],
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
    rw [sdiff_empty, card_empty, mul_zero,zero_mul, sum_empty, zero_add,hnem,sum_empty],},
end


-- if A is (t+2)-clique-free then there exists a (t+1)-partition of M of A so that 
-- e(A) +∑ i≤t, e(A_i) ≤ e(complete_multi_partite M)
-- (Note either A is contained in M or we need to remove edges from inside parts
-- so this implies that if e(A)=max e(M)-s then it can be made (t+1)-partite by
-- removing at most s edges)
lemma furedi : ∀A:finset α, G.clique_free_set A (t+2) → ∃M:multi_part α, M.A=A ∧ M.t =t ∧ 
∑v in A, G.deg_res v A + ∑ i in range(M.t+1),∑ v in (M.P i), G.deg_res v (M.P i) ≤ ∑ v in A, (mp M).deg_res v A:=
begin
  induction t with t ht, rw zero_add,
  intros A ha, use (default_M A 0), refine ⟨rfl,rfl,_⟩, rw G.two_clique_free_sum ha,
  rw zero_add, unfold default_M, dsimp,simp, apply sum_le_sum,
  intros x hx, rw G.two_clique_free ha x hx,exact zero_le _,
  --- t.succ case
  intros A ha, obtain⟨B,hBa,hBc,hBs⟩:=G.furedi_help A ha,  
  obtain ⟨M,Ma,Mt,Ms⟩:=ht B hBc,
  have dAB:disjoint M.A (A\B), {rw Ma, exact disjoint_sdiff,},
  set H: simple_graph α:= (mp (insert M dAB)),
  use (insert M dAB), refine ⟨_,_,_⟩,  
  rw [insert_AB, Ma], exact union_sdiff_of_subset hBa, rw [insert_t, Mt],
  --- so we now have the new partition and "just" need to check the degree sum bound..
  -- START HERE and make the next line work.
  have mpc:=H.mp_count M dAB, rw insert_AB at mpc,
  simp  [insert_P,insert_t], 
  
  sorry,
end

end simple_graph
