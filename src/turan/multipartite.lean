import data.nat.choose.basic
import tactic.linarith
import mathlib.combinatorics.simple_graph.multipartite
import mathlib.data.set.equitable
import mathlib.order.partition.equipartition

open finset nat
open_locale big_operators

namespace simple_graph
variables {t : ℕ} {α : Type*} [fintype α] [nonempty α] [decidable_eq α] {A : finset α}
  {P : finpartition A}

-- given a t partition on A form the complete multi-partite graph on A
-- with all edges present between different parts in M.A and no edges involving vertices outside A or inside any part of A

-- --any vertex in α but not in A is isolated
-- lemma no_nbhrs {P : finpartition A} {v w: α} (hA: v∉M.A) : ¬(M.multipartite_graph).adj v w:=
-- begin
--   contrapose! hA,
--   obtain ⟨i,hi,j,hj,ne,hv⟩:=hA, cases hv, {exact (sub_part hi) hv.1},
--   {exact (sub_part hj) hv.1},
-- end

-- -- having any neighbour implies the vertex is in A
-- lemma nbhrs_imp {P : finpartition A} {v w: α} : (M.multipartite_graph).adj v w → v ∈ M.A:=
-- begin
--   intros h1, by_contra, exact no_nbhrs h h1,
-- end

-- -- if v in P i  and w in A\(P i) then vw is an edge
-- lemma nbhr_diff_parts {P : finpartition A} {v w: α} {i : ℕ} (hi : i∈ range(M.t)) (hv: v∈ M.P i) (hw : w∈ M.A\M.P i)
--  : (M.multipartite_graph).adj v w:=
-- begin
--   rw mem_sdiff at hw,
--   cases hw with hA hni,
--   rw M.uni at hA, rw mem_bUnion at hA,
--   obtain ⟨j,hj1,hj2⟩:=hA,
--   refine mp_imp_adj hi hj1 hv hj2 _, intro h, rw h at hni, exact hni hj2
-- end

-- --if v is in P i then its nbhd is A\(P i)
-- lemma mp_nbhd {P : finpartition A} {v:α} {i: ℕ} (hv: i∈ range(M.t) ∧ v ∈ M.P i) : (M.multipartite_graph).neighbor_finset v = (M.A)\(M.P i) :=
-- begin
--   ext,split,{rw mem_neighbor_finset,intro h, rw adj_comm at h,
--   rw mem_sdiff, refine  ⟨nbhrs_imp h,_⟩, exact not_nbhr_same_part hv.1 hv.2 h.symm},
--   {rw mem_neighbor_finset, exact nbhr_diff_parts hv.1 hv.2},
-- end

-- -- degree sum over all vertices i.e. 2*e(M.multipartite_graph)
-- def mp_dsum (P : finpartition A) : ℕ:= ∑ v in M.A, (M.multipartite_graph).degree v

-- -- degree of vertex in P i is card(A\P i)
-- lemma mp_deg {P : finpartition A} {v : α} {i: ℕ} (hv: i∈ range(M.t) ∧ v∈ M.P i) : (M.multipartite_graph).degree v = ((M.A)\(M.P i)).card:=
-- begin
--   rw degree,rwa mp_nbhd hv,
-- end

-- -- degree of v in P i as |A|- |P i|
-- lemma mp_deg_diff {P : finpartition A} {v : α} {i: ℕ} (hv: i∈ range(M.t) ∧ v∈ M.P i) : (M.multipartite_graph).degree v = M.A.card -  (M.P i).card:=
-- begin
--   rw mp_deg hv, exact card_sdiff (sub_part hv.1),
-- end

-- -- sum of degrees as sum over parts
-- lemma mp_deg_sum (P : finpartition A) : ∑ v in M.A, (M.multipartite_graph).degree v = ∑i in range(M.t),(M.P i).card * ((M.A)\(M.P i)).card :=
-- begin
--   nth_rewrite 0 M.uni,
--   rw sum_bUnion (pair_disjoint M), apply finset.sum_congr rfl _,
--   intros x hx, rw [finset.card_eq_sum_ones, sum_mul, one_mul], apply finset.sum_congr rfl _,
--   intros v hv, exact mp_deg ⟨hx,hv⟩,
-- end

-- --- same using squares of part sizes and avoiding the cursed tsubtraction
-- lemma mp_deg_sum_sq' (P : finpartition A) : ∑ v in M.A, (M.multipartite_graph).degree v + ∑i in range(M.t), (M.P i).card^2 = M.A.card^2:=
-- begin
--   rw mp_deg_sum M, rw pow_two, nth_rewrite 0 card_uni, rw ← sum_add_distrib, rw sum_mul,
--   refine finset.sum_congr rfl _,
--   intros x hx,rw pow_two,rw ← mul_add, rw card_part_uni hx,
-- end

-- -- expressed  as |A|^2- ∑ degrees squared
-- lemma mp_deg_sum_sq (P : finpartition A) : ∑ v in M.A, (M.multipartite_graph).degree v = M.A.card^2 - ∑i in range(M.t), (M.P i).card^2
-- :=eq_tsub_of_add_eq (mp_deg_sum_sq' M)

-- -- turan_partition partition corresponds to balanced partition sizes so if we have two turan_partition partitions
-- -- of same set A into the same number of parts then their degree sums are the the same
-- lemma turan_partition_deg_sum_eq (M N : finpartition A): M.A= N.A → M.t=N.t → P.is_equipartition → turan_partition N → mp_dsum M = mp_dsum N:=
-- begin
--    intros hA ht iM iN, unfold mp_dsum,  rw [mp_deg_sum_sq,mp_deg_sum_sq,hA], rw [turan_partition_iff_not_moveable, ¬ P.is_equipartition,not_not] at *,
--    apply congr_arg _,
--    have hN:= turan_bal iN, rw [← ht , ← hA] at hN,
--    have:= bal_turan_help' (turan_bal iM) hN, rwa ← ht,
-- end

-- -- this is the part of the degree sum that has changed by moving a vertex
-- lemma mp_deg_sum_move_help{P : finpartition A} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t) ∧ v ∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) (hc: (M.P j).card+1<(M.P i).card ) :
-- (M.P i).card * ((M.A)\(M.P i)).card + (M.P j).card * ((M.A)\(M.P j)).card <((move M hvi hj).P i).card * (((move M hvi hj).A)\((move M hvi hj).P i)).card + ((move M hvi hj).P j).card * (((move M hvi hj).A)\((move M hvi hj).P j)).card:=
-- begin
--   rw [move_Pcard hvi hj hvi.1,  move_Pcard hvi hj hj.1, move_Pcard_sdiff hvi hj hvi.1,  move_Pcard_sdiff hvi hj hj.1],
--   split_ifs,{exfalso, exact h.1 rfl},{exfalso, exact h.1 rfl},{exfalso, exact h.1 rfl},{exfalso, exact h_1.2 rfl},{exfalso, exact hj.2 h_2},
--   {rw card_sdiff (sub_part hvi.1), rw card_sdiff (sub_part hj.1),
--   exact move_change hc (two_parts hvi.1  hj.1 hj.2.symm)},
-- end

-- -- this is the part of the degree sum that hasn't changed by moving a vertex
-- lemma mp_deg_sum_move_help2{P : finpartition A} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t) ∧ v ∈ M.P i) (hj : j∈range(M.t) ∧ j≠i)  :
-- ∑ (x : ℕ) in ((range (M.t + 1)).erase j).erase i, ((move M hvi hj).P x).card * ((move M hvi hj).A \ (move M hvi hj).P x).card =
-- ∑ (y : ℕ) in ((range (M.t + 1)).erase j).erase i, (M.P y).card*((M.A\(M.P y)).card):=
-- begin
--   apply sum_congr rfl _, intros k hk, rw move_Pcard hvi hj, rw move_Pcard_sdiff hvi hj,split_ifs,{refl},
--   {exfalso, rw h_1 at hk,exact not_mem_erase i _ hk}, {exfalso,push_neg at h, simp only [*, ne.def, not_false_iff, mem_erase, eq_self_iff_true] at *},
--   {exact mem_of_mem_erase (mem_of_mem_erase hk)},   {exact mem_of_mem_erase (mem_of_mem_erase hk)},
-- end

-- -- given a vertex v ∈ P i and a part P j such that card(P j)+1 < card(P i) then moving v from Pi to Pj will increase the sum of degrees
-- -- putting the two previous lemmas together tells us that the move has increased the degree sum
-- lemma mp_deg_sum_move {P : finpartition A} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t) ∧ v ∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) (hc: (M.P j).card+1<(M.P i).card ) :
-- ∑ w in M.A,  (M.multipartite_graph).degree w < ∑ w in (move M hvi hj).A,  (mp (move M hvi hj)).degree w :=
-- begin
--   rw [mp_deg_sum M,mp_deg_sum (move M hvi hj), (move_t hvi hj)],
--   rw [← sum_erase_add (range(M.t)) _ hj.1,← sum_erase_add (range(M.t)) _ hj.1],
--   rw ← sum_erase_add ((range(M.t)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1),
--   rw ← sum_erase_add ((range(M.t)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1),
--   rw mp_deg_sum_move_help2,
--   rw [add_assoc,add_assoc], refine (add_lt_add_iff_left _).mpr _ , exact mp_deg_sum_move_help hvi hj hc,
-- end

-- -- equivalently moving v from P i to P j reduces sum of sum_sq_c of part sizes (basically edges in the complement of mp)
-- lemma sum_sq_c_dec (P : finpartition A) {v : α} {i j: ℕ}  (hvi: i∈ range(M.t) ∧ v ∈ M.P i) (hj : j∈range(M.t) ∧ j≠i) (hc: (M.P j).card+1<(M.P i).card ) :
-- sum_sq_c (move M hvi hj) < sum_sq_c M:=
-- begin
--   unfold sum_sq_c,
--   have h3:=mp_deg_sum_move hvi hj hc,
--   have h1:=mp_deg_sum_sq' M,   have h2:=mp_deg_sum_sq' (move M hvi hj), rw [move_A, move_t] at *,
--   rw ← h2 at h1, rw move_t, linarith,
-- end

-- -- Given any partition M we can find a turan_partition on the same set with the same number of parts.
-- lemma moved (P : finpartition A) : ∃ N:multi_part  α, N.A = M.A ∧ N.t = M.t ∧ turan_partition N ∧ mp_dsum M ≤ mp_dsum N:=
-- begin
--   apply well_founded.recursion (measure_wf sum_sq_c) M,
--   intros X h,
--   by_cases h': turan_partition X,{exact ⟨X,rfl,rfl,h', le_rfl⟩,},{
--     obtain ⟨i,hi,j,hj,v,hv,ne,hc⟩:=¬ P.is_equipartition.exists h',
--     set Y:=(move X ⟨hi,hv⟩ ⟨hj,ne⟩) with hY,
--     specialize h Y (sum_sq_c_dec X ⟨hi,hv⟩ ⟨hj,ne⟩ hc),
--     rw [move_t,move_A] at h, have :=mp_deg_sum_move  ⟨hi,hv⟩ ⟨hj,ne⟩ hc, rw [←mp_dsum,←mp_dsum,← hY] at this,
--     obtain ⟨N,h1,h2,h3,h4⟩:=h, refine ⟨N,h1,h2,h3,_⟩, exact le_trans (le_of_lt this) h4,},
-- end

-- -- Only Turan graphs maximize number of edges:
-- -- given a turan_partition and any other partition on the same set and into same number of parts
-- -- that is not-turan, the degree sum of the former is strictly larger
-- lemma moved_max (M N:finpartition A): M.A =N.A → M.t =N.t → P.is_equipartition →  ¬turan_partition N → mp_dsum N < mp_dsum M:=
-- begin
--   intros hA ht him h1,
--   obtain ⟨i,hi,j,hj,v,hv,ne,hc⟩:= ¬ P.is_equipartition.exists h1,
--   set O:=(move N ⟨hi,hv⟩ ⟨hj,ne⟩) with hO, have Ns:mp_dsum N < mp_dsum O:=mp_deg_sum_move ⟨hi,hv⟩ ⟨hj,ne⟩ hc,
--   obtain ⟨Q,QA,Qt,Qim,Qs⟩:=moved O, have :=turan_partition_deg_sum_eq M Q _ _ him Qim,rw this,
--   {exact lt_of_lt_of_le Ns Qs}, {rw [hA,QA], have NOA:N.A=O.A:=move_A ⟨hi,hv⟩ ⟨hj,ne⟩,exact NOA},
--   {rw[ht,Qt],  have NOt:N.t=O.t:=move_t ⟨hi,hv⟩ ⟨hj,ne⟩,exact NOt},
-- end

-- -- the degree sum of any complete t-partite graph is at most twice the turan numb of parts and set size
-- lemma turan_bound_M (P : finpartition A): mp_dsum M ≤ 2*turan_num M.t M.A.card:=
-- begin
--   obtain ⟨N,hA,ht,iN,sN⟩:=moved M,
--   apply le_trans sN _, apply le_of_eq,
--   rw turan_partition_iff_not_moveable at iN,rw ¬ P.is_equipartition at iN, rw not_not at iN,rw P' at iN, rw ← hA,rw ←ht,
--   have:= bal_turan_bd (turan_bal iN),
--   rw sum_sq at this, rw  mp_dsum,rw mp_deg_sum_sq, unfold P' at this,
--   rw [← this,  add_comm], simp only [add_tsub_cancel_right],
-- end

-- -- so if we have a partition of α then the number of edges is at most the turan number
-- lemma turan_max_edges (P : finpartition A): M.A=univ → (M.multipartite_graph).edge_finset.card ≤ turan_num M.t (fintype.card α):=
-- begin
--   intro hA, apply (mul_le_mul_left (by norm_num:0<2)).mp,
--   rw ← sum_degrees_eq_twice_card_edges, have:=turan_bound_M M,  unfold mp_dsum at this,rw hA at this,
--   rwa card_univ at this,
-- end

-- -- Now reformulate our bound to say that any complete multipartite graph on α that attains the turan bound is a turan_partition
-- lemma turan_eq_imp (P : finpartition A) (hu: M.A=univ):  (M.multipartite_graph).edge_finset.card = turan_num M.t (fintype.card α) → P.is_equipartition:=
-- begin
--   intros h, contrapose h, apply ne_of_lt, obtain ⟨N,NA,Nt,iN,le⟩:= moved M,
--   apply (mul_lt_mul_left (by norm_num:0<2)).mp, rw ←sum_degrees_eq_twice_card_edges,
--   have lt:=moved_max N M NA Nt iN h,
--   have le2:=turan_bound_M N, unfold mp_dsum at *, rw hu at *,rw NA at *,rw Nt at *,rw card_univ at *,
--   exact lt_of_lt_of_le lt le2,
-- end

-- -- finally need to verify that any turan partition does indeed attain the upper bound
-- lemma turan_imm_imp_eq (P : finpartition A) {t :ℕ} (hu: M.A=univ) (ht :M.t=t): P.is_equipartition → (M.multipartite_graph).edge_finset.card = turan_num t (fintype.card α) :=
-- begin
--   rw turan_partition_iff_not_moveable, unfold ¬ P.is_equipartition, rw not_not,
--   intros iM,  apply (nat.mul_right_inj (by norm_num:0<2)).mp, rw [←sum_degrees_eq_twice_card_edges, ←hu, ←ht],
--   rw [mp_deg_sum_sq,  ← card_univ, ← hu],
--   have cA:= card_uni M,
--   rwa [← bal_turan_bd (turan_bal iM),  sum_sq, P', add_tsub_cancel_left],
-- end

-- --- next few results for counting degrees in mp once a new part has been inserted.

-- -- vertices in new part are adjacent to all old vertices
-- --- should have used lemmas from multipartite for this...
-- -- this says that the degree of any vertex in the new part equals the sum over the old parts

-- lemma mp_com (P : finpartition A) {C :finset α} (h: disjoint M.A C) :∀ v ∈ C, (mp (insert M h)).deg_on v M.A=(M.A.card):=
-- begin
--  intros v hv, rw deg_on, congr, ext,
--  rw mem_res_nbhd, simp only [mem_neighbor_finset, mem_range, ne.def, exists_prop, and_iff_left_iff_imp],
--  intro ha, obtain⟨j,hjr,hjm⟩ :=inv_part ha,
--  use j,rw insert_t,
--  refine ⟨_,_,_,_,_⟩, {rw mem_range at *,linarith [hjr]}, {exact M.t},{linarith},
--  {intro eq, rw eq at hjr, exact not_mem_range_self hjr},
--  {right, rw insert_P, split_ifs,{exfalso, exact h_1 rfl},rw insert_P, refine ⟨hv,_⟩,split_ifs,{exact hjm},{
--  push_neg at h_2,exfalso, rw h_2 at hjr,  exact not_mem_range_self hjr},},
-- end

-- -- given two vertices in the old partition they are adjacent in the partition with
-- -- C inserted iff they were already adjacent
-- lemma mp_old_adj (M :finpartition A) {C : finset α} {v w :α}(h: disjoint M.A C) : v∈ M.A → w ∈ M.A → ((M.multipartite_graph).adj v w ↔ (mp (insert M h)).adj v w):=
-- begin
--   intros hv hw,
--   split,{intro hins, obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,
--   use k, rw insert_t,rw mem_range at *, refine ⟨(by linarith),l,_,lnek,_⟩,{
--   rw mem_range,linarith [hlr]},{simp [insert_P],
--   split_ifs,{exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr},
--   {exfalso,rw ← h_1 at hkr, exact lt_irrefl k hkr},
--   {exfalso,rw ← h_2 at hlr, exact lt_irrefl l hlr},
--   {exact lkc},},},
--   {intro hins, obtain⟨k,hkr,l,hlr,lnek,lkc⟩:=hins,rw insert_t at hkr,rw insert_t at hlr,
--   refine ⟨k,_,l,_,lnek,_⟩,{
--   rw mem_range at *,
--   by_contra h', have :k=M.t:=by linarith [hkr,h],
--   cases lkc,{ rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
--   exact h vinb}, {rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
--   exact h vinb},},{
--   rw mem_range at *,
--   by_contra h', have :l=M.t:=by linarith [hlr,h],
--   cases lkc, {rw this at lkc, have vinb:=mem_inter.mpr ⟨hw,insert_C M h lkc.2⟩,
--   exact h vinb},{ rw this at lkc, have vinb:=mem_inter.mpr ⟨hv,insert_C M h lkc.1⟩,
--   exact h vinb},},{
--   cases lkc, {rw [insert_P,insert_P] at lkc, split_ifs at lkc,{left, exact lkc},
--   {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},
--   {exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb},
--   {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},},{
--   rw [insert_P,insert_P] at lkc, split_ifs at lkc,{right, exact lkc},
--   {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},
--   {exfalso, have vinb:=mem_inter.mpr ⟨hv,lkc.1⟩,exact h vinb},
--   {exfalso, have winb:=mem_inter.mpr ⟨hw,lkc.2⟩,exact h winb},},},},
-- end

-- -- previous lemma interpreted in terms of res nbhds
-- lemma mp_old_nbhd_res (M :finpartition A) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).nbhd_res v M.A=(M.multipartite_graph).nbhd_res v M.A:=
-- begin
-- --  set H: simple_graph α:= (mp (insert M h)),
--   intros v hv,ext,split,{intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
--   rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (mp_old_adj M h hv ha.1).mpr ha.2},{
--   intros ha, rw mem_res_nbhd at *,refine ⟨ha.1,_⟩,
--   rw mem_neighbor_finset,rw mem_neighbor_finset at ha, exact (mp_old_adj M h hv ha.1).mp ha.2},
-- end

-- -- .. and in terms of deg res
-- lemma mp_old_deg_on (M :finpartition A) {C : finset α} (h: disjoint M.A C) :∀v∈M.A, (mp (insert M h)).deg_on v M.A=(M.multipartite_graph).deg_on v M.A:=
-- begin
--   intros v hv, rw deg_on,rw deg_on,  rw mp_old_nbhd_res M h v hv,
-- end

-- -- so sum of deg res to old partition over old partition is unchanged
-- lemma mp_old_sum (M :finpartition A) {C : finset α} (h: disjoint M.A C) :∑ v in M.A, (mp (insert M h)).deg_on v M.A= ∑ v in M.A,(M.multipartite_graph).deg_on v M.A
-- :=sum_congr rfl (mp_old_deg_on M h)

-- -- vertices in the new part are not adjacent to each other
-- lemma mp_int_adj (P : finpartition A) {v w :α} {C :finset α} (h: disjoint M.A C) : v∈C → w∈C →  ¬(mp (insert M h)).adj v w:=
-- begin
--   intros hv hw,   have vin:= insert_P' M h v hv,
--   have win:= insert_P' M h w hw,
--   have :=self_mem_range_succ (M.t), rw ← insert_t M h at this,
--   contrapose win,push_neg at win, exact not_nbhr_same_part this vin win,
-- end

-- -- so their deg res to the new part is zero
-- lemma mp_int_deg_on (P : finpartition A) {C :finset α} (h: disjoint M.A C) : ∀v∈C,(mp (insert M h)).deg_on v C=0:=
-- begin
--   intros v hv, rw deg_on, rw card_eq_zero, by_contra h',
--   obtain ⟨w,hw,adw⟩ :=(mp (insert M h)).exists_mem_nempty h',
--   exact (mp_int_adj M h hv hw) adw,
-- end

-- -- so the sum of their deg res to new part is also zero i.e. e(C)=0
-- lemma mp_int_sum (P : finpartition A) {C :finset α} (h: disjoint M.A C) :∑ v in C, (mp (insert M h)).deg_on v C=0:=
-- begin
--   simp only [sum_eq_zero_iff], intros x hx, exact mp_int_deg_on M h x hx,
-- end

-- --- Counting edges in complete multipartite graphs:
-- --- if we add in a new part C then the sum of degrees over new vertex set
-- --  is sum over old + 2 edges in bipartite join
-- -- ie 2*e(M')=2*e(M)+2*e(M,C)
-- lemma mp_count (P : finpartition A) {C :finset α} (h: disjoint M.A C) :∑v in M.A, (M.multipartite_graph).deg_on v M.A +2*(M.A.card)*C.card =
-- ∑ v in (insert M h).A, (mp (insert M h)).deg_on v (insert M h).A:=
-- begin
--   set H: simple_graph α:= (mp (insert M h)),
--   simp  [ insert_AB], rw sum_union h, rw [H.deg_on_add_sum' h,H.deg_on_add_sum' h],
--   rw [add_assoc ,mp_int_sum M h,  add_zero,  H.sum_deg_on_comm h.symm],
--   rw [← sum_add_distrib, card_eq_sum_ones C, mul_sum,  mp_old_sum M h ,add_right_inj],
--   apply sum_congr rfl, rw [(by norm_num: 2= 1+1),add_mul, one_mul, mul_one], intros x hx, rwa (mp_com M h x hx),
-- end

-- --- Any complete t-partite graph is (t+2)-clique free.
-- lemma mp_clique_free (P : finpartition A): M.t=t → M.A=univ →  (M.multipartite_graph).clique_free (t+2):=
-- begin
--   intros ht hA, by_contra, unfold clique_free at h, push_neg at h,
--   obtain ⟨S,hs1,hs2⟩:=h, rw is_clique_iff at hs1,
--   -- would now like to invoke the pigeonhole principle
--   -- have t+2 pigeons in t classes so two in some class which are then non-adjacent...
--   -- i did try to find this in mathlib but it was late so...
--   suffices : ∃ i∈range(M.t +1),1 < (S∩(M.P i)).card,{
--     obtain ⟨i,hi,hc⟩:=this,  rw [one_lt_card_iff] at hc,
--     obtain ⟨a,b,ha,hb,ne⟩:=hc, rw mem_inter at *,
--     have nadj:= not_nbhr_same_part' hi  ha.2 hb.2,
--     exact nadj  (hs1 ha.1 hb.1 ne),},
--   by_contra, push_neg at h,
--   have ub:(range(M.t)).sum (λi, (S∩ (M.P i)).card)≤ M.t,{
--     nth_rewrite_rhs 0 ← card_range (M.t), nth_rewrite_rhs 0 card_eq_sum_ones,
--     apply sum_le_sum h,}, nth_rewrite_rhs 0 ht at ub,
--     have uni:=bUnion_parts M, rw hA at uni,
--     have sin:=inter_univ S, rw [uni ,inter_bUnion] at sin,
--     rw [← sin, card_bUnion] at hs2, linarith,
--     intros x hx y hy ne,
--     apply disj_of_disj_inter S S (M.disj x hx y hy ne),
-- end

end simple_graph
