import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.list.basic
import data.nat.basic
import tactic.core
import mpartition
import algebra.big_operators
open finset nat mpartition

open_locale big_operators 

namespace simple_graph 


variables {α : Type*}[fintype α][inhabited α][decidable_eq α]
variables{M : multi_part α}
include M


-- given a t+1 partition on A form the complete multi-partite graph on α
-- with all edges present between parts in M.A and no edges involving vertices outside A
@[ext]
def mp (M: multi_part α) : simple_graph α:={
  adj:= λ x y, (∃ i ∈ range(M.t+1), ∃ j ∈ range(M.t+1), i≠j ∧ ((x∈ M.P i ∧ y ∈ M.P j) ∨ (x ∈ M.P j ∧ y ∈ M.P i))), 
  symm:=
  begin
    intros x y hxy,
    obtain ⟨i,hi,j,hj,ne,⟨hx,hy⟩⟩:=hxy,
    refine ⟨j ,hj, i, hi, ne.symm,_ ⟩, left ,exact ⟨hy,hx⟩,
    refine ⟨i ,hi, j, hj, ne,_ ⟩, left, rwa and_comm, 
  end,
  loopless:=begin
    intro x, push_neg, intros i hi j hj ne, 
    split; intros hxi hxj, exact M.disj i hi j hj ne (mem_inter.mpr ⟨hxi,hxj⟩), 
    exact M.disj i hi j hj ne (mem_inter.mpr ⟨hxj,hxi⟩), 
end,}


instance mp_decidable_rel : decidable_rel (mp M).adj :=
λ x y, finset.decidable_dexists_finset

instance neighbor_mp_set.mem_decidable (v : α):
  decidable_pred (∈ (mp M).neighbor_set v) := 
begin
  unfold neighbor_set, apply_instance,
end

instance multi_partite_fintype  : fintype (mp M).edge_set := 
begin
  unfold edge_set, apply_instance, 
end

--any vertex in α but not in A is isolated
lemma no_nbhrs {M: multi_part α} {v w: α} (hA: v∉M.A) : ¬(mp M).adj v w:=
begin
  contrapose! hA, 
  obtain ⟨i,hi,j,hj,a,b,c⟩:=hA, exact (sub_part hi) b, 
  exact (sub_part hj) hA_h_h_h_h_right.1,
end

-- having any neighbour implies the vertex is in A
lemma nbhrs_imp {M: multi_part α} {v w: α} : (mp M).adj v w → v ∈ M.A:=
begin
  intros h1, by_contra, exact no_nbhrs h h1,
end

-- degrees are zero outside A
lemma mp_nbhd_compl (M : multi_part α) {v : α} (hA: v∉M.A) : (mp M).degree v = 0:= 
begin
  rw degree, rw finset.card_eq_zero,
  rw eq_empty_iff_forall_not_mem, intros x hx,rw mem_neighbor_finset at hx, exact no_nbhrs hA hx,
end

-- if v and w belong to parts P i and P j and vw is an edge then i≠j
lemma mp_adj_imp {M : multi_part α} {v w: α} {i j : ℕ} (hi: i∈ range(M.t+1))(hj: j∈ range(M.t+1))(hvi: v∈M.P i) (hwj: w∈M.P j): (mp M).adj v w → i≠j:=
begin
  intros h,cases h with a ha,
  obtain ⟨har,b,hbr,abne, ab⟩:=ha, cases ab, 
  have ai:=uniq_part hi har hvi ab.1,have bj:=uniq_part hj hbr hwj ab.2,
  rwa [← ai,← bj] at abne,
  have aj:=uniq_part hj har hwj ab.2, have bi:=uniq_part hi hbr hvi ab.1,
  rw [← aj,← bi] at abne,
  exact abne.symm,
end

-- if v ∈ P i and vw is an edge then w ∈ P j for some j ∈ range(t+1), i≠j
lemma mp_adj_imp' {M : multi_part α} {v w: α} {i : ℕ}(hi: i∈ range(M.t+1))(hvi: v∈M.P i) :(mp M).adj v w → ∃j ∈ range(M.t+1), w∈ M.P j ∧ i≠j:=
begin
  intros h,
  obtain ⟨j,hj,k,hk,ne,h1⟩:= h, cases h1, have :=uniq_part hi hj hvi h1.1, rw ← this at ne,
  use [k,hk,⟨h1.2,ne⟩],
  have :=uniq_part hi hk hvi h1.1, rw ← this at ne,
  use [j,hj,⟨h1.2,ne.symm⟩],
end

--if v and w are in distinct parts then they are adjacent
lemma mp_imp_adj {M : multi_part α} {v w: α} {i j : ℕ}(hi: i∈ range(M.t+1))(hj: j∈ range(M.t+1))(hvi: v∈M.P i) (hwj: w∈M.P j): i≠ j → (mp M).adj v w :=
begin
  intros h, refine ⟨i,hi,j,hj,h,_⟩,left ,exact ⟨hvi,hwj⟩,
end

-- if v ∈ P i and w ∈ P.j with i,j ∈ range(t+1) then vw is an edge iff i≠j
lemma mp_adj_iff {M : multi_part α} {v w: α} {i j : ℕ}(hi: i∈ range(M.t+1))(hj: j∈ range(M.t+1))(hvi: v∈M.P i) (hwj: w∈M.P j): 
(mp M).adj v w ↔  i≠j := ⟨mp_adj_imp hi hj hvi hwj, mp_imp_adj hi hj hvi hwj⟩

--if v in P i and vw is an edge then w ∉ P i
lemma not_nhbr_same_part {M : multi_part α} {v w: α} {i : ℕ} (hi : i∈ range(M.t+1)) (hv: v∈ M.P i) : (mp M).adj v w → w ∉ M.P i:=
begin
  intros h1, by_contra, apply mp_adj_imp hi hi hv h h1,refl, 
end

-- if v in P i  and w in A\(P i) then vw is an edge
lemma nbhr_diff_parts {M : multi_part α} {v w: α} {i : ℕ} (hi : i∈ range(M.t+1)) (hv: v∈ M.P i) (hw : w∈ M.A\M.P i)
 : (mp M).adj v w:=
begin
  rw mem_sdiff at hw,
  cases hw with hA hni,
  rw M.uni at hA, rw mem_bUnion at hA,
  obtain ⟨j,hj1,hj2⟩:=hA,
  refine mp_imp_adj hi hj1 hv hj2 _, by_contra, rw h at hni, exact hni hj2,
end

--if v is in P i then its nbhd is A\(P i)
lemma mp_nbhd {M : multi_part α} {v:α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v ∈ M.P i) : (mp M).neighbor_finset v = (M.A)\(M.P i) :=
begin
  ext,split,rw mem_neighbor_finset,intro h, rw adj_comm at h,
  rw mem_sdiff, refine  ⟨nbhrs_imp h,_⟩, exact not_nhbr_same_part hv.1 hv.2 h.symm,
  rw mem_neighbor_finset, exact nbhr_diff_parts hv.1 hv.2,
end
 
-- degree sum over all vertices 
def mp_dsum (M : multi_part α) : ℕ:= ∑ v in M.A, (mp M).degree v

-- degree of vertex in P i is card(A\P i)
lemma mp_deg {M : multi_part α} {v : α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v∈ M.P i) : (mp M).degree v = ((M.A)\(M.P i)).card:= 
begin
  rw degree,rwa mp_nbhd hv,
end

-- degree of v in P i as |A|- |P i|
lemma mp_deg_diff {M : multi_part α} {v : α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v∈ M.P i) : (mp M).degree v = M.A.card -  (M.P i).card:= 
begin
  rw mp_deg hv, exact card_sdiff (sub_part hv.1),
end

-- sum of degrees as sum over parts 
lemma mp_deg_sum (M : multi_part α) : ∑ v in M.A, (mp M).degree v = ∑i in range(M.t+1),(M.P i).card * ((M.A)\(M.P i)).card :=
begin
  nth_rewrite 0 M.uni,
  rw sum_bUnion (pair_disjoint M), apply finset.sum_congr rfl _,
  intros x hx, rw [finset.card_eq_sum_ones, sum_mul, one_mul], apply finset.sum_congr rfl _,
  intros v hv, exact mp_deg ⟨hx,hv⟩,
end

---using squares of part sizes and avoiding tsubtraction
lemma mp_deg_sum_sq' {M : multi_part α} : ∑ v in M.A, (mp M).degree v + ∑i in range(M.t+1), (M.P i).card^2 = M.A.card^2:=
begin
  rw mp_deg_sum M, rw pow_two, nth_rewrite 0 card_uni, rw ← sum_add_distrib, rw sum_mul, 
  refine finset.sum_congr rfl _,
  intros x hx,rw pow_two,rw ← mul_add, rw card_part_uni hx,
end

-- standard expression  as |A|^2- ∑ degrees squared.
lemma mp_deg_sum_sq (M : multi_part α) : ∑ v in M.A, (mp M).degree v = M.A.card^2 - ∑i in range(M.t+1), (M.P i).card^2
:=eq_tsub_of_add_eq mp_deg_sum_sq'


-- upper bound on deg sum of any complete multipartite graph on A to show that it can't be improved more than |A|^2 times.
lemma mp_dsum_le (M: multi_part α) : mp_dsum M ≤ M.A.card^2:=
begin
  rw [mp_dsum, mp_deg_sum_sq], exact tsub_le_self,
end


-- immoveable partition corresponds to balanced partition sizes so if we have two immoveable partitions of same set A into
-- the same number of parts then their degree sums are the the same
lemma immoveable_deg_sum_eq (M N : multi_part α): M.A= N.A → M.t=N.t → immoveable M → immoveable N → mp_dsum M = mp_dsum N:=
begin
   intros hA ht iM iN, unfold mp_dsum,  rw [mp_deg_sum_sq,mp_deg_sum_sq,hA], rw [immoveable_iff_not_moveable, moveable,not_not] at *,
   apply congr_arg _, unfold P' at *, rw ← ht at iN,  
   have:= bal_sum_sq_eq iM iN _, unfold sum_sq at this, rwa  ← ht,
   nth_rewrite 1 ht, rw [mpartition.psum, mpartition.psum,← card_uni,←card_uni],congr, exact hA,
end




lemma mp_deg_sum_move_help{M : multi_part α} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t+1) ∧ v ∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) (hc: (M.P j).card+1<(M.P i).card ) : 
(M.P i).card * ((M.A)\(M.P i)).card + (M.P j).card * ((M.A)\(M.P j)).card <((move M hvi hj).P i).card * (((move M hvi hj).A)\((move M hvi hj).P i)).card + ((move M hvi hj).P j).card * (((move M hvi hj).A)\((move M hvi hj).P j)).card:=
begin
  rw move_Pcard hvi hj hvi.1, rw move_Pcard hvi hj hj.1,rw move_Pcard_sdiff hvi hj hvi.1, rw move_Pcard_sdiff hvi hj hj.1,
  split_ifs,exfalso, exact h.1 rfl,exfalso, exact h.1 rfl,exfalso, exact h.1 rfl,exfalso, exact h_1.2 rfl,exfalso, exact hj.2 h_2,
  rw card_sdiff (sub_part hvi.1), rw card_sdiff (sub_part hj.1),
  exact move_change hc (two_parts hvi.1  hj.1 hj.2.symm),
end

lemma mp_deg_sum_move_help2{M : multi_part α} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t+1) ∧ v ∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i)  : 
∑ (x : ℕ) in ((range (M.t + 1)).erase j).erase i, ((move M hvi hj).P x).card * ((move M hvi hj).A \ (move M hvi hj).P x).card =
∑ (y : ℕ) in ((range (M.t + 1)).erase j).erase i, (M.P y).card*((M.A\(M.P y)).card):=
begin
  apply sum_congr rfl _, intros k hk, rw move_Pcard hvi hj, rw move_Pcard_sdiff hvi hj,split_ifs,refl,
  exfalso, rw h_1 at hk,exact not_mem_erase i _ hk,exfalso,push_neg at h, simp only [*, ne.def, not_false_iff, mem_erase, eq_self_iff_true] at *,
  exact mem_of_mem_erase (mem_of_mem_erase hk),   exact mem_of_mem_erase (mem_of_mem_erase hk),  
end

-- given a vertex v ∈ P i and a part P j such that card(P j)+1 < card(P i) then moving v from Pi to Pj will increase the sum of degrees
lemma mp_deg_sum_move {M : multi_part α} {v : α} {i j: ℕ}  (hvi: i∈ range(M.t+1) ∧ v ∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) (hc: (M.P j).card+1<(M.P i).card ) : 
∑ w in M.A,  (mp M).degree w < ∑ w in (move M hvi hj).A,  (mp (move M hvi hj)).degree w :=
begin
  rw mp_deg_sum M,rw mp_deg_sum (move M hvi hj), 
  --rw (move_A hvi hj), 
  rw (move_t hvi hj), 
  rw [← sum_erase_add (range(M.t+1)) _ hj.1,← sum_erase_add (range(M.t+1)) _ hj.1],
  rw ← sum_erase_add ((range(M.t+1)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1),
  rw ← sum_erase_add ((range(M.t+1)).erase j) _ (mem_erase_of_ne_of_mem hj.2.symm hvi.1),
  rw mp_deg_sum_move_help2,
  rw [add_assoc,add_assoc], refine (add_lt_add_iff_left _).mpr _ , exact mp_deg_sum_move_help hvi hj hc,
end

end simple_graph







