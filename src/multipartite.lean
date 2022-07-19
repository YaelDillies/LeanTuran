import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.list.basic
import data.nat.basic
import tactic.core
import algebra.big_operators
open finset fintype nat

open_locale big_operators 

namespace simple_graph 

variables {α : Type*}[fintype α][inhabited α][decidable_eq α]
-- basic structure for a complete (t+1)-partite graph on α
@[ext] 
structure multi_part (α : Type*)[decidable_eq α]:=--[fintype α][inhabited α][decidable_eq α]:=
(t :ℕ) (P: ℕ → finset α) (A :finset α) 
(uni: A = (range(t+1)).bUnion (λi , P i))
(disj: ∀i∈ range(t+1),∀j∈ range(t+1), i≠j → disjoint (P i) (P j)) 


def insert (M : multi_part α)  {B : finset α} (h: disjoint M.A B): multi_part α :={
  t:=M.t+1,
  P:=begin intro i, exact ite (i≠M.t+1) (M.P i) (B), end,
  A:=B ∪ M.A,
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
    intros i hi j hj iltj, split_ifs, 
    refine M.disj i _ j _ iltj,
    exact mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hi) h_1), 
    exact mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hj) h_2), 
    rw [M.uni, disjoint_bUnion_left] at h, 
    apply h i (mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hi) h_1)),
    rw [M.uni, disjoint_bUnion_left] at h, rw disjoint.comm,
    apply h j (mem_range.mpr (lt_of_le_of_ne (mem_range_succ_iff.mp hj) h_2)),
    push_neg at h_1,push_neg at h_2, rw ← h_2 at h_1, exfalso,
    exact iltj h_1, 
  end,}

-- member of a part implies member of union
lemma mem_part{M:multi_part α} {v :α} {i :ℕ}: i∈range(M.t+1) → v ∈ M.P i → v ∈ M.A :=
begin
  intros hi hv,rw M.uni,rw mem_bUnion, exact ⟨i,hi,hv⟩,
end
-- every vertex in A belongs to a part
lemma inv_part {M:multi_part α} {v :α} (hA: v∈M.A): ∃ i∈ range(M.t+1), v ∈ M.P i:=
begin
  rw [M.uni,mem_bUnion] at hA, exact hA,
end
-- if v belongs to P i and P j then i = j.
lemma uniq_part {M : multi_part α}{v :α} {i j : ℕ} : i ∈ range(M.t+1)→ j ∈ range(M.t+1) → v∈M.P i → v∈ M.P j → i = j:=
begin
  intros hi hj hiv hjv, by_contra, have:=M.disj i hi j hj h, exact this (mem_inter.mpr ⟨hiv,hjv⟩),
end
-- every part is contained in A
lemma sub_part {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)) : M.P i ⊆ M.A :=
begin
  rw M.uni, intros x hx,  rw  mem_bUnion,  exact ⟨i,hi,hx⟩,
end

--A is the union of each part and the sdiff
lemma sdiff_part {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)) : M.A = M.A\(M.P i)∪M.P i :=
begin
  have:= sub_part hi,
  rwa [sdiff_union_self_eq_union, left_eq_union_iff_subset] at *,
end


lemma disjoint_part {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)): disjoint ((M.A)\(M.P i)) (M.P i) := sdiff_disjoint

lemma card_part_uni {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)):  M.A.card= (M.A\(M.P i)).card + (M.P i).card:=
begin
  nth_rewrite 0 sdiff_part hi,
  apply card_disjoint_union sdiff_disjoint,
end


---- given a graph on a subset of α can form the bipartite join with rest of α
--- given a t+1 partition on A form the complete multi-partite graph 
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

variables{M : multi_part α}

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

lemma no_nbhrs {M: multi_part α} {v w: α} (hA: v∉M.A) : ¬(mp M).adj v w:=
begin
  contrapose! hA, 
  obtain ⟨i,hi,j,hj,a,b,c⟩:=hA, exact (sub_part hi) b, 
  exact (sub_part hj) hA_h_h_h_h_right.1,
end

lemma nbhrs_imp {M: multi_part α} {v w: α} : (mp M).adj v w → v ∈ M.A:=
begin
  intros h1, by_contra, exact no_nbhrs h h1,
end


lemma mp_nbhd_compl (M : multi_part α) {v : α} (hA: v∉M.A) : (mp M).degree v = 0:= 
begin
  rw degree, rw finset.card_eq_zero,
  rw eq_empty_iff_forall_not_mem, intros x hx,rw mem_neighbor_finset at hx, exact no_nbhrs hA hx,
end

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

lemma mp_adj_imp' {M : multi_part α} {v w: α} {i j : ℕ}(hi: i∈ range(M.t+1))(hvi: v∈M.P i) :(mp M).adj v w → ∃j ∈ range(M.t+1), w∈ M.P j ∧ i≠j:=
begin
  intros h,
  obtain ⟨j,hj,k,hk,ne,h1⟩:= h, cases h1, have :=uniq_part hi hj hvi h1.1, rw ← this at ne,
  use [k,hk,⟨h1.2,ne⟩],
  have :=uniq_part hi hk hvi h1.1, rw ← this at ne,
  use [j,hj,⟨h1.2,ne.symm⟩],
end


lemma mp_imp_adj {M : multi_part α} {v w: α} {i j : ℕ}(hi: i∈ range(M.t+1))(hj: j∈ range(M.t+1))(hvi: v∈M.P i) (hwj: w∈M.P j): i≠ j → (mp M).adj v w :=
begin
  intros h, refine ⟨i,hi,j,hj,h,_⟩,left ,exact ⟨hvi,hwj⟩,
end


lemma mp_adj_iff {M : multi_part α} {v w: α} {i j : ℕ}(hi: i∈ range(M.t+1))(hj: j∈ range(M.t+1))(hvi: v∈M.P i) (hwj: w∈M.P j): 
(mp M).adj v w ↔  i≠j := ⟨mp_adj_imp hi hj hvi hwj, mp_imp_adj hi hj hvi hwj⟩



lemma not_nhbr_same_part {M : multi_part α} {v w: α} {i : ℕ} (hi : i∈ range(M.t+1)) (hv: v∈ M.P i) : (mp M).adj v w → w ∉ M.P i:=
begin
  intros h1, by_contra, apply mp_adj_imp hi hi hv h h1,refl, 
end

lemma nbhr_diff_parts {M : multi_part α} {v w: α} {i : ℕ} (hi : i∈ range(M.t+1)) (hv: v∈ M.P i) (hw : w∈ M.A\M.P i) : (mp M).adj v w:=
begin
  rw mem_sdiff at hw,
  cases hw with hA hni,
  rw M.uni at hA, rw mem_bUnion at hA,
  obtain ⟨j,hj1,hj2⟩:=hA,
  refine mp_imp_adj hi hj1 hv hj2 _, by_contra, rw h at hni, exact hni hj2,
end

lemma mp_nbhd {M : multi_part α} {v:α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v ∈ M.P i) : (mp M).neighbor_finset v = (M.A)\(M.P i) :=
begin
  ext,split,rw mem_neighbor_finset,intro h, rw adj_comm at h,
  rw mem_sdiff, refine  ⟨nbhrs_imp h,_⟩, exact not_nhbr_same_part hv.1 hv.2 h.symm,
  rw mem_neighbor_finset, exact nbhr_diff_parts hv.1 hv.2,
end

lemma mp_deg {M : multi_part α} {v : α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v∈ M.P i) : (mp M).degree v = ((M.A)\(M.P i)).card:= 
begin
  rw degree,rwa mp_nbhd hv,
end

lemma mp_deg_diff {M : multi_part α} {v : α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v∈ M.P i) : (mp M).degree v = M.A.card -  (M.P i).card:= 
begin
  rw mp_deg hv, exact card_sdiff (sub_part hv.1),
end

lemma mp_deg_sum {M : multi_part α} : ∑ v in M.A, (mp M).degree v = M.A.card^2 -∑i in range(M.t+1),(M.P i).card^2:=
begin
 
sorry
end
--lemma mp_nbhd_comp {M : multi_part α} {v : α} {i: ℕ} (hv: i∈ range(M.t+1) ∧ v∈ M.P i) : (mp M).degree v + (M.P i).card = M.A.card:= 
--begin
--  rw degree, rw mp_nbhd hv, rw (card_part_uni hv.1).symm,
--end

end simple_graph


--
--lemma mp_deg_sum {M : multi_part α} : 
--∑ v in (univ:finset α), (mp M).degree v  =  M.A.card^2 - ∑ i in range(M.t + 1),(M.P i).card^2:=
--begin
--  sorry, 
  --rw M.uni, unfold degree,
--end
-- extend a t+1 partite-graph on A to (t+2)-partite on A ∪ B with disjoint A B.







