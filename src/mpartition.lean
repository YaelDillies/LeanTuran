import data.finset.basic
import data.list.basic
import data.nat.basic
import tactic.core
import algebra.big_operators
open finset nat

open_locale big_operators 
-- basic structure for a complete (t+1)-partite graph on α
-- not actually a partition in the sense of mathlib since that would
-- require at most one empty part, while I'm happy to allow any number of
-- empty parts 
namespace mpartition

def tn : ℕ → ℕ → ℕ:=
begin
  intros t n,
  set a:= n/(t+1),--- size of a small part
  set b:= n%(t+1),-- number of large parts
  exact (a^2)*nat.choose(t+1-b)(2)+a*(a+1)*b*(t+1-b)+((a+1)^2)*nat.choose(b)(2),
end


--complement is easier to deal with and also multiply by 2
-- so 2*(tn t n) = n^2 - (tn' t n) 
def tn' : ℕ → ℕ → ℕ:=
begin
  intros t n,
  set a:= n/(t+1),--- size of a small part
  set b:= n%(t+1),-- number of large parts
  exact (t+1-b)*a^2 + b*(a+1)^2,
end



-- the actual mess is here
lemma tn_tn' (t n : ℕ) : (tn' t n) + 2*(tn t n) = n^2:=
begin
  unfold tn tn', simp,
  ---START HERE
sorry,
end

-- start with some helper functions that don't need partitions to be defined.
-- here P : ℕ → ℕ plays the role of sizes of parts in a (t+1)-partition 

-- sum of part sizes i.e number of vertices 
def psum (t : ℕ) (P : ℕ → ℕ): ℕ:= ∑i in range(t+1), P i

-- sum of squares of part sizes (basically 2*edges in complement)
def sum_sq (t : ℕ) (P: ℕ → ℕ): ℕ := ∑i in range(t+1),(P i)^2

-- inevitable and painful mod (t+1) calculation related to sizes of parts in balanced partition
lemma mod_tplus1 {a b c d t: ℕ} (hc: c ≤ t) (hd:d ≤ t) (ht: (t+1)*a + c = (t+1)*b+d) : 
 (a = b) ∧ (c = d):=
begin
  have hc':c<t+1:=by linarith [hc], have hd':d<t+1:=by linarith [hd],
  have mc: c%(t+1)=c:=mod_eq_of_lt hc',have md: d%(t+1)=d:=mod_eq_of_lt hd',
  rw [add_comm,add_comm _ d] at ht,
  have hmtl:(c+(t+1)*a)%(t+1)=c%(t+1):=add_mul_mod_self_left c (t+1) a,
  have hmtr:(d+(t+1)*b)%(t+1)=d%(t+1):=add_mul_mod_self_left d (t+1) b,
  rw mc at hmtl, rw md at hmtr,rw ht at hmtl,rw hmtl at hmtr,
  refine ⟨_,hmtr⟩, rw hmtr at ht,simp only [add_right_inj, mul_eq_mul_left_iff, succ_ne_zero, or_false] at *,
  exact ht,
end

---can this be used to simplify the previous lemma ?
lemma mod_tplus1' {t n:ℕ} : (t+1)*(n/(t+1))+n%(t+1)=n:=
begin
  exact div_add_mod n (t+1),
end


-- now lots of useful results about balanced partitions

-- a balanced (t+1) partition is one with almost equal parts
def balanced (t : ℕ) (P : ℕ → ℕ): Prop:= ∀ i ∈ range(t+1),∀ j∈ range(t+1), P i ≤ (P j) + 1

-- smallest part is well-defined
def min_p (t : ℕ) (P : ℕ → ℕ) : ℕ:= begin
  have nem: ((range(t+1)).image(λi , P i)).nonempty :=(nonempty.image_iff  _).mpr (nonempty_range_succ),
  exact min' ((range(t+1)).image(λi , P i)) nem,
end

-- indices of small parts
def small_parts {t : ℕ} {P:ℕ → ℕ} (h: balanced t P) : finset ℕ:=(range(t+1)).filter (λi, P i = min_p t P)

-- .. and large parts
def large_parts {t : ℕ} {P:ℕ → ℕ} (h: balanced t P) : finset ℕ:=(range(t+1)).filter (λi, P i = min_p t P +1 )

-- there is a smallest part 
lemma small_nonempty {t : ℕ} {P:ℕ → ℕ} (h: balanced t P) :(small_parts h).nonempty:=
begin
  rw small_parts, have nem: ((range(t+1)).image(λi , P i)).nonempty :=(nonempty.image_iff  _).mpr (nonempty_range_succ),
  set a:ℕ:=min' ((range(t+1)).image(λi , P i)) nem with ha,
  have ain:= min'_mem ((range(t+1)).image(λi , P i)) nem, rw ← ha at ain,
  rw mem_image at ain,
  obtain ⟨k,hk1,hk2⟩:=ain, use k, rw mem_filter,refine ⟨hk1,_⟩,rw ha at hk2,exact hk2,
end

-- in a balanced partition all parts are small or large
lemma con_sum {t :ℕ} {P :ℕ → ℕ} (h: balanced t P): ∀i∈ range(t+1), P i = min_p t P ∨ P i = min_p t P +1:=
begin
  unfold balanced at h,
  have nem: ((range(t+1)).image(λi , P i)).nonempty :=(nonempty.image_iff  _).mpr (nonempty_range_succ),
  set a:ℕ:=min' ((range(t+1)).image(λi , P i)) nem with ha,
  set b:ℕ:=max' ((range(t+1)).image(λi , P i)) nem with hb,
  intros i hi,
  have ale: a ≤ P i:= min'_le ((range(t+1)).image(λi , P i)) (P i) (mem_image_of_mem (P ) hi),
  have leb:P i ≤ b:= le_max' ((range(t+1)).image(λi , P i)) (P i) (mem_image_of_mem (P ) hi),
  have ain:= min'_mem ((range(t+1)).image(λi , P i)) nem, rw ← ha at ain,
  have bin:= max'_mem ((range(t+1)).image(λi , P i)) nem, rw ← hb at bin,
  have blea: b≤ a+1,{ rw mem_image at *,
    obtain ⟨k,hk,hak⟩:=ain, obtain ⟨l,hl,hbl⟩:=bin,
    rw [← hak,←hbl], exact h l hl k hk,},
  have ple :=le_trans leb blea,
  by_contra, push_neg at h, cases h, have h1:=lt_of_le_of_ne ale h_left.symm,
  have h2:=lt_of_le_of_ne ple h_right, linarith,
end

-- large parts are those that aren't small
lemma large_parts' {t : ℕ} {P:ℕ → ℕ} (h: balanced t P): large_parts h = (range(t+1)).filter (λi, ¬ P i = min_p t P):=
begin
  have :=con_sum h, unfold large_parts, ext,rw [mem_filter,mem_filter],split,
  intro h', refine ⟨h'.1,_⟩, intros h2, rw h2 at h', exact succ_ne_self (min_p t P) h'.2.symm,
  intros h', refine ⟨h'.1,_⟩, specialize this a h'.1,  cases this, exfalso, exact h'.2 this, exact this,
end

-- parts cannot be both small and large
lemma parts_disjoint {t : ℕ}  {P :ℕ → ℕ} (h: balanced t P) : disjoint (small_parts h) (large_parts h):=
begin
  convert disjoint_filter_filter_neg (range(t+1)) (λi, P i = min_p t P),
  exact large_parts' h,
end

-- all parts are either small or large
lemma parts_union {t : ℕ}  {P :ℕ → ℕ} (h: balanced t P) : (range(t+1)) = (small_parts h) ∪ (large_parts h):=
begin
  have :=con_sum h,
  ext,unfold small_parts, unfold large_parts, rw mem_union, split,   intro ha,
  rw [mem_filter,mem_filter],specialize this a ha, cases this, left ,exact ⟨ha,this⟩,right,exact ⟨ha,this⟩,
  rw [mem_filter,mem_filter],intros h, cases h, exact h_1.1, exact h_1.1,
end

-- so the number of small parts + large parts = t+1
lemma parts_card_add {t : ℕ}  {P :ℕ → ℕ} (h: balanced t P) : (small_parts h).card + (large_parts h).card= t+1:=
begin
  rw [← card_range (t+1), parts_union h, card_disjoint_union (parts_disjoint h)],
end

-- not all parts are large since there is at least one small part
lemma large_parts_card {t : ℕ} {P:ℕ → ℕ} (h: balanced t P) : (large_parts h).card ≤ t:=
begin
  have spos:0 < (small_parts h).card:=card_pos.mpr (small_nonempty h),
  have := parts_card_add h, linarith,
end

lemma small_parts_card  {t : ℕ} {P:ℕ → ℕ} (h: balanced t P) : (small_parts h).card =(t+1)-(large_parts h).card:=
begin
  rw ← parts_card_add h, rwa [add_tsub_cancel_right],
end

-- any sum of a function over P is determined by the sizes and parts
lemma bal_sum_f {t : ℕ} {P: ℕ → ℕ} (h: balanced t P) (f: ℕ → ℕ):∑ i in range(t+1), f (P i) = 
(small_parts h).card * f(min_p t P) + (large_parts h).card * f(min_p t P+1) := 
begin
  rw [parts_union h, sum_union (parts_disjoint h)], congr, 
  rw [card_eq_sum_ones, sum_mul, one_mul], apply sum_congr,refl,rw small_parts,intros x, rw mem_filter,intro hx,rw hx.2,
  rw [card_eq_sum_ones, sum_mul, one_mul], apply sum_congr,refl, rw large_parts,intros x, rw mem_filter,intro hx,rw hx.2,
end

-- simple equation for sum of parts 
lemma bal_sum {t : ℕ} {P : ℕ → ℕ} (h: balanced t P) : psum t P = (small_parts h).card * (min_p t P) + 
  (large_parts h).card * (min_p t P+1) := bal_sum_f h (λi,i)

-- nicer version of previous
lemma bal_sum' {t : ℕ} {P : ℕ → ℕ} (h: balanced t P) : psum t P = (t+1)* (min_p t P) + (large_parts h).card :=
begin
  rw [bal_sum h, mul_add,mul_one,← add_assoc,← add_mul,parts_card_add h],
end

-- given a balanced partition of n into (t+1)-parts the small part is n/(t+1) and there are n%(t+1) lare parts
lemma bal_sum_n {t n :ℕ} {P :ℕ→ ℕ} (hp: balanced t P) (hn: psum t P = n): min_p t P = n/(t+1) ∧ (large_parts hp).card = n%(t+1):=
begin
  rw [bal_sum' hp, ← div_add_mod n (t+1)] at hn, exact mod_tplus1 (large_parts_card hp) (le_of_lt_succ (mod_lt n (succ_pos t))) hn,
end

-- sum of a function f over parts of a balanced partition  of n into (t+1) parts is:
lemma bal_sum_n_f {t n : ℕ} {P: ℕ → ℕ} (hp: balanced t P) (hn: psum t P = n) (f: ℕ → ℕ) :∑ i in range(t+1), f (P i) = 
(t+1-n%(t+1)) * f(n/(t+1)) + (n%(t+1)) * f(n/(t+1)+1) := 
begin
  obtain hf :=bal_sum_f hp, obtain ⟨mn,ln⟩:= bal_sum_n hp hn, 
  specialize hf f,  rwa [mn, small_parts_card, ln] at hf, 
end

-- balanced partitions have same part sizes and number of each type of part
lemma bal_eq {t : ℕ} {P Q :ℕ→ ℕ} (hbp : balanced t P) (hbq: balanced t Q) (hs: psum t P = psum t Q): 
(min_p t P = min_p t Q) ∧ (large_parts hbp).card = (large_parts hbq).card ∧ (small_parts hbp).card = (small_parts hbq).card:=
begin
  rw [bal_sum' hbp, bal_sum' hbq] at hs,
  have hc:=large_parts_card hbp,have hd:=large_parts_card hbq,
  have:=mod_tplus1 hc hd hs, have addP:=parts_card_add hbp,
  have addQ:=parts_card_add hbq, rw this.2 at addP, refine ⟨this.1,this.2,_⟩, linarith,
end




-- any two balanced (t+1)-partitions of same size set give the same sum of squares.
-- could be for other functions but not needed 
-- this tells us that balanced partitions of the same vertex set give the same number of edges
lemma bal_sum_sq_eq {t : ℕ} {P Q:ℕ → ℕ} (hbp: balanced t P) (hbq: balanced t Q) (hs: psum t P = psum t Q): sum_sq t P = sum_sq t Q:=
begin
  have h1:=bal_sum_f hbp (λx ,x^2), have h2:=bal_sum_f hbq (λx ,x^2), 
  have h3:= bal_eq hbp hbq hs,
  rw [sum_sq,sum_sq,h1,h2,h3.1,h3.2.1,h3.2.2],
end




lemma bal_turan_help {n t :ℕ} {P:ℕ→ ℕ} (hb: balanced t P) (hn: (∑i in range(t+1), P i)=n):  sum_sq t P = tn' t n:=
begin
  rw tn', rw sum_sq, rw bal_sum_n_f hb hn (λi, i^2),
end



lemma bal_turan_bd {n t:ℕ} {P:ℕ→ ℕ} (hb: balanced t P) (hn: (∑i in range(t+1), P i)=n) : sum_sq t P + 2*tn t n = n^2:=
begin
  rw bal_turan_help hb hn, exact tn_tn' t n,
end
--- now actually introduce the partitions we use to build complete multipartite graphs
variables {α : Type*}[fintype α][inhabited α][decidable_eq α]
@[ext] 
structure multi_part (α : Type*)[decidable_eq α][fintype α][inhabited α][decidable_eq α]:=
(t :ℕ) (P: ℕ → finset α) (A :finset α) 
(uni: A = (range(t+1)).bUnion (λi , P i))
(disj: ∀i∈ range(t+1),∀j∈ range(t+1), i≠j → disjoint (P i) (P j)) 


-- given M with M.t+1 parts and partition sets P we have P' M is the corresponding sizes of parts
def P' (M: multi_part α) :ℕ → ℕ:= (λi, (M.P i).card)



def sum_sq_c (M: multi_part α): ℕ:= ∑i in range(M.t+1), card(M.P i)^2

-- a partition is moveable if the part sizes are unbalanced
--def moveable (M : multi_part α)  :Prop := ∃ i∈ range(M.t+1),∃ j ∈ range(M.t+1), (M.P j).card +1 < (M.P i).card
def moveable (M : multi_part α)  :Prop := ¬ balanced M.t (P' M)
--- ie. immoveable means the sizes of parts is such that it is balanced
def immoveable (M : multi_part α) :Prop :=∀i∈ range(M.t+1),∀j∈ range(M.t+1), (M.P i).card ≤ (M.P j).card +1


-- obviously
lemma immoveable_iff_not_moveable (M : multi_part α) :immoveable M ↔ ¬moveable M:=
begin
  unfold immoveable, unfold moveable,push_neg,refl,
end


lemma immoveable_imp {M: multi_part α} (h: ¬immoveable M): ∃i∈ range(M.t+1),∃j∈ range(M.t+1),∃v∈M.P i, j≠i ∧ (M.P j).card +1< (M.P i).card:=
begin
  rw [immoveable_iff_not_moveable, not_not,  moveable,balanced,  P'] at h, push_neg at h,
  obtain ⟨i,hi,j,hj,hc⟩:=h, use [i, hi, j, hj], 
  have ic: 0<(M.P i).card:= by linarith,
  rw card_pos at ic, obtain ⟨v,hv⟩:=ic,
  have cne: (M.P i).card≠(M.P j).card:= by linarith,
  refine ⟨v,hv,_,hc⟩, intro eq,rw eq at cne, exact cne rfl,
end



-- there is a partition
instance (α :Type*)[decidable_eq α][fintype α][inhabited α][decidable_eq α] : inhabited (multi_part α):=
{default:={ t:=0, P:= λ i , ∅, A:=∅, uni:=rfl, 
disj:=λ i hi j hj ne, disjoint_empty_left ∅,
 }}

-- default mpartition of B into s+1 parts 1 x B and s x ∅
def default_M (B:finset α) (s:ℕ)  : multi_part α:={
  t:=s, P:= begin intro i, exact ite (i=0) (B) (∅), end, A:=B,
  uni:= begin ext, split,intro ha,rw mem_bUnion,use 0, rw mem_range, exact ⟨zero_lt_succ s,ha⟩, 
   rw mem_bUnion,intro h, cases h with i h2,cases h2,split_ifs at h2_h,exact h2_h,exfalso, exact h2_h,end,
  disj:= begin intros i hi j hj ne,split_ifs,exfalso,rw h at ne,rw h_1 at ne, exact ne rfl, 
    exact disjoint_empty_right _,exact disjoint_empty_left _,exact disjoint_empty_left _,end,}

--

-- insert new disjoint set to the partition to increase number of parts
--- we will need this to build the complete multipartite graph used fro Furedi's stabilty result
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
--

--- after insert the vertex set is the union of new and old
lemma insert_AB (M: multi_part α) {B :finset α} (h: disjoint M.A B):
(insert M h).A = M.A ∪ B:=union_comm _ _

-- t becomes t+1 (so now have (t+2) parts rather than (t+1))
lemma insert_t (M: multi_part α) {B :finset α} (h: disjoint M.A B):(insert M h).t =M.t+1:=rfl

--the parts are the same except the last which is the new set.
lemma insert_P (M: multi_part α) {B :finset α} (h: disjoint M.A B) :∀i, (insert M h).P i =
 ite (i≠ M.t+1) (M.P i) (B) :=λi, rfl 

--all vertices in the new part are in the last part of the new partition
lemma insert_P' (M: multi_part α) {B :finset α} (h: disjoint M.A B) : ∀v∈B, v∈ (insert M h).P (M.t+1):=
begin
  intros v hv, rw insert_P,split_ifs,exfalso, exact h_1 rfl, exact hv,
end

--conversely if v is in the last part of the new partition then it is from the added part.
lemma insert_C (M: multi_part α) {B :finset α} (h: disjoint M.A B){v:α} : v∈ (insert M h).P (M.t+1) → v∈ B:=
begin
  intro h1, rw insert_P at h1,split_ifs at h1,exfalso, exact h_1 rfl, exact h1,
end

-- there is always a (s+1)-partition of B for any finset α B and nat s
lemma exists_mpartition (B: finset α) (s:ℕ): ∃ M:multi_part α, M.A=B ∧ M.t=s:=
begin
  use default_M B s, exact ⟨rfl,rfl⟩,
end

---M.disj is the same as pairwise_disjoint but without any coercion to set for range(t+1) 
lemma pair_disjoint (M : multi_part α) : ((range(M.t+1):set ℕ)).pairwise_disjoint M.P:=M.disj

-- size of A is sum of size of part
lemma card_uni  (M : multi_part α) : M.A.card = ∑i in range(M.t+1),(M.P i).card:= begin
  rw [M.uni, finset.card_eq_sum_ones, sum_bUnion (pair_disjoint M)],
  apply finset.sum_congr rfl _, intros x hx, rwa ← finset.card_eq_sum_ones,
end

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

-- if v belongs to P i and j≠ i and is in range then v ∉ part j
lemma uniq_part' {M : multi_part α}{v :α} {i j : ℕ} : i ∈ range(M.t+1)→ j ∈ range(M.t+1) → i≠ j→ v∈M.P i → v∉ M.P j:=
begin
  intros hi hj hiv ne, contrapose hiv,push_neg at hiv,rw not_ne_iff, exact uniq_part hi hj ne hiv,
end

-- every part is contained in A
lemma sub_part {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)) : M.P i ⊆ M.A :=
begin
  rw M.uni, intros x hx,  rw  mem_bUnion,  exact ⟨i,hi,hx⟩,
end

-- if there are two different parts then the sum of their sizes is at most the size of the whole
-- could make a version for any number of parts but don't really need it
lemma two_parts {M: multi_part α} {i j : ℕ} (hi: i ∈ range(M.t+1))  (hj: j ∈ range(M.t+1)) (hne: i≠ j) : (M.P i).card + (M.P j).card ≤ M.A.card:=
begin
  rw card_uni, rw ← sum_erase_add (range(M.t+1)) _ hj, apply nat.add_le_add_right,
  rw ← sum_erase_add ((range(M.t+1)).erase j) _ (mem_erase_of_ne_of_mem hne hi),
  nth_rewrite 0 ← zero_add (M.P i).card, apply nat.add_le_add_right,
  simp only [zero_le],
end

--A is the union of each part and the sdiff
lemma sdiff_part {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)) : M.A = M.A\(M.P i)∪M.P i :=
begin
  have:= sub_part hi,
  rwa [sdiff_union_self_eq_union, left_eq_union_iff_subset] at *,
end

-- each part is disjoint from its sdiff with the whole
lemma disjoint_part {M:multi_part α} {i : ℕ} : disjoint ((M.A)\(M.P i)) (M.P i) := sdiff_disjoint

-- size of uni = sum of rest and part
lemma card_part_uni {M:multi_part α} {i : ℕ} (hi: i ∈ range(M.t+1)):  M.A.card= (M.A\(M.P i)).card + (M.P i).card:=
begin
  nth_rewrite 0 sdiff_part hi,
  apply card_disjoint_union sdiff_disjoint,
end

-- create a new partition by moving v from P i to P j,
-- why could I not use "(M.P j).insert v" invalid field notation, but it didn't complain about "(M.P i).erase v"
--- Error message :'insert' is not a valid "field" because environment does not contain 'finset.insert' M.P j which has type finset α
def move (M : multi_part α) {v : α} {i j: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) : multi_part α :={
  t:=M.t,
  P:= begin intros k, exact ite (k ≠ i ∧ k ≠ j) (M.P k) (ite (k = i) ((M.P i).erase v) ((M.P j) ∪ {v})),end,
  A:=M.A,
  uni:=begin 
    rw M.uni,ext,split, rw [mem_bUnion,mem_bUnion],intros h,simp only [*, mem_range, ne.def, exists_prop] at *,
    by_cases hav: a=v,
      refine ⟨j,hj.1,_⟩,rw ← hav at *, split_ifs,exfalso, exact h_1.2 rfl,exfalso, push_neg at h_1,exact hj.2 h_2,
      refine mem_union_right _ (mem_singleton_self a), 
      obtain ⟨k,hk1,hk2⟩:=h,
      refine ⟨k,hk1,_⟩, split_ifs, exact hk2, refine mem_erase.mpr _,rw h_1 at hk2, exact ⟨hav,hk2⟩,
      push_neg at h, rw (h h_1) at hk2, exact mem_union_left _ hk2,
    rw [mem_bUnion,mem_bUnion],intros h,simp only [*, mem_range, ne.def, exists_prop] at *,
    by_cases hav: a=v,
      rw ← hav at hvi, exact ⟨ i,hvi⟩,
      obtain ⟨k,hk1,hk2⟩:=h, split_ifs at hk2, exact ⟨k,hk1,hk2⟩, exact ⟨i,hvi.1,(erase_subset v (M.P i)) hk2⟩,
      refine ⟨j,hj.1,_⟩, rw mem_union at hk2, cases hk2, exact hk2,exfalso, exact hav (mem_singleton.mp hk2), end,
  disj:=begin 
    intros a ha b hb ne,split_ifs, exact M.disj a ha b hb ne,
    have:=M.disj a ha i hvi.1 h.1, apply disjoint_of_subset_right _ this, exact erase_subset _ _,  
    simp only [disjoint_union_right, disjoint_singleton_right], refine ⟨M.disj a ha j hj.1 h.2,_⟩,
    intro hv, exact h.1 (uniq_part ha hvi.1 hv hvi.2),
    have:=M.disj i hvi.1 b hb  h_2.1.symm,apply disjoint_of_subset_left _ this, exact erase_subset _ _, 
    exfalso, push_neg at h, push_neg at h_2,rw [h_1,h_3] at ne, exact ne rfl,
    simp only [disjoint_union_right, disjoint_singleton_right, mem_erase, _root_.ne.def, eq_self_iff_true, not_true, false_and,
    not_false_iff, and_true],
    have:=M.disj i hvi.1 j hj.1 hj.2.symm, apply disjoint_of_subset_left _ this, exact erase_subset _ _, 
    simp only [disjoint_union_left, disjoint_singleton_right],
    refine ⟨M.disj j hj.1 b hb h_2.2.symm,_⟩, rw disjoint_singleton_left,
    intro hb2, have:= uniq_part hb hvi.1 hb2 hvi.2 , exact h_2.1 this,
    simp only [disjoint_union_left, disjoint_singleton_left, mem_erase, _root_.ne.def, eq_self_iff_true, not_true, false_and,
  not_false_iff, and_true],
    have:=M.disj j hj.1  i hvi.1 hj.2, apply disjoint_of_subset_right _ this, exact erase_subset _ _, 
    exfalso, push_neg at h_2,push_neg at h, have bj:= h_2 h_3, have aj:= h h_1,rw aj at ne, rw bj at ne, exact ne rfl,
end,}

-- new whole is same as old
lemma move_A {M : multi_part α} {v : α} {i j: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) :(move M hvi hj).A=M.A:=
rfl

-- the moved partition still has t+1 parts
lemma move_t {M : multi_part α} {v : α} {i j: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) :(move M hvi hj).t=M.t:=
 rfl

-- the moved parts are the same except for P i and P j which have lost/gained v
lemma move_P {M : multi_part α} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) : k∈ range(M.t+1) → ((move M hvi hj).P k) = ite (k≠i ∧k≠j) (M.P k) (ite (k=i) ((M.P i).erase v) ((M.P j) ∪ {v})):=
begin
  intros k , refl,
end

-- the sizes of parts changed by moving v 
lemma move_Pcard {M : multi_part α} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) : k∈ range(M.t+1) → ((move M hvi hj).P k).card = ite (k≠i ∧k≠j) (M.P k).card (ite (k=i) ((M.P i).card -1) ((M.P j).card+1)):=
begin
  intros hk,rw move_P hvi hj hk,split_ifs, 
  refl,  exact card_erase_of_mem hvi.2,
  have jv:=uniq_part' hvi.1 hj.1 hj.2.symm hvi.2,
  rw ← disjoint_singleton_right at jv,
  apply card_disjoint_union jv,
end

--- the complement of the part with v has gained v
lemma sdiff_erase {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∈ B) : A\(B.erase v)=(A\B) ∪ {v} :=
begin
  ext, split, intro h, rw [mem_union,mem_sdiff] at *,rw mem_sdiff at h,rw mem_erase at h,
  push_neg at h, by_cases h': a=v,right, exact mem_singleton.mpr h',
  left, exact ⟨h.1,(h.2 h')⟩,
  intros h,rw mem_sdiff,rw mem_erase,rw [mem_union,mem_sdiff] at h, push_neg,
  cases h,exact ⟨h.1,λi,h.2⟩,by_contra h',push_neg at h',
  have ha:=hB hv,
  have:=mem_singleton.mp h, rw ← this at ha,
  have h2:=h' ha, exact h2.1 this,
end

--size of complement of erased part has increased
lemma card_sdiff_erase {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∈ B) : (A\(B.erase v)).card=(A\B).card+1 :=
begin
  have hv2: v∉A\B, {rw mem_sdiff,push_neg,intro i, exact hv,},
  have:=disjoint_singleton_right.mpr hv2,
  rw sdiff_erase hB hv, exact card_disjoint_union this,
end

--  complement of part without v has lost v 
lemma sdiff_insert {v : α} {A B :finset α} (hB: B⊆A) (hv: v ∉ B) : A\(B ∪  {v})=(A\B).erase v:= 
begin
  ext,split,intro h,
  rw mem_erase, rw mem_sdiff at *,rw mem_union at h, push_neg at h,rw mem_singleton at h,  exact ⟨h.2.2,h.1,h.2.1⟩,
  intro h,rw mem_erase at h, rw mem_sdiff, rw mem_union, push_neg,rw mem_singleton, rw mem_sdiff at h, exact ⟨h.2.1,h.2.2,h.1⟩,
end

---size of complement decreased
lemma card_sdiff_insert {v : α} {A B :finset α} (hB: B⊆A) (hvB: v ∉ B) (hvA: v ∈ A) : (A\(B ∪ {v})).card=(A\B).card -1:= 
begin
  have : v∈A\B:=mem_sdiff.mpr ⟨hvA,hvB⟩,
  rw sdiff_insert hB hvB, exact card_erase_of_mem this,
end

-- how have the sizes of the complements of parts changed by moving v
lemma move_Pcard_sdiff {M : multi_part α} {v : α} {i j k: ℕ} (hvi: i∈ range(M.t+1) ∧ v∈ M.P i) (hj : j∈range(M.t+1) ∧ j≠i) :
 k∈ range(M.t+1) → (((move M hvi hj).A)\((move M hvi hj).P k)).card = ite (k≠i ∧k≠j) ((M.A)\(M.P k)).card (ite (k=i) (((M.A)\(M.P i)).card +1) (((M.A)\(M.P j)).card-1)):=
begin
  intros hk,rw move_P hvi hj hk,rw move_A hvi hj,split_ifs, refl,
  exact card_sdiff_erase (sub_part  hvi.1) hvi.2,
  exact card_sdiff_insert (sub_part  hj.1) (uniq_part' hvi.1 hj.1 hj.2.symm hvi.2) (mem_part hvi.1 hvi.2),
end

-- key increment inequality we need to show moving a vertex in a moveable partition is increases deg sum
lemma move_change {a b n:ℕ} (hb: b+1<a) (hn: a+b ≤ n):  a*(n-a) +b*(n-b) < (a-1)*(n-a+1)+ (b+1)*(n-b-1):=
begin
  rw mul_add, rw add_mul,rw mul_one, rw one_mul,
  have ha:=tsub_add_cancel_of_le (by linarith [hb]: 1 ≤ a),
  have h2: a ≤ n-b:=le_tsub_of_add_le_right hn,
  have hnb:=tsub_add_cancel_of_le  (le_trans (by linarith [hb]: 1 ≤ a) h2),
  nth_rewrite 0 ← ha, nth_rewrite 0 ← hnb,
  rw [add_mul,mul_add,one_mul,mul_one ,add_assoc,add_assoc],
  apply nat.add_lt_add_left,
  rw [add_comm, ← add_assoc, add_comm (a-1), add_assoc, add_assoc],
  apply nat.add_lt_add_left,
  have ab: b< a-1,{by linarith [hb],},
  have nba: (n-a)< (n-b-1),{
    have nba': (n-a)<(n-(b+1)),{
      have h3:=tsub_pos_of_lt hb,
      have h4: a ≤ n :=by linarith,
      have h6:=tsub_add_tsub_cancel (h4) (le_of_lt hb),
      linarith,}, rw add_comm at nba',
      rwa tsub_add_eq_tsub_tsub_swap at nba',},
  exact nat.add_lt_add ab nba,
end

end mpartition