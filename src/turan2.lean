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
variables {t n : ℕ} 
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

variables {α : Type*}[fintype α][inhabited α][decidable_eq α]

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
    intros i hi j hj ne, split_ifs, 
    refine M.disj i _ j _ ne, sorry,
  sorry, sorry,sorry,sorry,
  end,
  deg_sum:= begin
  sorry,
  end,}


end simple_graph



