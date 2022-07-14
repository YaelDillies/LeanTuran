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


lemma tn_simp (t :ℕ): turan_numb t 0 = 0:=by cases t;refl

lemma tn_simp' (n :ℕ): turan_numb 0 n = 0:=by cases n;refl

lemma tn_le (t c n : ℕ) (h: c ∈ range (n+1)): turan_numb t c +c*(n+1-c) ≤ turan_numb (t+1) (n+1):=
begin
  obtain ⟨x, hx : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have := finset.le_max_of_mem (mem_image_of_mem _ h) hx,
  rw [turan_numb, hx], apply le_trans this,refl,
end

-- obtain the optimal choice of size of new part in turan graph T (t+1)(n+1)
lemma tn_max_mem (t c n : ℕ) (h: c∈ range (n+1)) : ∃b∈ range(n+1), turan_numb t b +b*(n+1-b) = turan_numb (t+1) (n+1):=
begin
  obtain ⟨i, hi : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λa, turan_numb t a + a*(n+1-a)) h),
  have :=mem_of_max  hi,
   rw mem_image at this,
  rcases this with ⟨b,hbr,hbm⟩,
  use [b,hbr],
  rw [turan_numb, hi, hbm],refl,
end


lemma mysucc (h: 0 <n) :∃m:ℕ, m.succ=n :=
begin
use n.pred, apply succ_pred_eq_of_pos h,
end



lemma maxlistsum (t n : ℕ) : ∃l:list ℕ,l.length=t+1 ∧ l.sum=n ∧ n^2=(l.map (λi,i^2)).sum +2*turan_numb t n:=
begin
  revert n,
  induction t with t ht,
  intro n, rw [zero_add,tn_simp',mul_zero],
  use [[n]],dsimp, simp only [eq_self_iff_true, list.sum_cons, list.sum_nil, add_zero, and_self] at *,
  intro n,
--  induction n using nat.strong_induction_on with n hn,
  cases nat.eq_zero_or_pos n with hn0,
  rcases ht 0 with ⟨h0,h1,h2,h3⟩,
  rw [tn_simp,mul_zero,zero_pow (by norm_num:0<2)] at h3,
  set ml:= 0 :: h0,
  use ml,
  simp only [list.length, list.map, add_left_inj, list.sum_cons, zero_add, nat.nat_zero_eq_zero, zero_pow', ne.def, bit0_eq_zero,
  nat.one_ne_zero, not_false_iff, add_zero], rw [hn0,zero_pow (by norm_num:0<2),tn_simp,mul_zero,add_zero ],
  exact ⟨h1,h2,h3⟩,
  have ms:=succ_pred_eq_of_pos h,
  set m:=n.pred with m,rw ← ms,
----inductive step 
sorry,
end






-- form list [b,b,...b] of length a
def mylist : ℕ → ℕ → list ℕ
| 0   b   := []
|(a+1)  b   :=  b :: mylist a b

def addlist : list ℕ → list ℕ → list ℕ
| [] _ := []
| _ [] := []
| (a :: l) (b :: m)  :=(a+b):: addlist l m







-- given t and n return the size of the next part in turan (t+1) partite graph of order n
noncomputable theory
def  Turan_part  : ℕ → ℕ → ℕ:=
begin
  intros t n,
  by_cases hn: n=0, exact 0,
  by_cases ht: n=0, exact  n,
  choose m hm using nat.exists_eq_succ_of_ne_zero hn, 
  choose s hs using nat.exists_eq_succ_of_ne_zero ht, 
  choose b hb1 hb2 using (tn_max_mem s m m ((self_mem_range_succ m))),
  exact b,
end



end simple_graph



