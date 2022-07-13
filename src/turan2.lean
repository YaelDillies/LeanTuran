import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import tactic.core
import algebra.big_operators
open finset fintype

open_locale big_operators classical
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


-- complete (t+1) partite graph with n vertices
def  Turan_Graph (t n : ℕ) : simple_graph (fin (n+1)):=
begin
  induction t with t ht,
  induction n with n hn,
  exact ⊥, exact ⊥,
  choose b hb1 hb2 using (tn_max_mem t n n ((self_mem_range_succ n))),

  exact ⊤,
end



