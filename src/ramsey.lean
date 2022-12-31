import combinatorics.simple_graph.clique
import combinatorics.simple_graph.degree_sum
import data.finset.basic
import data.nat.basic
import tactic.core
import algebra.big_operators


open finset nat 
open_locale big_operators classical


variable {α : Type} 
variable [fintype α]
variable {t : ℕ}


lemma card_rels : fintype.card (α → α → Prop) = 2^((fintype.card α)^2):=
begin
  rw [pow_two,fintype.card_fun,pow_mul,fintype.card_fun, fintype.card_Prop],
end

def equiv_of_symm_irr : equiv {r : α → α → Prop // symmetric r ∧ irreflexive r} (set ({s:finset α // card s = 2})):=
{ to_fun :=
begin
  intro r, rintros ⟨s,ps⟩,
  rw card_eq_two at ps,
  exact r.1 ps.some ps.some_spec.some,
end,
inv_fun :=
begin 
  rintros A,
  refine ⟨_,_,_⟩,
  intros x y,
  by_cases x=y,
  exact false,
  exact  (⟨({x,y}:finset α), card_eq_two.2 ⟨x ,y ,h, rfl⟩ ⟩:({s:finset α// card s = 2})) ∈ A,
  intros x y, dsimp, split_ifs,
  exact false.elim,
  exact false.elim,
  exfalso, exact h (h_1.symm),
  intros h,
  have : ({x,y}:finset α) = {y,x},{
    ext,
    simp only [mem_insert, mem_singleton],
    tauto,
  },
  simp_rw ← this, exact h,
  intros x h1,
  split_ifs at h1;exact h1,
end,
left_inv :=
begin 

  sorry,
end,  
right_inv :=
begin 
  sorry,
end,
}


lemma card_symrels : fintype.card {r : α → α → Prop // symmetric r ∧ irreflexive r} = 2^((fintype.card α).choose 2):=
begin
  rw ← fintype.card_finset_len,
  rw fintype.card_congr equiv_of_symm_irr, exact fintype.card_set,
  apply_instance,
end


/-- The number of possible t-cliques in a a simple_graph α is {card α choose t}-/
lemma card_cliques : card (powerset_len t (univ:finset α)) = nat.choose (fintype.card α) t:=
begin
  rw [card_powerset_len, card_univ],
end

@[reducible]def graphs_with_clique (s : finset α) : set (simple_graph α) :=  {G:simple_graph α | G.is_clique s}



@[simp]lemma empty_clique (G: simple_graph α) : G.is_clique ∅ :=
begin
 intros a ha, exfalso, exact not_mem_empty a ha,
end



@[ext]lemma graph_ext (G H :simple_graph α) : G = H ↔ ∀ u v, G.adj u v = H.adj u v:=
begin
  split, 
  intro h,rw h, intros u v, refl,
  intro h, 
  ext x y,
  rw h x y,
end


def edge_set_to_graph : set ((powerset_len 2 (univ:finset α))) → (simple_graph α):= λ padj,
{ adj := 
begin 
  intros u v, 
  by_cases u = v,
    exact false,
  set ed:=({u,v}:finset α) with hed,
  have : ed ∈ powerset_len 2 univ,
  {
    rw mem_powerset_len,
    exact ⟨subset_univ _,card_eq_two.2 ⟨u,v,h,hed⟩⟩,
  },
  have nt:(powerset_len 2 (univ:finset α)):=subtype.mk ed this,
  exact nt ∈ padj,
end,
symm := 
begin 
  intros u v,dsimp,
  split_ifs,
  exact false.elim,
  exact false.elim,
  exfalso, apply h (h_1.symm),
  intro hadj,
  have : ({u,v}:finset α)= {v,u},
  {
    ext,
    simp only [mem_insert, mem_singleton],
    tauto,
  },
  simp_rw ← this,
  assumption,
end,
loopless := 
begin 
  obviously,
end}

def graph_to_edge_set : (simple_graph α) → set ((powerset_len 2 (univ:finset α))):= 
begin
  intro G,
  rintro ⟨pair,pr⟩,
  rw mem_powerset_len at pr,
  obtain ⟨pr1,pr2⟩:=pr,
  rw card_eq_two at pr2,
  exact G.adj pr2.some pr2.some_spec.some,
end


def graph_equiv :equiv (simple_graph α) (set (powerset_len 2 (univ:finset α))) :={ 
to_fun :=graph_to_edge_set,
inv_fun :=edge_set_to_graph,
left_inv :=
begin
  intro G,
  ext u v,
  unfold edge_set_to_graph,
  dsimp,
--  unfold graph_to_edge_set,
  --dsimp,
  split_ifs,
  simp,
  rw h, exact G.loopless _,

  split,
  intros h1,
  unfold graph_to_edge_set at h1,
  dsimp at h1,
  have : ({u,v}:finset α) ∈ powerset_len 2 univ,
  {
    rw mem_powerset_len,
    exact ⟨subset_univ _,card_eq_two.2 ⟨u,v,h,rfl⟩⟩,
  },
  sorry,
  intros h1,
  unfold graph_to_edge_set,
  dsimp,
  have : ({u,v}:finset α) ∈ powerset_len 2 univ,
  {
    rw mem_powerset_len,
    exact ⟨subset_univ _,card_eq_two.2 ⟨u,v,h,rfl⟩⟩,
  },
  


  sorry,
end,
right_inv :=
begin
   sorry,
end,
}




@[simp]lemma card_graphs' : fintype.card (simple_graph α) =  2^fintype.card (powerset_len 2 (univ:finset α)):=
begin
  have : equiv (simple_graph α) (set (powerset_len 2 (univ:finset α))),{
    sorry,
  }  ,
  rw fintype.card_congr this,simp only [fintype.card_set],
end

@[simp]lemma card_graphs : fintype.card (simple_graph α) = 2^(nat.choose (fintype.card α) 2):=
begin
  simpa only [card_graphs', fintype.card_coe, card_powerset_len],
end


lemma card_graphs_with_clique {s : finset α} (hs : s ∈ powerset_len t (univ:finset α)) :
 fintype.card (graphs_with_clique s) = 2^((nat.choose (fintype.card α) 2) - (nat.choose t 2)):=
 begin
  cases t with t ht,
  simp only [fintype.card_of_finset, filter_congr_decidable, choose_zero_succ, tsub_zero],
  rw [powerset_len_zero,mem_singleton] at hs, rw hs,
  dsimp, 
  simp only [empty_clique, filter_true_of_mem, mem_univ, forall_const],
  exact card_graphs,
  rw mem_powerset_len at hs,
--  obtain ⟨hs1,hs2⟩:=hs,
  simp only [set.coe_set_of],

  sorry,
 end


