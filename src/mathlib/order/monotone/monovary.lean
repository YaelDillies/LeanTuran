import order.monotone.monovary
import set_theory.ordinal.basic

open function set
variables {ι ι' α β γ : Type*}

section preorder
variables [preorder α] [preorder β] [preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s t : set ι}

lemma monovary_on_iff_monovary : monovary_on f g s ↔ monovary (λ i : s, f i) (λ i, g i) :=
by simp [monovary, monovary_on]

lemma antivary_on_iff_antivary : antivary_on f g s ↔ antivary (λ i : s, f i) (λ i, g i) :=
by simp [antivary, antivary_on]

section partial_order
variables [partial_order ι]

lemma strict_mono.trans_monovary (hf : strict_mono f) (h : monovary g f) : monotone g :=
monotone_iff_forall_lt.2 $ λ a b hab, h $ hf hab

lemma strict_mono.trans_antivary (hf : strict_mono f) (h : antivary g f) : antitone g :=
antitone_iff_forall_lt.2 $ λ a b hab, h $ hf hab

lemma strict_anti.trans_monovary (hf : strict_anti f) (h : monovary g f) : antitone g :=
antitone_iff_forall_lt.2 $ λ a b hab, h $ hf hab

lemma strict_anti.trans_antivary (hf : strict_anti f) (h : antivary g f) : monotone g :=
monotone_iff_forall_lt.2 $ λ a b hab, h $ hf hab

lemma strict_mono_on.trans_monovary_on (hf : strict_mono_on f s) (h : monovary_on g f s) :
  monotone_on g s :=
monotone_on_iff_forall_lt.2 $ λ a ha b hb hab, h ha hb $ hf ha hb hab

lemma strict_mono_on.trans_antivary_on (hf : strict_mono_on f s) (h : antivary_on g f s) :
  antitone_on g s :=
antitone_on_iff_forall_lt.2 $ λ a ha b hb hab, h ha hb $ hf ha hb hab

lemma strict_anti_on.trans_monovary_on (hf : strict_anti_on f s) (h : monovary_on g f s) :
  antitone_on g s :=
antitone_on_iff_forall_lt.2 $ λ a ha b hb hab, h hb ha $ hf ha hb hab

lemma strict_anti_on.trans_antivary_on (hf : strict_anti_on f s) (h : antivary_on g f s) :
  monotone_on g s :=
monotone_on_iff_forall_lt.2 $ λ a ha b hb hab, h hb ha $ hf ha hb hab

end partial_order
end preorder


section
variables [linear_order α] [linear_order β] (f : ι → α) (g : ι → β) {s : set ι}

/-- If `f : ι → α` and `g : ι → β` are monovarying, then `monovary_order f g` is a linear order on
`ι` that makes `f` and `g` simultaneously monotone.
We define `i < j` if `f i < f j`, or if `f i = f j` and `g i < g j`, breaking ties arbitrarily. -/
def monovary_order (i j : ι) : Prop :=
prod.lex (<) (prod.lex (<) well_ordering_rel) (f i, g i, i) (f j, g j, j)

instance : is_strict_total_order ι (monovary_order f g) :=
{ trichotomous := λ i j, begin
    convert trichotomous_of (prod.lex (<) $ prod.lex (<) well_ordering_rel) _ _,
    { simp only [prod.ext_iff, ←and_assoc, imp_and_distrib, eq_iff_iff, iff_and_self],
      exact ⟨congr_arg _, congr_arg _⟩ },
    { apply_instance }
  end,
  irrefl := λ i, by { rw monovary_order, exact irrefl _ },
  trans := λ i j k, by { rw monovary_order, exact trans } }

variables {f g}

lemma monovary_on_iff_exists_monotone_on :
  monovary_on f g s ↔ ∃ [linear_order ι], by exactI monotone_on f s ∧ monotone_on g s :=
begin
  classical,
  letI := linear_order_of_STO (monovary_order f g),
  refine ⟨λ hfg, ⟨‹_›, monotone_on_iff_forall_lt.2 $ λ i hi j hj hij, _,
    monotone_on_iff_forall_lt.2 $ λ i hi j hj hij, _⟩, _⟩,
  { obtain h | ⟨h, -⟩ := prod.lex_iff.1 hij; exact h.le },
  { obtain h | ⟨-, h⟩ := prod.lex_iff.1 hij,
    { exact hfg.symm hi hj h },
    obtain h | ⟨h, -⟩ := prod.lex_iff.1 h; exact h.le },
  { rintro ⟨_, hf, hg⟩,
    exactI hf.monovary_on hg }
end

lemma antivary_on_iff_exists_monotone_on_antitone_on :
  antivary_on f g s ↔ ∃ [linear_order ι], by exactI monotone_on f s ∧ antitone_on g s :=
by simp_rw [←monovary_on_to_dual_right, monovary_on_iff_exists_monotone_on,
  monotone_on_to_dual_comp_iff]

lemma monovary_on_iff_exists_antitone_on :
  monovary_on f g s ↔ ∃ [linear_order ι], by exactI antitone_on f s ∧ antitone_on g s :=
by simp_rw [←antivary_on_to_dual_left, antivary_on_iff_exists_monotone_on_antitone_on,
  monotone_on_to_dual_comp_iff]

lemma antivary_on_iff_exists_antitone_on_monotone_on :
  antivary_on f g s ↔ ∃ [linear_order ι], by exactI antitone_on f s ∧ monotone_on g  s:=
by simp_rw [←monovary_on_to_dual_left, monovary_on_iff_exists_monotone_on,
  monotone_on_to_dual_comp_iff]

lemma monovary_iff_exists_monotone :
  monovary f g ↔ ∃ [linear_order ι], by exactI monotone f ∧ monotone g :=
by simp [←monovary_on_univ, monovary_on_iff_exists_monotone_on]

lemma antivary_iff_exists_monotone_antitone :
  antivary f g ↔ ∃ [linear_order ι], by exactI monotone f ∧ antitone g :=
by simp [←antivary_on_univ, antivary_on_iff_exists_monotone_on_antitone_on]

lemma monovary_iff_exists_antitone :
  monovary f g ↔ ∃ [linear_order ι], by exactI antitone f ∧ antitone g :=
by simp [←monovary_on_univ, monovary_on_iff_exists_antitone_on]

lemma antivary_iff_exists_antitone_monotone :
  antivary f g ↔ ∃ [linear_order ι], by exactI antitone f ∧ monotone g :=
by simp [←antivary_on_univ, antivary_on_iff_exists_antitone_on_monotone_on]

alias monovary_on_iff_exists_monotone_on ↔ monovary_on.exists_monotone_on _
alias antivary_on_iff_exists_monotone_on_antitone_on ↔ antivary_on.exists_monotone_on_antitone_on _
alias monovary_on_iff_exists_antitone_on ↔ monovary_on.exists_antitone_on _
alias antivary_on_iff_exists_antitone_on_monotone_on ↔ antivary_on.exists_antitone_on_monotone_on _
alias monovary_iff_exists_monotone ↔ monovary.exists_monotone _
alias antivary_iff_exists_monotone_antitone ↔ antivary.exists_monotone_antitone _
alias monovary_iff_exists_antitone ↔ monovary.exists_antitone _
alias antivary_iff_exists_antitone_monotone ↔ antivary.exists_antitone_monotone _

end
