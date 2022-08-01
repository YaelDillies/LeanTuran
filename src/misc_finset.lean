import data.finset.basic
import data.fintype.basic
import data.nat.basic
import tactic.core

open finset

-- just some lemmas that I couldn't quite find in finset.basic

variables {α : Type*} [fintype α][nonempty α][decidable_eq α]
--probably easier ways of doing this...
--if A and B are disjoint then seo are A ∩ C and B ∩ D for any C,D
lemma disj_of_inter_disj (C D :finset α){A B :finset α} (h: disjoint A B): disjoint (A∩C) (B∩D):=
disjoint.mono (le_iff_subset.mpr (inter_subset_left A C)) (inter_subset_left B D) h

--if A and B are disjoint then seo are C ∩ A and D ∩ B for any C,D
lemma disj_of_disj_inter (C D :finset α){A B :finset α} (h: disjoint A B): disjoint (C∩A ) (D∩B):=
disjoint.mono (le_iff_subset.mpr (inter_subset_right C A)) (inter_subset_right D B) h

-- in particular (B ∩ C) and (A\B ∩ C) are disjoint
lemma sdiff_inter_disj (A B C:finset α) : disjoint (B ∩ C)  (A\B ∩ C):=
disj_of_inter_disj C C disjoint_sdiff

#lint