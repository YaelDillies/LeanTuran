/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import simplicial_complex.pure

/-!
# Skeleton of a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n k : ℕ}
  {K : simplicial_complex 𝕜 E} {s t : finset E} {A : set (finset E)}

/-- The `k`-skeleton of a simplicial complex is the simplicial complex made of its simplices of
dimension less than `k`. -/
def skeleton (K : simplicial_complex 𝕜 E) (k : ℕ) : simplicial_complex 𝕜 E :=
K.of_subcomplex'
  {s | s ∈ K ∧ s.card ≤ k + 1}
  (λ s ⟨hs, _⟩, hs)
  (λ s t hs hts ht, ⟨K.down_closed' hs.1 hts ht, (card_le_of_subset hts).trans hs.2⟩)

lemma skeleton_le : K.skeleton k ≤ K := K.of_subcomplex_le _

lemma skeleton_bot (k : ℕ) : (⊥ : simplicial_complex 𝕜 E).skeleton k = ⊥ := of_subcomplex_bot _

lemma skeleton_nonempty_iff : (K.skeleton k).faces.nonempty ↔ K.faces.nonempty :=
begin
  refine ⟨set.nonempty.mono skeleton_le, _⟩,
  rintro ⟨s, hs⟩,
  obtain ⟨x, hx⟩ := K.nonempty hs,
  refine ⟨{x}, K.down_closed' hs (singleton_subset_iff.2 hx) $ singleton_nonempty _, _⟩,
  rw card_singleton,
  exact le_add_self,
end

lemma pure.skeleton_of_le (hK : K.pure n) (h : k ≤ n) : (K.skeleton k).pure k :=
begin
  refine ⟨λ s hs, hs.2, _⟩,
  rintro s ⟨⟨hs, hscard⟩, hsmax⟩,
  obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_of_card_le (add_le_add_right h 1) hs hscard,
  rwa hsmax ⟨ht, htcard.le⟩ hst,
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] [finite_dimensional 𝕜 E]
  {m n k : ℕ} {K : simplicial_complex 𝕜 E} {s t : finset E} {A : set (finset E)}

lemma pure.skeleton (hK : K.pure n) : (K.skeleton k).pure (min k n) :=
begin
  obtain hn | hn := le_total k n,
  { rw min_eq_left hn,
    exact hK.skeleton_of_le hn },
  { rw min_eq_right hn,
    refine ⟨λ s hs, hK.1 $ skeleton_le hs, λ s hs, _⟩,
    obtain ⟨t, ht, hst⟩ := subfacet (skeleton_le hs.1),
    rw hs.2 ⟨facets_subset ht, (hK.2 ht).le.trans (add_le_add_right hn _)⟩ hst,
    exact hK.2 ht }
end

end linear_ordered_field
end geometry.simplicial_complex
