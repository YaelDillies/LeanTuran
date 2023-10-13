import analysis.convex.simplicial_complex.basic
import mathlib.analysis.convex.combination
import mathlib.linear_algebra.affine_space.independent
import mathlib.linear_algebra.affine_space.finite_dimensional

open finset geometry
open_locale affine big_operators classical

variables {𝕜 E ι : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {K K₁ K₂ : simplicial_complex 𝕜 E} {x y : E} {s t : finset E} {A : set (finset E)} {m n : ℕ}

protected lemma nonempty (K : simplicial_complex 𝕜 E) (hs : s ∈ K) : s.nonempty :=
nonempty_of_ne_empty $ ne_of_mem_of_not_mem hs K.not_empty_mem

--TODO: Replace `down_closed`
protected lemma down_closed' (K : simplicial_complex 𝕜 E) (hs : s ∈ K.faces) (hts : t ⊆ s)
  (ht : t.nonempty) : t ∈ K.faces := K.down_closed hs hts ht.ne_empty

@[simp] lemma mem_faces_iff (K : simplicial_complex 𝕜 E) : s ∈ K.faces ↔ s ∈ K := iff.rfl

lemma le_def : K₁ ≤ K₂ ↔ K₁.faces ⊆ K₂.faces := iff.rfl

lemma eq_bot_of_forall_not_mem (K : simplicial_complex 𝕜 E) (h : ∀ s, s ∉ K) : K = ⊥ :=
by { ext s, exact iff_of_false (h s) id }

lemma facets_singleton (hK : K.faces = {s}) : K.facets = {s} :=
begin
  rw set.eq_singleton_iff_unique_mem at ⊢ hK,
  exact ⟨⟨hK.1, λ t ht _, (hK.2 _ ht).symm⟩, λ t ht, hK.2 _ ht.1⟩,
end

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps] def of_subcomplex' (K : simplicial_complex 𝕜 E)
  (faces : set (finset E))
  (subset : faces ⊆ K.faces)
  (down_closed : ∀ ⦃s t : finset E⦄, s ∈ faces → t ⊆ s → t.nonempty → t ∈ faces) :
  simplicial_complex 𝕜 E :=
{ faces := faces,
  not_empty_mem := λ h, K.not_empty_mem (subset h),
  indep := λ s hs, K.indep (subset hs),
  down_closed := λ s t hs hts ht, down_closed hs hts $ nonempty_iff_ne_empty.2 ht,
  inter_subset_convex_hull := λ s t hs ht, K.inter_subset_convex_hull (subset hs) (subset ht) }

lemma of_subcomplex_le (K : simplicial_complex 𝕜 E) (faces) {subset down_closed} :
  K.of_subcomplex' faces subset down_closed ≤ K :=
subset

lemma of_subcomplex_bot (faces) {subset down_closed} :
  (⊥ : simplicial_complex 𝕜 E).of_subcomplex' faces subset down_closed = ⊥ :=
le_bot_iff.1 $ of_subcomplex_le _ _

lemma mem_of_mem_convex_hull (hx : x ∈ K.vertices) (hs : s ∈ K)
 (hxs : x ∈ convex_hull 𝕜 (s : set E)) :
  x ∈ s :=
begin
  have h := K.inter_subset_convex_hull hx hs ⟨by simp, hxs⟩,
  by_contra H,
  norm_cast at h,
  rwa [inter_comm, disjoint_iff_inter_eq_empty.1 (disjoint_singleton_right.2 H), coe_empty,
    convex_hull_empty] at h,
end

lemma subset_of_convex_hull_subset_convex_hull (hs : s ∈ K) (ht : t ∈ K)
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) : s ⊆ t :=
λ x hxs, mem_of_mem_convex_hull (K.down_closed' hs (singleton_subset_iff.2 hxs) $
  singleton_nonempty _) ht $ hst $ subset_convex_hull 𝕜 ↑s hxs

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]
  {K : simplicial_complex 𝕜 E} {x y : E} {s t : finset E} {A : set (finset E)} {m n : ℕ}

/-- A constructor for simplicial complexes by specifying a set of faces to close downward. -/
@[simps] def of_set_closure
  (indep : ∀ {s : finset E}, s ∈ A → affine_independent 𝕜 (coe : (s : set E) → E))
  (inter_subset_convex_hull : ∀ {s t}, s ∈ A → t ∈ A →
    convex_hull 𝕜 ↑s ∩ convex_hull 𝕜 ↑t ⊆ convex_hull 𝕜 (s ∩ t : set E)) :
  simplicial_complex 𝕜 E :=
{ faces := {s | s.nonempty ∧ ∃ t, t ∈ A ∧ s ⊆ t},
  indep := λ s ⟨hs, t, ht, hst⟩, (indep ht).mono hst,
  down_closed := λ s t ⟨hs, u, hu, hsu⟩ hts ht, ⟨nonempty_iff_ne_empty.2 ht, u, hu, hts.trans hsu⟩,
  inter_subset_convex_hull :=
  begin
    rintro v s ⟨hv, t, ht, hvt⟩ ⟨hs, u, hu, hsu⟩ x ⟨hxv, hxs⟩,
    have hxtu : x ∈ convex_hull 𝕜 (t ∩ u : set E) :=
      inter_subset_convex_hull ht hu ⟨convex_hull_mono hvt hxv, convex_hull_mono hsu hxs⟩,
    have hxvu : x ∈ convex_hull 𝕜 (v ∩ u : set E),
    { have := affine_independent.subset_convex_hull_inter (indep ht) hvt (inter_subset_left t u),
      norm_cast at this hxtu,
      exact_mod_cast convex_hull_mono
        (inter_subset_inter_left $ inter_subset_right t u) (this ⟨hxv, hxtu⟩) },
    have hxts : x ∈ convex_hull 𝕜 (t ∩ s : set E),
    { have := affine_independent.subset_convex_hull_inter (indep hu) (inter_subset_right t u) hsu,
      norm_cast at this hxtu,
      exact_mod_cast convex_hull_mono
        (inter_subset_inter_right $ inter_subset_left t u) (this ⟨hxtu, hxs⟩) },
    norm_cast at hxvu hxts,
    have hxvs := affine_independent.subset_convex_hull_inter (indep ht)
      ((inter_subset_inter_right hvt).trans $ inter_subset_left t u)
      (inter_subset_left t s) ⟨hxvu, hxts⟩,
    norm_cast at hxvs,
    exact_mod_cast convex_hull_mono ((inter_subset_inter_right $ inter_subset_left v u).trans $
      inter_subset_inter_left $ inter_subset_right t s) hxvs,
  end,
  not_empty_mem := λ h, h.1.ne_empty rfl }

/-- A constructor for simplicial complexes by specifying a face to close downward. -/
@[simp] def of_simplex (indep : affine_independent 𝕜 (coe : s → E)) :
  simplicial_complex 𝕜 E :=
of_set_closure
  begin rintro t (ht : t = s), rw ht, exact indep end
  begin rintro t u (ht : t = s) (hu : u = s), rw [ht, hu, set.inter_self _, set.inter_self _],
    exact set.subset.rfl end

lemma mem_of_simplex (hs : affine_independent 𝕜 (coe : s → E)) :
  t ∈ of_simplex hs ↔ t.nonempty ∧ t ⊆ s :=
begin
  refine ⟨_, λ h, ⟨h.1, s, rfl, h.2⟩⟩,
  rintro ⟨ht, u, (rfl : u = s), hts⟩,
  exact ⟨ht, hts⟩,
end

variables {𝕜 E}

-- Corollary of `affine_independent.card_le_finrank_succ`
lemma face_dimension_le_space_dimension [finite_dimensional 𝕜 E] (hs : s ∈ K) :
  s.card ≤ finite_dimensional.finrank 𝕜 E + 1 :=
by simpa using (K.indep hs).card_le_finrank_succ.trans (add_le_add_right (submodule.finrank_le _) _)

lemma subfacet [finite_dimensional 𝕜 E] (hs : s ∈ K) : ∃ {t}, t ∈ K.facets ∧ s ⊆ t :=
begin
  have := id hs,
  revert this,
  apply strong_downward_induction_on s,
  { rintro t h htcard ht,
    by_cases htfacet : t ∈ K.facets,
    { exact ⟨t, htfacet, subset.refl _⟩ },
    obtain ⟨u, hu, htu⟩ := (not_facet_iff_subface ht).mp htfacet,
    obtain ⟨v, hv⟩ := h (face_dimension_le_space_dimension hu) htu hu,
    exact ⟨v, hv.1, htu.1.trans hv.2⟩ },
  exact face_dimension_le_space_dimension hs,
end

lemma facets_eq_empty_iff [finite_dimensional 𝕜 E] : K.facets = ∅ ↔ K = ⊥ :=
begin
  refine ⟨λ h, _, _⟩,
  { ext s,
    refine iff_of_false (λ hs, _) (set.not_mem_empty _),
    obtain ⟨t, ht, hst⟩ := subfacet hs,
    exact h.subset ht },
  { rintro rfl,
    exact facets_bot }
end

end linear_ordered_field
end geometry.simplicial_complex
