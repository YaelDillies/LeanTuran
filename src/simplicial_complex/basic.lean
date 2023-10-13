/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import mathlib.analysis.convex.simplicial_complex.basic
import mathlib.linear_algebra.affine_space.independent
import simplicial_complex.simplex

/-!
# Simplicial complexes
-/

open finset geometry
open_locale affine big_operators classical

variables {𝕜 E ι : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E]
  {K K₁ K₂ : simplicial_complex 𝕜 E} {x y : E} {s t : finset E} {A : set (finset E)} {m n : ℕ}

/-- The cells of a simplicial complex are its simplices whose dimension matches the one of the
space. -/
def cells (K : simplicial_complex 𝕜 E) : set (finset E) :=
{s | s ∈ K ∧ s.card = finite_dimensional.finrank 𝕜 E + 1}

/-- The subcells of a simplicial complex are its simplices whose cardinality matches the dimension
of the space. They are thus one smaller than cells. -/
def subcells (K : simplicial_complex 𝕜 E) : set (finset E) :=
{s | s ∈ K ∧ s.card = finite_dimensional.finrank 𝕜 E}

lemma disjoint_interiors (hs : s ∈ K) (ht : t ∈ K) (hxs : x ∈ combi_interior 𝕜 s)
  (hxt : x ∈ combi_interior 𝕜 t) :
  s = t :=
begin
  by_contra,
  have hst : s ∩ t ⊂ s,
  { use inter_subset_left s t,
    intro H,
    exact hxt.2 (set.mem_bUnion ⟨subset.trans H (inter_subset_right s t), (λ H2,
      h (subset.antisymm (subset.trans H (inter_subset_right s t)) H2))⟩ hxs.1) },
  refine hxs.2 (set.mem_bUnion hst _),
  exact_mod_cast K.inter_subset_convex_hull hs ht ⟨hxs.1, hxt.1⟩,
end

lemma disjoint_interiors_aux (hs : s ∈ K) (ht : t ∈ K) (h : s ≠ t) :
  disjoint (combi_interior 𝕜 s) (combi_interior 𝕜 t) :=
set.disjoint_left.2 $ λ x hxs hxt, h $ disjoint_interiors hs ht hxs hxt

lemma eq_singleton_of_singleton_mem_combi_interior (hx : {x} ∈ K) (hs : s ∈ K)
  (hxs : x ∈ combi_interior 𝕜 s) : s = {x} :=
begin
  apply disjoint_interiors hs hx hxs,
  rw combi_interior_singleton,
  exact set.mem_singleton x,
end

lemma combi_interiors_cover : (⋃ s ∈ K, combi_interior 𝕜 s) = K.space :=
begin
  unfold space,
  refine (set.Union₂_mono $ λ _ _, _).antisymm (set.Union₂_subset $ λ s hs, _),
  { exact combi_interior_subset_convex_hull },
  rw simplex_combi_interiors_cover,
  refine set.Union₂_mono' (λ t hts, _),
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { refine ⟨s, hs, _⟩,
    rw combi_interior_empty,
    exact set.empty_subset _ },
  { exact ⟨t, K.down_closed' hs hts ht, set.subset.rfl⟩ }
end

/-- The simplices interiors form a partition of the underlying space (except that they contain the
empty set) -/
lemma combi_interiors_partition (hx : x ∈ K.space) : ∃! s, s ∈ K ∧ x ∈ combi_interior 𝕜 s :=
begin
  rw ←combi_interiors_cover at hx,
  obtain ⟨s, hs, hxs⟩ := set.mem_Union₂.1 hx,
  exact ⟨s, ⟨⟨hs, hxs⟩, λ t ⟨ht, hxt⟩, disjoint_interiors ht hs hxt hxs⟩⟩,
end

lemma mem_convex_hull_iff : x ∈ convex_hull 𝕜 (s : set E) ↔ ∃ t ⊆ s, x ∈ combi_interior 𝕜 t :=
begin
  simp [simplex_combi_interiors_cover],
end

lemma mem_combi_frontier_iff' : x ∈ combi_frontier 𝕜 s ↔ ∃ {t}, t ⊂ s ∧ x ∈ combi_interior 𝕜 t :=
begin
  rw mem_combi_frontier_iff,
  split,
  { rintro ⟨t, hts, hxt⟩,
    --rw [simplex_combi_interiors_cover, mem_Union₂] at hxt,
    --obtain ⟨u, hu⟩ := simplex_combi_interiors_cover
    sorry
  },
  { rintro ⟨t, hts, hxt⟩,
    exact ⟨t, hts, hxt.1⟩ }
end

lemma subset_of_combi_interior_inter_convex_hull_nonempty (hs : s ∈ K) (ht : t ∈ K)
  (hst : (combi_interior 𝕜 s ∩ convex_hull 𝕜 (t : set E)).nonempty) :
  s ⊆ t :=
begin
  obtain ⟨x, hxs, hxt⟩ := hst,
  obtain ⟨u, hut, hxu⟩ := mem_convex_hull_iff.1 hxt,
  rw disjoint_interiors hs (K.down_closed' ht hut $ nonempty_of_ne_empty _) hxs hxu,
  exact hut,
  { rintro rfl,
    rwa combi_interior_empty at hxu }
end

noncomputable def dim (K : simplicial_complex 𝕜 E) : ℕ := sorry

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

variables {𝕜 E}

lemma cells_subset_facets [finite_dimensional 𝕜 E] : K.cells ⊆ K.facets :=
begin
  rintro s ⟨hs, hscard⟩,
  by_contra,
  obtain ⟨t, ht, hst⟩ := (not_facet_iff_subface hs).mp h,
  have := card_lt_card hst,
  have := face_dimension_le_space_dimension ht,
  linarith,
end

lemma simplex_combi_interiors_split_interiors (ht : affine_independent 𝕜 (coe : (t : set E) → E))
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) :
  ∃ u ⊆ t, combi_interior 𝕜 s ⊆ combi_interior 𝕜 u :=
begin
  let K := simplicial_complex.of_simplex ht,
  let F := t.powerset.filter (λ v : finset E, (s : set E) ⊆ convex_hull 𝕜 ↑v),
  sorry
  /-obtain ⟨u, hu, humin⟩ := inf' _
  (begin
    use t,
    simp only [true_and, mem_powerset_self, mem_filter],
    exact subset.trans (subset_convex_hull 𝕜 _) hst,
  end : F.nonempty)
  begin
    rintro A B hA hB,
    simp at ⊢ hA hB,
    exact ⟨subset.trans (inter_subset_left _ _) hA.1,
      subset.trans (subset_inter hA.2 hB.2) (K.disjoint ((mem_simplex_complex_iff ht).2 hA.1)
      ((mem_simplex_complex_iff ht).2 hB.1))⟩
  end,
  simp at hu,
  use [u, hu.1],
  rintro x hxs,
  use convex_hull_min hu.2 (convex_convex_hull 𝕜 _) hxs.1,
  rintro hxu,
  rw mem_combi_frontier_iff' at hxu,
  obtain ⟨v, hvu, hxv⟩ := hxu,
  apply hvu.2 (humin v _),
  simp,
  use [subset.trans hvu.1 hu.1],
  rw convex_hull_eq _ at ⊢ hu,
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxv,
  let u : E → E → 𝕜 := λ a, if ha : a ∈ s then classical.some (hu.2 ha) else (λ b, 0),
  have hupos : ∀ {a}, a ∈ s → ∀ (b : E), b ∈ u → 0 < u a b,
  { rintro a ha,
    have := classical.some_spec (hu.2 ha),
    sorry
  },
  have husum : ∀ {a}, a ∈ s → ∑ (b : E) in u, u a b = 1,
  { sorry
  },
  have hucenter : ∀ {a}, a ∈ s → u.center_mass (u a) id = a,
  { sorry
  },
  let t : E → 𝕜 := λ b, if hb : b ∈ u then ∑ (a : E) in s, v a * u a b else 0,-/
  /-rintro y (hys : y ∈ s),
  obtain ⟨v, hvpos, hvsum, hvcenter⟩ := combi_interior_subset_positive_weighings hxs,
  obtain ⟨w, hwpos, hwsum, hwcenter⟩ := combi_interior_subset_positive_weighings hxv,-/
  --rw mem_convex_hull,
  /-by_contra hsv,
  obtain ⟨y, hys, hyv⟩ := not_subset.1 hsv,-/
  /-apply hxs.2,
  rw mem_combi_frontier_iff at ⊢,
  use [s.filter (λ w : E, w ∈ convex_hull 𝕜 (v : set E)), filter_subset _ _],
  { rintro hsv,
    apply hvu.2 (humin v _),
    simp,
    use [subset.trans hvu.1 hu.1],
    rintro y (hys : y ∈ s),
    have := hsv hys,
    simp at this,
    exact this.2 },
  { simp,
    apply convex_hull_mono (subset_inter (subset.refl _) _) hxs.1,
    by_contra hsv,
    rw not_subset at hsv,
    /-suffices hsv : ↑s ⊆ convex_hull 𝕜 ↑v,
    { apply convex_hull_mono (subset_inter (subset.refl _) hsv) hxs.1,
    },-/
    sorry
  }-/
end

lemma simplex_combi_interiors_split_interiors_nonempty (hs : s.nonempty)
  (ht : affine_independent 𝕜 (coe : (t : set E) → E))
  (hst : convex_hull 𝕜 (s : set E) ⊆ convex_hull 𝕜 ↑t) :
  ∃ u ⊆ t, u.nonempty ∧ combi_interior 𝕜 s ⊆ combi_interior 𝕜 u :=
begin
  sorry
end

end linear_ordered_field
end geometry.simplicial_complex
