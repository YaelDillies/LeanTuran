/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import simplicial_complex.link
import simplicial_complex.subdivision

/-!
# Boundary of a simplicial complex
-/

open finset geometry

variables {𝕜 E : Type*}

namespace geometry.simplicial_complex
section ordered_ring
variables [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {K : simplicial_complex 𝕜 E}
  {s t : finset E} {A : set (finset E)} {n : ℕ}

def on_boundary (K : simplicial_complex 𝕜 E) (s : finset E) : Prop :=
s.nonempty ∧ ∃ t ∈ K.faces, s ⊂ t ∧ ∀ ⦃u⦄, u ∈ K.faces → s ⊂ u → t = u

def boundary (K : simplicial_complex 𝕜 E) : simplicial_complex 𝕜 E :=
K.of_subcomplex'
  {s | s.nonempty ∧ ∃ t ∈ K.faces, s ⊆ t ∧ K.on_boundary t}
  (λ s ⟨hs, t, ht, hst, _⟩, K.down_closed' ht hst hs)
  (λ s u ⟨hs, t, ht, hst, v⟩ hus hu, ⟨hu, t, ht, hus.trans hst, v⟩)

lemma boundary_le : K.boundary ≤ K := K.of_subcomplex_le _

lemma boundary_bot : (⊥ : simplicial_complex 𝕜 E).boundary = ⊥ := of_subcomplex_bot _

lemma mem_boundary_iff_subset_unique_facet :
  s ∈ K.boundary.faces ↔ s.nonempty ∧ ∃ (t ∈ K) (u ∈ K.facets), s ⊆ t ∧ t ⊂ u ∧
    ∀ ⦃v⦄, v ∈ K.faces → t ⊂ v → u = v :=
begin
  split,
  { rintro ⟨hs, t, ht, hst, ht', u, hu, htu, huunique⟩,
    exact ⟨hs, t, ht, u, ⟨hu, λ v hv huv, huunique hv ⟨htu.1.trans huv, λ hvt, htu.2 $
      huv.trans hvt⟩⟩, hst, htu, huunique⟩ },
  { rintro ⟨hs, t, ht, u, hu, hst, htu, huunique⟩,
    exact ⟨hs, t, ht, hst, K.nonempty ht, u, hu.1, htu, huunique⟩ }
end

lemma facets_disjoint_boundary : disjoint K.facets K.boundary.faces :=
begin
  rw set.disjoint_left,
  rintro s ⟨hs, hsunique⟩ ⟨hs, t, ht, hst, ht, u, hu, htu, huunique⟩,
  apply htu.2,
  rw ←hsunique hu (hst.trans  htu.1),
  exact hst,
end

lemma boundary_facet_iff : s ∈ K.boundary.facets ↔ K.on_boundary s :=
begin
  split,
  { rintro ⟨⟨hs, t, ht, hst, ht', u, hu, htu, huunique⟩, hsmax⟩,
    refine ⟨hs, u, hu, finset.ssubset_of_subset_of_ssubset hst htu, _⟩,
    rwa hsmax ⟨ht', _, ht, subset.rfl, ht', _, hu, htu, huunique⟩ hst },
  rintro ⟨hs, t, ht, hst, htunique⟩,
  refine ⟨⟨hs, s, K.down_closed' ht hst.1 hs, subset.rfl, hs, _, ht, hst, htunique⟩, _⟩,
  rintro V ⟨hV, W, hW, hVW, hW', u, hu, hWu, huunique⟩ hsV,
  apply hsV.antisymm,
  classical,
  by_contra hVs,
  have := htunique (K.down_closed' hW hVW hV) ⟨hsV, hVs⟩,
  subst this,
  have := htunique hu ⟨hsV.trans $ hVW.trans hWu.1, λ hus, hWu.2 $ hus.trans $ hsV.trans hVW⟩,
  subst this,
  exact hWu.2 hVW,
end

lemma boundary_facet_iff' :
  s ∈ K.boundary.facets ↔ s.nonempty ∧
    ∃ t ∈ K.facets, s ⊂ t ∧ ∀ ⦃t'⦄, t' ∈ K.faces → s ⊂ t' → t = t' :=
begin
  rw boundary_facet_iff,
  split,
  { rintro ⟨hs, t, ht, hst, htunique⟩,
    refine ⟨hs, t, _, hst, htunique⟩,
    exact ⟨ht, λ t' ht' htt', htunique ht' $ hst.trans_subset htt'⟩ },
  { rintro ⟨hs, t, ht, hst, htunique⟩,
    exact ⟨hs, t, ht.1, hst, htunique⟩ }
end

protected lemma pure.boundary (hK : K.pure n) : K.boundary.pure (n - 1) :=
begin
  refine ⟨λ s hs, _, λ s hs, _⟩,
  sorry,
  obtain ⟨hs', t, ht, hst, htunique⟩ := boundary_facet_iff'.1 hs,
  cases n,
  { exact ((card_le_of_subset hst.1).trans_eq $ hK.2 ht).antisymm (card_pos.2 hs') },
  have htcard : t.card = n + 2 := hK.2 ht,
  have hscard : s.card ≤ n + 1,
  { have := finset.card_lt_card hst,
    rw htcard at this,
    exact nat.le_of_lt_succ this },
  have : n + 1 - s.card + s.card ≤ t.card,
  { rw [hK.2 ht, nat.sub_add_cancel hscard, nat.succ_eq_add_one],
    linarith },
  obtain ⟨W, hsW, hWt, hWcard⟩ := finset.exists_intermediate_set (n + 1 - s.card) this hst.1,
  rw nat.sub_add_cancel hscard at hWcard,
  have hW : W ∈ K.boundary.faces,
  { have htW : ¬t ⊆ W,
    { have hWtcard : W.card < t.card,
      { rw [hWcard, hK.2 ht, nat.succ_eq_add_one],
        linarith },rintro htW,
      have : n + 2 = n + 1 := by rw [← hK.2 ht, ← hWcard, eq_of_subset_of_card_le htW hWtcard.le],
      exact nat.succ_ne_self (n + 1) this },
    have hW' : W.nonempty := sorry,
    refine ⟨hW', W, K.down_closed' (facets_subset ht) hWt hW', subset.rfl, hW', t, ht.1, ⟨hWt, htW⟩,
      λ u hu hWu, _⟩,
    exact htunique hu ⟨hsW.trans hWu.1, λ hus, hWu.2 $ hus.trans hsW⟩ },
  rw [nat.succ_sub_one, ←hWcard, hs.2 hW hsW],
end

lemma link_boundary : K.boundary.link A = (K.link A).boundary :=
begin
  ext V,
  sorry
  -- split,
  -- { rintro ⟨hVdisj, W, s, hW, ⟨t, u, ht, hu, hst, htu, huunique⟩, hVs, hWs⟩,
  --   refine ⟨V, _, _⟩,
  --   { sorry
  --     /-split,
  --     exact (λ U hU, hVdisj hU),
  --     exact ⟨W, u, hW, facets_subset hu, subset.trans hVs (subset.trans hst htu.1),
  --       hWs.trans (subset.trans hst htu.1)⟩,-/
  --   },
  --   { /-refine ⟨subset.rfl, u, _, _⟩,
  --     { sorry --waiting for link_facet_iff. May make this lemma require more assumptions
  --     },
  --     use ⟨finset.subset.trans hVs (finset.subset.trans hst htu.1),
  --       (λ huV, htu.2 (finset.subset.trans huV (finset.subset.trans hVs hst)))⟩,
  --     rintro U ⟨hUdisj, T, R, hT, hR, hUR, hTR⟩ hVU,
  --     apply huunique (K.down_closed hR hUR),-/
  --     sorry }
  -- },
  -- { sorry }
end

end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {K : simplicial_complex 𝕜 E}
  {s t : finset E} {A : set (finset E)} {n : ℕ}

lemma boundary_boundary [finite_dimensional 𝕜 E] (hK : K.pure n) (hK' : ∀ ⦃s⦄, s ∈ K.faces →
  (s : finset E).card = n - 1 → {t | t ∈ K.faces ∧ s ⊆ t} ≃ (fin 2)) :
  K.boundary.boundary = ⊥ :=
begin
  refine facets_eq_empty_iff.1 (set.eq_empty_of_forall_not_mem $ λ V hV, _),
  obtain ⟨hV, W, hW, hVW, hWunique⟩ := boundary_facet_iff'.1 hV,
  obtain ⟨hW', s, hs, hsV, hsunique⟩ := boundary_facet_iff'.1 hW,
  sorry
end

/-- A m-simplex is on the boundary of a full dimensional complex iff it belongs to exactly one cell.
-/ -- Dull?
lemma boundary_subcell_iff_one_surface (hK : K.full_dimensional)
  (hscard : s.card = finite_dimensional.finrank 𝕜 E) :
  s ∈ K.boundary.faces ↔ nat.card {t | t ∈ K.faces ∧ s ⊂ t} = 1 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at s)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  split,
  { rintro ⟨hs, t, ht, hst, u, hu, htu, huunique⟩,
    have : s = t,
    {   sorry
    },
    sorry--rw nat.card_eq_fintype_card,
  },
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ s → b ∉ s → s ∪ {a} ∈ K.faces → s ∪ {b} ∈ K.faces →
  --   ∃ w : E → 𝕜, w a < 0 ∧ ∑ y in s ∪ {a}, w y = 1 ∧ (s ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

/-- A m-simplex is not on the boundary of a full dimensional complex iff it belongs to exactly two
cells. -/
lemma not_boundary_subcell_iff_two_surfaces (hK : K.full_dimensional)
  (hscard : s.card = finite_dimensional.finrank 𝕜 E) :
  s ∉ K.boundary.faces ↔ nat.card {t | t ∈ K.faces ∧ s ⊂ t} = 2 :=
  -- It's probably a bad idea to use `nat.card` since it's incredibly underdeveloped for doing
  -- actual maths in
  -- Does this lemma need you to assume locally finite (at s)? If so, the set you care about is a
  -- subset of the set we know is finite, so we can convert to a finset and use normal card
begin
  -- have aux_lemma : ∀ {a b : E}, a ≠ b → a ∉ s → b ∉ s → s ∪ {a} ∈ K.faces → s ∪ {b} ∈ K.faces →
  --   ∃ w : E → 𝕜, w a < 0 ∧ ∑ y in s ∪ {a}, w y = 1 ∧ (s ∪ {a}).center_mass w id = b,
  -- {
  --   sorry
  -- },
  sorry
end

end linear_ordered_field
end geometry.simplicial_complex
