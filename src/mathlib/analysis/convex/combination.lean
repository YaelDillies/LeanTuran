import analysis.convex.combination
import linear_algebra.affine_space.finite_dimensional
import mathlib.linear_algebra.affine_space.independent

open finset
open_locale big_operators

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {m n : ℕ}

lemma affine_independent.subset_convex_hull_inter {X : finset E}
  (hX : affine_independent 𝕜 (coe : (X : set E) → E)) {Y₁ Y₂ : finset E}
  (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull 𝕜 (Y₁ : set E) ∩ convex_hull 𝕜 (Y₂ : set E) ⊆ convex_hull 𝕜 (Y₁ ∩ Y₂ : set E) :=
begin
  classical,
  rintro x ⟨hx₁, hx₂⟩,
  rw ←coe_inter,
  rw finset.convex_hull_eq at hx₁ hx₂,
  rcases hx₁ with ⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩,
  rcases hx₂ with ⟨w₂, h₁w₂, h₂w₂, h₃w₂⟩,
  rw center_mass_eq_of_sum_1 _ _ h₂w₁ at h₃w₁,
  rw center_mass_eq_of_sum_1 _ _ h₂w₂ at h₃w₂,
  dsimp at h₃w₁ h₃w₂,
  let w : E → 𝕜,
  { intro x,
    apply (if x ∈ Y₁ then w₁ x else 0) - (if x ∈ Y₂ then w₂ x else 0) },
  have h₁w : ∑ i in X, w i = 0,
  { rw [finset.sum_sub_distrib, ←sum_filter, filter_mem_eq_inter, ←sum_filter,
      filter_mem_eq_inter, (finset.inter_eq_right_iff_subset _ _).2 hY₁,
      (finset.inter_eq_right_iff_subset _ _).2 hY₂, h₂w₁, h₂w₂],
    simp only [sub_self] },
  have : ∑ (i : E) in X, w i • i = 0,
  { simp only [sub_smul, zero_smul, ite_smul, finset.sum_sub_distrib, ←finset.sum_filter, h₃w₁,
      finset.filter_mem_eq_inter, (finset.inter_eq_right_iff_subset _ _).2 hY₁,
      (finset.inter_eq_right_iff_subset _ _).2 hY₂, h₃w₂, sub_self] },
  have hX' := hX.eq_zero_of_sum_eq_zero_subtype h₁w this,
  have t₁ : ∀ x, x ∈ Y₁ → x ∉ Y₂ → w₁ x = 0,
  { intros x hx₁ hx₂,
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX' _ (hY₁ hx₁),
    simpa [hx₁, hx₂] using this },
  have h₄w₁ : ∑ (y : E) in Y₁ ∩ Y₂, w₁ y = 1,
  { rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₂w₁],
    simp_intros x hx₁ hx₂,
    exact t₁ x hx₁ (hx₂ hx₁)},
  rw finset.convex_hull_eq,
  refine ⟨w₁, _, h₄w₁, _⟩,
  { simp only [and_imp, finset.mem_inter],
    intros y hy₁ hy₂,
    exact h₁w₁ y hy₁},
  { rw finset.center_mass_eq_of_sum_1 _ _ h₄w₁,
    dsimp only [id.def],
    rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₃w₁],
    simp_intros x hx₁ hx₂,
    exact or.inl (t₁ x hx₁ $ hx₂ hx₁) }
end

/-- If an affine independent finset is contained in the convex hull of another finset, then it is
smaller than that finset. -/
lemma affine_independent.card_le_card_of_subset_convex_hull {X Y : finset E}
  (hX : affine_independent 𝕜 (coe : X → E)) (hXY : (X : set E) ⊆ convex_hull 𝕜 ↑Y) :
  X.card ≤ Y.card :=
begin
  obtain rfl | h₁ := X.eq_empty_or_nonempty,
  { simp },
  obtain rfl | h₂ := Y.eq_empty_or_nonempty,
  { simp only [finset.coe_empty, convex_hull_empty, set.subset_empty_iff, finset.coe_eq_empty]
      at hXY,
    subst hXY },
  have X_card_pos : 1 ≤ X.card := h₁.card_pos,
  have X_eq_succ : fintype.card (X : set E) = (X.card - 1) + 1,
  { simp [nat.sub_add_cancel ‹1 ≤ X.card›] },
  have Y_card_pos : 1 ≤ Y.card := h₂.card_pos,
  have Y_eq_succ : fintype.card (Y : set E) = (Y.card - 1) + 1,
  { simp [nat.sub_add_cancel ‹1 ≤ Y.card›] },
  have direction_le := affine_subspace.direction_le (affine_span_mono 𝕜 hXY),
  rw [affine_span_convex_hull] at direction_le,
  letI : finite_dimensional 𝕜 (vector_span 𝕜 (Y : set E)) :=
    finite_dimensional_vector_span_of_finite _ Y.finite_to_set,
  rw [direction_affine_span, direction_affine_span] at direction_le,
  have finrank_le := submodule.finrank_le_finrank_of_le direction_le,
  rw [←@subtype.range_coe _ (X : set E), ←@subtype.range_coe _ (Y : set E),
    hX.finrank_vector_span X_eq_succ] at finrank_le,
  have := le_trans finrank_le (finrank_vector_span_range_le 𝕜 (coe : Y → E) Y_eq_succ),
  rwa tsub_le_tsub_iff_right at this,
  exact Y_card_pos,
end
