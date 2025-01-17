/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import measure_theory.function.lp_space
import measure_theory.integral.average
import order.upper_lower.locally_finite
import mathlib.data.set.image

/-!
# Bergelson's intersectivity lemma

This file proves the Bergelson intersectivity lemma: In a finite measure space, a sequence of events
that have measure at least `r` has an infinite subset whose finite intersections all have positive
volume.

This is in some sense a finitary version of the second Borel-Cantelli lemma.

## References

[Bergelson, *Sets of recurrence of `ℤᵐ`-actions and properties of sets of differences in
`ℤᵐ`][bergelson1985]

https://github.com/leanprover-community/mathlib/pull/18732

@Article{         bergelson1985,
  author        = {Bergelson, Vitaly},
  title         = {Sets of Recurrence of Zm-Actions and Properties of Sets of
                  Differences in Zm},
  journal       = {Journal of the London Mathematical Society},
  volume        = {s2-31},
  number        = {2},
  pages         = {295-304},
  doi           = {https://doi.org/10.1112/jlms/s2-31.2.295},
  url           = {https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/jlms/s2-31.2.295},
  eprint        = {https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/jlms/s2-31.2.295},
  year          = {1985}
}

## TODO

Restate the theorem using the upper density of a set of naturals, once we have it. This will make
`strong_bergelson` be actually strong.

Use the ergodic theorem to deduce the refinement of the Poincaré recurrence theorem proved by
Bergelson.
-/

open filter function measure_theory set
open_locale big_operators ennreal nnreal

variables {ι α : Type*} [measurable_space α] {μ : measure α} [is_finite_measure μ] {r : ℝ≥0∞}

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume.

TODO: The infinity of `t` should be strengthened to `t` having positive natural density. -/
lemma strong_bergelson {s : ℕ → set α} (hs : ∀ n, measurable_set (s n)) (hr₀ : r ≠ 0)
  (hr : ∀ n, r ≤ μ (s n)) :
  ∃ t : set ℕ, t.infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.finite → 0 < μ (⋂ n ∈ u, s n) :=
begin
  -- We let `M f` be the set on which the norm of `f` exceeds its essential supremum, and `N` be the
  -- union of `M` of the finite products of the indicators of the `s n`.
  let M : (α → ℝ) → set α := λ f, {x | snorm_ess_sup f μ < ‖f x‖₊},
  let N : set α := ⋃ u : finset ℕ, M (set.indicator (⋂ n ∈ u, s n) 1),
  -- `N` is a null set since `M f` is a null set for each `f`.
  have hN₀ : μ N = 0 := measure_Union_null (λ u, meas_snorm_ess_sup_lt),
  -- The important thing about `N` is that if we remove `N` from our space, then finite unions of
  -- the `s n` are null iff they are empty.
  have hN₁ : ∀ u : finset ℕ, ((⋂ n ∈ u, s n) \ N).nonempty → 0 < μ (⋂ n ∈ u, s n),
  { simp_rw pos_iff_ne_zero,
    rintro u ⟨x, hx⟩ hu,
    refine hx.2 (mem_Union.2 ⟨u, (_ : _ < _)⟩),
    rw [indicator_of_mem hx.1, snorm_ess_sup_eq_zero_iff.2],
    simp,
    { rwa [indicator_ae_eq_zero, function.support_one, inter_univ] } },
  -- Define `f n` to be the average of the first `n + 1` indicators of the `s k`.
  let f : ℕ → α → ℝ≥0∞ := λ n, (↑(n + 1) : ℝ≥0∞)⁻¹ • ∑ k in finset.range (n + 1), (s k).indicator 1,
  -- We gather a few simple properties of `f`.
  have hfapply : ∀ n a, f n a = (↑(n + 1))⁻¹ * ∑ k in finset.range (n + 1), (s k).indicator 1 a,
  { simp only [f, pi.coe_nat, pi.smul_apply, pi.inv_apply, finset.sum_apply, eq_self_iff_true,
    forall_const, implies_true_iff, smul_eq_mul] },
  have hf₀ : 0 ≤ f,
  { exact zero_le _ },
  have hf : ∀ n, measurable (f n),
  { exact λ n, measurable.mul' (@measurable_const ℝ≥0∞ _ _ _ (↑(n + 1))⁻¹)
      (finset.measurable_sum' _ $ λ i _, measurable_one.indicator $ hs i) },
  have hf₁ : ∀ n, f n ≤ 1,
  { rintro n a,
    rw [hfapply, ←ennreal.div_eq_inv_mul],
    refine (ennreal.div_le_iff_le_mul (or.inl $ nat.cast_ne_zero.2 n.succ_ne_zero) $
      or.inr one_ne_zero).2 _,
    rw [mul_comm, ←nsmul_eq_mul, ←finset.card_range n.succ],
    exact finset.sum_le_card_nsmul _ _ _ (λ _ _, indicator_le (λ _ _, le_rfl) _) },
  -- By assumption, `f n` has integral at least `r`.
  have hf₂ : ∀ n, r ≤ ∫⁻ a, f n a ∂μ,
  { rintro n,
    simp_rw hfapply,
    rw [lintegral_const_mul, lintegral_finset_sum],
    simp only [lintegral_indicator_one (hs _)],
    rw ←ennreal.div_eq_inv_mul,
    refine (ennreal.le_div_iff_mul_le (or.inl $ nat.cast_ne_zero.2 n.succ_ne_zero) $ or.inl $
      ennreal.nat_ne_top _).2 _,
    refine le_trans _ (finset.card_nsmul_le_sum _ _ _ $ λ _ _, hr _),
    { simp [mul_comm] },
    { exact λ _ _, measurable_one.indicator (hs _) },
    { exact finset.measurable_sum _ (λ _ _, measurable_one.indicator $ hs _) } },
  have hμ : μ ≠ 0,
  { unfreezingI { rintro rfl },
    exact hr₀ (le_bot_iff.1 $ hr 0) },
  -- By the first moment method, there exists some `x ∉ N` such that `limsup f n x` is at least `r`.
  obtain ⟨x, hxN, hx⟩ := exists_not_mem_null_laverage_le hμ
    (ne_top_of_le_ne_top (measure_ne_top μ univ) _) hN₀,
  rw laverage_eq at hx,
  replace hx := (ennreal.div_le_div_right ((le_limsup_of_le ⟨μ univ, eventually_map.2 _⟩ $ λ b hb,
    _).trans $ limsup_lintegral_le hf (λ n, ae_of_all μ $ hf₁ n) $
    ne_of_eq_of_ne lintegral_one is_finite_measure.measure_univ_lt_top.ne) _).trans hx,
  -- This exactly means that the `s n` containing `x` have all their finite intersection non-null.
  refine ⟨{n | x ∈ s n}, λ hxs, _, λ u hux hu, _⟩,
  -- This next block proves that a set of strictly positive natural density is infinite, mixed with
  -- the fact that `{n | x ∈ s n}` has strictly positive natural density.
  -- TODO: Separate it out to a lemma once we have a natural density API.
  { refine ((ennreal.div_pos_iff.2 ⟨hr₀, (measure_lt_top _ _).ne⟩).trans_le hx).ne'
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      _ _ $
        λ n, _).limsup_eq,
    exact λ n, (↑(n + 1)) ⁻¹ * hxs.to_finset.card,
    simpa using ennreal.tendsto.mul_const (ennreal.tendsto_inv_nat_nhds_zero.comp $
      tendsto_add_at_top_nat 1) (or.inr $ ennreal.nat_ne_top _),
    exact (λ n, hf₀ n x),
    refine mul_le_mul_left' _ _,
    classical,
    simp_rw [finset.sum_apply, indicator_apply, pi.one_apply, finset.sum_boole],
    exact nat.cast_le.2 (finset.card_le_of_subset $ λ m hm, hxs.mem_to_finset.2
      (finset.mem_filter.1 hm).2) },
  { simp_rw ←hu.mem_to_finset,
    exact hN₁ _ ⟨x, mem_Inter₂.2 $ λ n hn, hux $ hu.mem_to_finset.1 hn, hxN⟩ },
  { refine eventually_of_forall (λ n, _),
    rw [←one_mul (μ univ), ←lintegral_const],
    exact lintegral_mono (hf₁ _) },
  { obtain ⟨n, hn⟩ := hb.exists,
    exact (hf₂ _).trans hn },
  { rw ←lintegral_one,
    refine lintegral_mono (λ a, limsup_le_of_le ⟨0, λ R hR, _⟩ $
      eventually_of_forall $ λ n, hf₁ _ _),
    obtain ⟨r', hr'⟩ := (eventually_map.1 hR).exists,
    exact (hf₀ _ _).trans hr' }
end

/-- **Bergelson Intersectivity Lemma**: In a finite measure space, a sequence of events that have
measure at least `r` has an infinite subset whose finite intersections all have positive volume. -/
lemma weak_bergelson [infinite ι] {s : ι → set α} (hs : ∀ i, measurable_set (s i)) (hr₀ : r ≠ 0)
  (hr : ∀ i, r ≤ μ (s i)) :
  ∃ t : set ι, t.infinite ∧ ∀ ⦃u⦄, u ⊆ t → u.finite → 0 < μ (⋂ i ∈ u, s i) :=
begin
  obtain ⟨t, ht, h⟩ := strong_bergelson (λ n, hs $ infinite.nat_embedding _ n) hr₀ (λ n, hr _),
  refine ⟨_, ht.image $ (infinite.nat_embedding _).injective.inj_on _, λ u hut hu,
    (h (preimage_subset_of_subset_image (infinite.nat_embedding _).injective hut) $ hu.preimage $
    (embedding.injective _).inj_on _).trans_le $ measure_mono $ subset_Inter₂ $ λ i hi, _⟩,
  obtain ⟨n, hn, rfl⟩ := hut hi,
  exact Inter₂_subset _ hi,
end
