import measure_theory.measure.lebesgue.eq_haar
import mathlib.measure_theory.measure.measure_space
import mathlib.measure_theory.measure.open_pos

open topological_space set filter metric
open_locale ennreal pointwise topology nnreal

namespace measure_theory
namespace measure

/-! ### Normed groups -/

section seminormed_group
variables {G : Type*} [measurable_space G] [group G] [topological_space G] [t2_space G]
  [topological_group G] [borel_space G] [second_countable_topology G] [locally_compact_space G]
variables {H : Type*} [measurable_space H] [seminormed_group H] [opens_measurable_space H]

open metric

@[to_additive]
lemma _root_.measurable.exists_nhds_one_bounded (f : G →* H) (h : measurable f)
  (μ : measure G . volume_tac) [μ.is_haar_measure] :
  ∃ s, s ∈ 𝓝 (1 : G) ∧ bounded (f '' s) :=
begin
  obtain ⟨r, hr⟩ := exists_pos_preimage_ball f (1 : H) (ne_zero.ne μ),
  refine ⟨_, div_mem_nhds_one_of_haar_pos μ (f ⁻¹' ball 1 r) (h measurable_set_ball) hr, _⟩,
  rw image_div,
  exact (bounded_ball.mono $ image_preimage_subset _ _).div
    (bounded_ball.mono $ image_preimage_subset _ _),
end

end seminormed_group
end measure
end measure_theory
