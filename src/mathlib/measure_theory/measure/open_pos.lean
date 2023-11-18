import measure_theory.measure.open_pos

open_locale topology ennreal measure_theory
open set function filter

namespace measure_theory
namespace measure
variables {X : Type*} [topological_space X] {m : measurable_space X}
  (μ : measure X) [is_open_pos_measure μ]

instance is_open_pos_measure.to_ae_ne_bot [nonempty X] : μ.ae.ne_bot :=
ae_ne_bot.2 $ λ h, is_open_univ.measure_ne_zero μ univ_nonempty $ by rw [h, coe_zero, pi.zero_apply]

end measure
end measure_theory
