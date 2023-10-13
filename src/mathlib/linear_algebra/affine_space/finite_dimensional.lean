import linear_algebra.affine_space.finite_dimensional

open_locale big_operators
open finset

variables {𝕜 E ι : Type*} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]
  [finite_dimensional 𝕜 E] [fintype ι] {p : ι → E}

lemma affine_independent.card_le_finrank_succ (hp : affine_independent 𝕜 p) :
  fintype.card ι ≤ finite_dimensional.finrank 𝕜 (vector_span 𝕜 (set.range p)) + 1 :=
begin
  casesI is_empty_or_nonempty ι,
  { simp [fintype.card_eq_zero] },
  rw ←tsub_le_iff_right,
  exact (affine_independent_iff_le_finrank_vector_span _ _ (tsub_add_cancel_of_le $
    nat.one_le_iff_ne_zero.2 fintype.card_ne_zero).symm).1 hp,
end
