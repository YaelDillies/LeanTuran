import algebra.indicator_function

open_locale big_operators

namespace finset
variables {α ι M : Type*} [comm_monoid M] [decidable_eq ι]

@[to_additive] lemma prod_inter_eq_prod_mul_indicator (s t : finset ι) (f : ι → M) :
  ∏ i in s ∩ t, f i = ∏ i in s, (t : set ι).mul_indicator f i :=
by simp [prod_mul_indicator_eq_prod_filter, filter_mem_eq_inter]

end finset
