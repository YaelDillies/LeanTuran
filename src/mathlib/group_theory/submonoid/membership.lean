import group_theory.submonoid.membership

open set

namespace submonoid
variables {α : Type*} [monoid α]

@[to_additive] lemma range_pow (a : α) : range (λ n : ℕ, a ^ n) = powers a := rfl

end submonoid
