import data.finset.pointwise

open mul_opposite
open_locale pointwise

variables {α : Type*}

namespace finset
section has_one
variables [has_one α] {s : finset α}

@[simp, norm_cast, to_additive] lemma coe_eq_one : (s : set α) = 1 ↔ s = 1 := coe_eq_singleton

end has_one

section has_mul
variables [decidable_eq α] [has_mul α]

@[simp, to_additive] lemma singleton_mul' (a : α) (s : finset α) : {a} * s = a • s :=
singleton_mul _

@[simp, to_additive] lemma mul_singleton' (s : finset α) (a : α) : s * {a} = op a • s :=
mul_singleton _

end has_mul
end finset
