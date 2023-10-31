import data.set.pointwise.smul

open mul_opposite
open_locale pointwise

namespace set
variables {α : Type*} [has_mul α]

@[simp, to_additive] lemma singleton_mul' (a : α) (s : set α) : {a} * s = a • s := singleton_mul
@[simp, to_additive] lemma mul_singleton' (s : set α) (a : α) : s * {a} = op a • s := mul_singleton

end set
