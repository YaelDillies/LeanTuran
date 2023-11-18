import group_theory.free_group

namespace free_group
variables {α : Type*} [decidable_eq α]

attribute [simp] to_word_inv

@[to_additive]
lemma to_word_mul_sublist (x y : free_group α) : (x * y).to_word <+ x.to_word ++ y.to_word :=
begin
  refine red.sublist _,
  have : x * y = free_group.mk (x.to_word ++ y.to_word),
  { rw [←free_group.mul_mk, free_group.mk_to_word, free_group.mk_to_word] },
  rw this,
  exact free_group.reduce.red,
end

end free_group
