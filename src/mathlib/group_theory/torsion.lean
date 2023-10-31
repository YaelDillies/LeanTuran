import group_theory.torsion

namespace monoid
variables {α : Type*} [monoid α]

@[simp, to_additive] lemma is_torsion_free_of_subsingleton [subsingleton α] : is_torsion_free α :=
λ a ha _, ha $ subsingleton.elim _ _

end monoid
