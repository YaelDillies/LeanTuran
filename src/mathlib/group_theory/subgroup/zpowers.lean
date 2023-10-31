import group_theory.subgroup.zpowers

section group
variables {α : Type*} [group α] {s : subgroup α} {a : α} {m n : ℤ}

open function int set subgroup submonoid

@[to_additive] lemma range_zpow (a : α) : range (λ n : ℤ, a ^ n) = zpowers a := rfl

end group
