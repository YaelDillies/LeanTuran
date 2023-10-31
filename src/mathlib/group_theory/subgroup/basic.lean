import group_theory.subgroup.basic

--TODO: Fix implicitness `subgroup.closure_eq_bot_iff`

namespace subgroup
variables {G : Type*} [group G]

attribute [norm_cast] coe_eq_univ add_subgroup.coe_eq_univ

@[simp, to_additive] lemma coe_sort_coe (s : subgroup G) : ↥(s : set G) = ↥s := rfl

end subgroup
