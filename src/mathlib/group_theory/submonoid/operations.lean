import group_theory.submonoid.operations

namespace submonoid
variables {G α β : Type*} [monoid G] [has_smul G α] {S : submonoid G}

@[simp, to_additive] lemma mk_smul (g : G) (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end submonoid
