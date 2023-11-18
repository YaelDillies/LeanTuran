import algebra.group.opposite
import group_theory.group_action.defs
import order.rel_iso.group

namespace rel_iso
variables {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ≃r r` on `α`. -/
instance apply_mul_action : mul_action (r ≃r r) α :=
{ smul := coe_fn,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

/-- The tautological action by `r ≃r r` on `α`. -/
instance apply_op_mul_action : mul_action (r ≃r r)ᵐᵒᵖ α :=
{ smul := λ e, e.unop.symm,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl
@[simp] lemma op_smul_def (f : (r ≃r r)ᵐᵒᵖ) (a : α) : f • a = f.unop.symm a := rfl

instance apply_has_faithful_smul : has_faithful_smul (r ≃r r) α := ⟨rel_iso.ext⟩
instance apply_op_has_faithful_smul : has_faithful_smul (r ≃r r)ᵐᵒᵖ α := sorry

end rel_iso
