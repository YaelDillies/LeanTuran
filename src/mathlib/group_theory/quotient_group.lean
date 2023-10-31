import group_theory.quotient_group

open set
open_locale pointwise

variables {α : Type*}

namespace subgroup
section group
variables [group α] {H : subgroup α} [subgroup.normal H] {s t : set α}

@[to_additive]
lemma image_coe_quotient (H : subgroup α) [H.normal] : (coe : α → α ⧸ H) '' H = 1 :=
begin
  ext a,
  dsimp,
  split,
  { rintro ⟨a, ha, rfl⟩,
    rwa [quotient_group.eq_one_iff] },
  { rintro rfl,
    exact ⟨1, H.one_mem, rfl⟩ }
end

@[to_additive] lemma preimage_image_coe (s : set α) : (coe : α → α ⧸ H) ⁻¹' (coe '' s) = H * s :=
begin
  ext a,
  split,
  { rintro ⟨b, hb, h⟩,
    refine ⟨a / b, b, (quotient_group.eq_one_iff _).1 _, hb, div_mul_cancel' _ _⟩,
    simp only [h, quotient_group.coe_div, div_self'] },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    refine ⟨b, hb, _⟩,
    simpa only [quotient_group.coe_mul, self_eq_mul_left, quotient_group.eq_one_iff] }
end

@[to_additive]
lemma image_coe_inj : (coe : α → α ⧸ H) '' s = (coe : α → α ⧸ H) '' t ↔ ↑H * s = H * t :=
by { simp_rw ←preimage_image_coe,
  exact quotient_group.mk_surjective.preimage_injective.eq_iff.symm }

end group

section comm_group
variables [comm_group α] {s : subgroup α} {a : α}

@[to_additive]
lemma mul_alt_version (N : subgroup α) (s : set α) :
  coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, x • s :=
by { simp_rw [quotient_group.preimage_image_coe N s, mul_comm _ (coe _), ← set.Union_inv_smul,
    ←set.preimage_smul _ s], congr }

end comm_group
end subgroup
