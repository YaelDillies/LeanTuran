import analysis.normed.group.basic

variables {E : Type*} [seminormed_group E]

@[to_additive norm_nsmul_le'] lemma norm_pow_le_mul_norm' (n : ℕ) (a : E) : ‖a^n‖ ≤ n * ‖a‖ :=
begin
  induction n with n ih, { simp, },
  simpa only [pow_succ', nat.cast_succ, add_mul, one_mul] using norm_mul_le_of_le ih le_rfl,
end

@[to_additive nnnorm_nsmul_le'] lemma nnnorm_pow_le_mul_norm' (n : ℕ) (a : E) : ‖a^n‖₊ ≤ n * ‖a‖₊ :=
by simpa only [← nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_nat_cast]
  using norm_pow_le_mul_norm' n a
