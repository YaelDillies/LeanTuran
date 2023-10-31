import set_theory.cardinal.basic

open function set order
open_locale big_operators cardinal classical

namespace cardinal
variables {α : Type*} {c : cardinal}

@[simp] lemma to_nat_eq_zero : to_nat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c :=
begin
  simp only [to_nat, zero_hom.coe_mk, dite_eq_right_iff, or_iff_not_imp_right, not_le],
  refine forall_congr (λ h, _),
  rw [←@nat.cast_eq_zero cardinal, ←classical.some_spec (to_nat._proof_1 _ h)],
end

lemma to_nat_ne_zero : to_nat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by simp [not_or_distrib]

@[simp] lemma to_nat_pos : 0 < to_nat c ↔ c ≠ 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans to_nat_ne_zero

lemma aleph_0_le_mk_iff : aleph_0 ≤ mk α ↔ infinite α := infinite_iff.symm
lemma mk_lt_aleph_0_iff : mk α < aleph_0 ↔ finite α := by simp [←not_le, aleph_0_le_mk_iff]

end cardinal
