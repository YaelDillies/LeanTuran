/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import algebra.char_p.basic
import data.finset.pointwise
import group_theory.subgroup.basic
import mathlib.set_theory.cardinal.finite

/-!
# For mathlib

A lot of stuff to move
-/

open_locale pointwise

namespace nat
variables {α β : Type*} [group α] [mul_action α β]

open cardinal

@[simp, to_additive] lemma card_smul_set (a : α) (s : set β) : nat.card ↥(a • s) = nat.card s :=
begin
  obtain hs | hs := s.infinite_or_finite,
  { rw [hs.card_eq_zero, hs.smul_set.card_eq_zero] },
  classical,
  lift s to finset β using hs,
  simp [←finset.coe_smul_finset],
end

end nat

namespace subgroup
variables {α : Type*} [group α] {s : subgroup α} {a : α}

@[norm_cast, to_additive] lemma coe_eq_one : (s : set α) = 1 ↔ s = ⊥ :=
(set_like.ext'_iff.trans (by refl)).symm

@[to_additive] lemma smul_coe (ha : a ∈ s) : a • (s : set α) = s :=
by { ext, rw set.mem_smul_set_iff_inv_smul_mem, exact subgroup.mul_mem_cancel_left _ (inv_mem ha) }

end subgroup

namespace subgroup
variables {α β : Type*} [group α] [group β] [mul_action α β] [is_scalar_tower α β β]

open set

@[to_additive] lemma pairwise_disjoint_smul (s : subgroup β) :
  (set.range $ λ a : α, a • (s : set β)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab,
  dsimp at ⊢ hab,
  rw disjoint_left,
  rintro _ ⟨c, hc, rfl⟩ ⟨d, hd, hcd⟩,
  refine hab _,
  rw [←smul_coe hc, ←smul_assoc, ←hcd, smul_assoc, smul_coe hc, smul_coe hd],
end

end subgroup

namespace char_p
variables {R : Type*} [add_group_with_one R] (p : ℕ) [char_p R p] {a b n : ℕ}

-- lemma add_order_of_cast (hn : n ≠ 0) : add_order_of (n : R) = p / p.gcd n := sorry

end char_p
