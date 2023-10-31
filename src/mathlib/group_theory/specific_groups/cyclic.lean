import group_theory.specific_groups.cyclic

instance {n : ℕ} : is_add_cyclic (zmod n) := ⟨⟨1, λ x, (zmod.int_cast_surjective x).imp $ by simp⟩⟩

instance {p : ℕ} [fact p.prime] : is_simple_add_group (zmod p) :=
add_comm_group.is_simple_iff_is_add_cyclic_and_prime_card.2
  ⟨by apply_instance, by simpa using fact.out p.prime⟩
