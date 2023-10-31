import order.conditionally_complete_lattice.basic

section
variables {ι : Sort*} {α : Type*} [conditionally_complete_linear_order_bot α] {f : ι → α} {a : α}

lemma cinfi_le_of_le' (c : ι) : f c ≤ a → infi f ≤ a := cinfi_le_of_le (order_bot.bdd_below _) _

end
