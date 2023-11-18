import order.zorn
import mathlib.order.chain

variable {α : Type*}

/-! ### Flags -/

namespace flag
variables [preorder α] {c : set α} {s : flag α} {a b : α}

lemma _root_.is_chain.exists_subset_flag (hc : is_chain (≤) c) : ∃ s : flag α, c ⊆ s :=
let ⟨s, hs, hcs⟩ := hc.exists_max_chain in ⟨hs.flag, hcs⟩

lemma exists_mem (a : α) : ∃ s : flag α, a ∈ s :=
let ⟨s, hs⟩ := set.subsingleton_singleton.is_chain.exists_subset_flag in ⟨s, hs rfl⟩

lemma exists_mem_mem (hab : a ≤ b) : ∃ s : flag α, a ∈ s ∧ b ∈ s :=
by simpa [set.insert_subset] using (is_chain_pair _ hab).exists_subset_flag

instance : nonempty (flag α) := ⟨max_chain_spec.flag⟩

end flag
