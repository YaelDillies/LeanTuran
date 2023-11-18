import order.chain

open set

variables {α β : Type*}

lemma is_chain_singleton (r : α → α → Prop) (a : α) : is_chain r {a} := pairwise_singleton _ _

lemma is_chain_pair (r : α → α → Prop) {a b : α} (h : r a b) : is_chain r {a, b} :=
(is_chain_singleton _ _).insert $ λ _ hb _, or.inl $ (eq_of_mem_singleton hb).symm.rec_on ‹_›

lemma is_max_chain.image {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) {c : set α}
  (hc : is_max_chain r c) :
  is_max_chain s (f '' c) :=
⟨hc.is_chain.image _ _ _ $ λ _ _, f.map_rel_iff.2, λ t ht hf,
  (f.to_equiv.eq_preimage_iff_image_eq _ _).1 begin
    rw preimage_equiv_eq_image_symm,
    exact hc.2 (ht.image _ _ _ $ λ _ _, f.symm.map_rel_iff.2) ((f.to_equiv.subset_image' _ _).2 hf),
  end⟩

namespace flag
section has_le
variables [has_le α] {s t : flag α} {c : set α} {a : α}

/-- Reinterpret a maximal chain as a flag. -/
protected def _root_.is_max_chain.flag (hc : is_max_chain (≤) c) : flag α := ⟨c, hc.is_chain, hc.2⟩

@[simp, norm_cast] lemma _root_.is_max_chain.coe_flag (hc : is_max_chain (≤) c) : ↑hc.flag = c :=
rfl

end has_le

section preorder
variables [preorder α] [preorder β] {s : flag α} {a b : α}

lemma mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
⟨λ ha b, s.le_or_le ha, λ hb, of_not_not $ λ ha, set.ne_insert_of_not_mem _ ‹_› $ s.max_chain.2
  (s.chain_le.insert $ λ c hc _, hb hc) $ set.subset_insert _ _⟩

/-- Flags are preserved under order isomorphisms. -/
def map (e : α ≃o β) : flag α ≃ flag β :=
{ to_fun := λ s, (s.max_chain.image e).flag,
  inv_fun := λ s, (s.max_chain.image e.symm).flag,
  left_inv := λ s, ext $ e.symm_image_image s,
  right_inv := λ s, ext $ e.image_symm_image s }

@[simp, norm_cast] lemma coe_map (e : α ≃o β) (s : flag α) : ↑(map e s) = e '' s := rfl
@[simp] lemma symm_map (e : α ≃o β) : (map e).symm = map e.symm := rfl

end preorder

end flag
