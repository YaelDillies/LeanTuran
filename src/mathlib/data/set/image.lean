import data.set.image

open function

namespace set
variables {α β : Type*} {f : α → β} {s : set α}

lemma preimage_subset_of_subset_image {t : set β} (hf : injective f) (h : t ⊆ f '' s) :
  f ⁻¹' t ⊆ s :=
λ x hx, hf.mem_set_image.1 $ h hx

end set
