import data.nat.lattice

namespace nat
variables {ι : Sort*}

@[simp] lemma infi_empty [is_empty ι] (f : ι → ℕ) : (⨅ i : ι, f i) = 0 :=
by rw [infi, set.range_eq_empty, Inf_empty]

@[simp] lemma infi_const_zero : (⨅ i : ι, 0) = 0 :=
begin
  casesI is_empty_or_nonempty ι,
  { exact infi_empty _ },
  { exact cinfi_const }
end

end nat
