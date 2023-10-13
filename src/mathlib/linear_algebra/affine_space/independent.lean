import linear_algebra.affine_space.independent

open_locale big_operators
open finset

variables {𝕜 E ι : Type*} [ring 𝕜] [add_comm_group E] [module 𝕜 E] {p : ι → E} {w w₁ w₂ : ι → 𝕜}
  {s : finset ι} {m n : ℕ}

lemma affine_independent.eq_zero_of_sum_eq_zero (hp : affine_independent 𝕜 p)
  (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w i • p i = 0) : ∀ i ∈ s, w i = 0 :=
affine_independent_iff.1 hp _ _ hw₀ hw₁

lemma affine_independent.eq_of_sum_eq_sum (hp : affine_independent 𝕜 p)
  (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i) (hwp : ∑ i in s, w₁ i • p i = ∑ i in s, w₂ i • p i) :
  ∀ i ∈ s, w₁ i = w₂ i :=
begin
  refine λ i hi, sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero _ _ _ hi),
  all_goals { simpa [sub_mul, sub_smul, sub_eq_zero] },
end

lemma affine_independent.eq_zero_of_sum_eq_zero_subtype {s : finset E}
  (hp : affine_independent 𝕜 (coe : s → E)) {w : E → 𝕜}
  (hw₀ : ∑ x in s, w x = 0) (hw₁ : ∑ x in s, w x • x = 0) :
  ∀ x ∈ s, w x = 0 :=
begin
  rw [←sum_attach] at hw₀ hw₁,
  exact λ x hx, hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _),
end

lemma affine_independent.eq_of_sum_eq_sum_subtype {s : finset E}
  (hp : affine_independent 𝕜 (coe : s → E)) {w₁ w₂ : E → 𝕜}
  (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i) (hwp : ∑ i in s, w₁ i • i = ∑ i in s, w₂ i • i) :
  ∀ i ∈ s, w₁ i = w₂ i :=
begin
  refine λ i hi, sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype _ _ _ hi),
  all_goals { simpa [sub_mul, sub_smul, sub_eq_zero] },
end
