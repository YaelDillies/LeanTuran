import analysis.convex.basic

open_locale big_operators
open finset

variables {𝕜 E ι : Type*} [ordered_ring 𝕜] [add_comm_group E] [module 𝕜 E] {m n : ℕ}

-- TODO: golf `affine_subspace.convex`
example (s : affine_subspace 𝕜 E) : convex 𝕜 (s : set E) :=
λ x hx y hy a b ha hb hab,
  calc a • x + b • y = b • (y - x) + x : convex.combo_eq_smul_sub_add hab
                ... ∈ s : s.2 _ hy hx hx
