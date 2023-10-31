/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import simplicial_complex.topology
import data.nat.parity

/-!
# Sperner's lemma
-/

section
variables {𝕜 ι : Type*} [ordered_semiring 𝕜] [fintype ι] [nonempty ι]

open function

@[simp] lemma std_simplex_nonempty : (std_simplex 𝕜 ι).nonempty :=
by classical; exact ⟨_, ite_eq_mem_std_simplex _ $ classical.arbitrary _⟩

end

namespace geometry

open set simplicial_complex
open_locale affine big_operators classical

variables {𝕜 : Type*} [linear_ordered_field 𝕜] {m n : ℕ}
local notation `E` := fin m → 𝕜
variables {S : simplicial_complex 𝕜 E} {f : E → fin m}

def is_sperner_coloring (S : simplicial_complex 𝕜 E) (f : E → fin m) : Prop :=
∀ (x : E) i, x ∈ S.vertices → x i = 0 → f x ≠ i

def panchromatic (f : (fin n → 𝕜) → fin m) (X : finset (fin n → 𝕜)) := X.image f = finset.univ

lemma panchromatic_iff (f : E → fin m) (X : finset E) : panchromatic f X ↔ (X.image f).card = m :=
begin
  rw panchromatic,
  refine ⟨λ h, _, λ h, finset.eq_of_subset_of_card_le (finset.image f X).subset_univ _⟩,
  { rw h,
    simp },
  { rw h,
    simp [h] }
end

lemma std_simplex_one : std_simplex 𝕜 (fin 1) = {1} :=
begin
  ext x,
  simp [std_simplex_eq_inter],
  split,
  { rintro ⟨-, hx⟩,
    ext i,
    obtain rfl : i = 0 := subsingleton.elim _ _,
    apply hx },
  { rintro rfl,
    refine ⟨λ _, _, rfl⟩,
    exact zero_le_one }
end

lemma strong_sperner_zero_aux {S : simplicial_complex 𝕜 (fin 1 → 𝕜)}
  (hS₁ : S.space = std_simplex 𝕜 (fin 1)) :
  S.faces = {{1}} :=
begin
  refine eq_singleton_iff_nonempty_unique_mem.2 ⟨_, _⟩,
  { simp only [faces_eq_coe, coe_nonempty, ←space_nonempty, hS₁, std_simplex_nonempty] },
  refine λ X hX, finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨S.nonempty hX, _⟩,
  have := simplicial_complex.subset_space hX,
  rw [hS₁, std_simplex_one] at this,
  rintro x hx,
  simpa using this hx,
end

theorem strong_sperner_zero {S : simplicial_complex 𝕜 (fin 1 → 𝕜)}
  (hS₁ : S.space = std_simplex 𝕜 (fin 1)) (hS₂ : S.finite) (f : (fin 1 → 𝕜) → fin 1) :
  odd ((S.faces_finset hS₂).filter (panchromatic f)).card :=
begin
  have : (S.faces_finset hS₂).filter (panchromatic f) = {{1}},
  { ext X,
    simp only [mem_faces_finset, finset.mem_singleton, finset.mem_filter,
      strong_sperner_zero_aux hS₁, mem_insert_iff, mem_singleton_iff],
    split,
    { rintro ⟨rfl | rfl, h⟩,
      refl },
    rintro rfl,
    refine ⟨rfl, _⟩,
    simp [panchromatic] },
  rw this,
  simp,
end

lemma affine_independent_proj {ι : Type*} {p : ι → fin (n+1) → 𝕜} (hp₁ : ∀ i, p i 0 = 0)
  (hp₂ : affine_independent 𝕜 p) : affine_independent 𝕜 (matrix.vec_tail ∘ p) :=
begin
  rw affine_independent_def,
  intros s w hw hs i hi,
  rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin n → 𝕜) at hs,
  rw finset.weighted_vsub_of_point_apply at hs,
  simp only [vsub_eq_sub, function.comp_app, sub_zero] at hs,
  have : s.weighted_vsub p w = (0:fin (n+1) → 𝕜),
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin (n+1) → 𝕜),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    ext j,
    simp only [pi.zero_apply],
    rw finset.sum_apply _ s (λ i, w i • p i),
    refine fin.cases _ _ j,
    { simp [hp₁] },
    intro j,
    dsimp,
    rw function.funext_iff at hs,
    specialize hs j,
    simp only [pi.zero_apply] at hs,
    rw finset.sum_apply _ s (λ i, w i • matrix.vec_tail (p i)) at hs,
    dsimp [matrix.vec_tail] at hs,
    apply hs },
  exact hp₂ s w hw this i hi,
end

lemma is_linear_map_matrix_vec_tail :
  is_linear_map 𝕜 (matrix.vec_tail : (fin n.succ → 𝕜) → (fin n → 𝕜)) :=
{ map_add := λ x y, rfl,
  map_smul := λ c x, rfl }

-- TODO: this generalises to affine subspaces
lemma convex_hull_affine {X : finset (fin m.succ → 𝕜)}
  (hX₂ : ∀ (x : fin (m + 1) → 𝕜), x ∈ X → x 0 = 0)
  {x : fin m.succ → 𝕜} (hx : x ∈ convex_hull 𝕜 (X : set (fin m.succ → 𝕜))) :
  x 0 = 0 :=
begin
  rw finset.convex_hull_eq at hx,
  rcases hx with ⟨w, hw₀, hw₁, rfl⟩,
  rw X.center_mass_eq_of_sum_1 _ hw₁,
  dsimp,
  rw finset.sum_apply 0 _ (λ i, w i • i),
  dsimp,
  replace hX₂ : ∀ x ∈ X, w x * x 0 = 0,
  { intros x hx,
    rw hX₂ x hx,
    simp },
  rw finset.sum_congr rfl hX₂,
  simp,
end

def simplicial_complex.dimension_drop (S : simplicial_complex 𝕜 (fin m.succ → 𝕜)) :
  simplicial_complex 𝕜 E :=
{ faces := {Y | ∃ X ∈ S.faces, finset.image matrix.vec_tail X = Y ∧
    ∀ (x : fin (m+1) → 𝕜), x ∈ X → x 0 = 0 },
  not_empty_mem := sorry,
  down_closed :=
  begin
    rintro _ Y ⟨X, hX₁, rfl, hX₂⟩ YX,
    sorry
  end,
  indep :=
  begin
    rintro _ ⟨X, hX₁, rfl, hX₂⟩,
    let f : ((finset.image matrix.vec_tail X : set (fin m → 𝕜))) → (X : set (fin (m+1) → 𝕜)),
    { intro t,
      refine ⟨matrix.vec_cons 0 t.1, _⟩,
      rcases t with ⟨t, ht⟩,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image] at ht,
      rcases ht with ⟨x, hx, rfl⟩,
      suffices : matrix.vec_head x = 0,
      { rw ← this,
        simpa },
      apply hX₂ x hx },
    have hf : function.injective f,
    { rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h,
      rw subtype.ext_iff at h,
      change matrix.vec_cons _ x₁ = matrix.vec_cons _ x₂ at h,
      apply subtype.ext,
      apply_fun matrix.vec_tail at h,
      simpa using h },
    have := affine_independent_proj _ (S.indep hX₁),
    { convert this.comp_embedding ⟨f, hf⟩,
      ext p,
      dsimp,
      simp },
    rintro ⟨i, hi⟩,
    apply hX₂ _ hi,
  end,
  inter_subset_convex_hull :=
  begin
    rintro _ _ ⟨X, hX₁, rfl, hX₂⟩ ⟨Y, hY₁, rfl, hY₂⟩,
    simp only [finset.coe_image],
    sorry
  end }

theorem strong_sperner {S : simplicial_complex 𝕜 (fin (m+1) → 𝕜)} {f}
  (hS₁ : S.space = std_simplex 𝕜 (fin (m+1))) (hS₂ : S.finite) (hS₃ : S.full_dimensional)
  (hf : is_sperner_coloring S f) :
  odd ((S.faces_finset hS₂).filter (panchromatic f)).card :=
begin
  induction m with n ih generalizing f,
  { apply strong_sperner_zero hS₁ },
  sorry
end

theorem sperner {S : simplicial_complex 𝕜 (fin (m+1) → 𝕜)}
  (hS₁ : S.space = std_simplex 𝕜 (fin (m+1))) (hS₂ : S.finite) (hS₃ : S.full_dimensional)
  {f} (hf : is_sperner_coloring S f) :
  ∃ X ∈ S.faces, panchromatic f X :=
begin
  obtain ⟨X, hX⟩ := finset.card_pos.1 (strong_sperner hS₁ hS₂ hS₃ hf).pos,
  simp only [mem_faces_finset, finset.mem_filter] at hX,
  exact ⟨_, hX.1, hX.2⟩,
end

end geometry
