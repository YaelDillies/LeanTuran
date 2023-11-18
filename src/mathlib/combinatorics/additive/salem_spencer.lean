import combinatorics.additive.salem_spencer
import data.zmod.basic
import mathlib.algebra.char_p.basic

open finset

section roth_number_nat
variables {s : finset ℕ} {k n : ℕ}

lemma fin.roth_number_nat_le_add_roth_number (hkn : 2 * k ≤ n) :
  roth_number_nat k ≤ add_roth_number (Iio k : finset $ fin n.succ) :=
begin
  classical,
  obtain ⟨s, hsm, hscard, hs⟩ := roth_number_nat_spec k,
  simp only [subset_iff, mem_range] at hsm,
  rw two_mul at hkn,
  rw [←hscard, ←card_image_of_inj_on ((char_p.nat_cast_inj_on_Iio (zmod n.succ) n.succ).mono $
    λ x hx, nat.lt_succ_iff.2 $ (hsm hx).le.trans $ le_add_self.trans hkn)],
  refine add_salem_spencer.le_add_roth_number _ _,
    { rw coe_image,
    rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ habc,
    norm_cast at habc,
    refine congr_arg _ (hs ha hb hc $ char_p.nat_cast_inj_on_Iio _ n.succ _ _ habc);
    simp only [nat.lt_succ_iff, set.mem_Iio];
    refine (add_le_add (hsm _).le (hsm _).le).trans hkn; assumption },
 { replace hkn := nat.lt_succ_iff.2 (le_add_self.trans hkn),
    simp only [image_subset_iff, mem_Iio, fin.lt_iff_coe_lt_coe, fin.coe_of_nat_eq_mod],
    rintro x hx,
    rw [nat.mod_eq_of_lt hkn, nat.mod_eq_of_lt ((hsm hx).trans hkn)],
    exact hsm hx }
end

end roth_number_nat
