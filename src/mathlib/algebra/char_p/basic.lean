import algebra.char_p.basic

variables (R : Type*)

lemma char_p.nat_cast_inj_on_Iio [add_group_with_one R] (p : ℕ) [char_p R p] :
  (set.Iio p).inj_on (coe : ℕ → R) :=
λ a ha b hb hab, ((char_p.nat_cast_eq_nat_cast _ _).1 hab).eq_of_lt_of_lt ha hb
