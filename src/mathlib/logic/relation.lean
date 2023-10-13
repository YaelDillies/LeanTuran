variables {α : Type*} {R : α → α → Prop} {a b : α}

lemma curry_eq_of_symmetric_transitive (symm : symmetric R) (trans : transitive R) (hab : R a b) :
  R a = R b := funext $ λ c, propext ⟨trans $ symm hab, trans hab⟩
