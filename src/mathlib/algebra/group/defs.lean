import algebra.group.defs

set_option old_structure_cmd true

/-- An `add_cancel_semigroup` is an additive semigroup such that `a + b = a + c` implies `b = c`,
and `a + c = b + c` implies `a = b`. -/
class add_cancel_semigroup (α : Type*)
  extends add_left_cancel_semigroup α, add_right_cancel_semigroup α

/-- A `cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`, and
`a * c = b * c` implies `a = b`. -/
@[to_additive add_cancel_semigroup]
class cancel_semigroup (α : Type*) extends left_cancel_semigroup α, right_cancel_semigroup α

attribute [to_additive] cancel_semigroup.to_left_cancel_semigroup
  cancel_semigroup.to_right_cancel_semigroup
