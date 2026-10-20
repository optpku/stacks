module

public import Mathlib.Algebra.Group.Equiv.Defs
public import ReasLib.Algebra.Ring.CommutatorQuotient

/-!
# Additive identification of a commutative ring with its commutator quotient
-/

@[expose] public section

noncomputable section

universe u

open Ring
open scoped Ring

namespace Ring.CommutatorQuotient

variable {R : Type u} [CommRing R]

/-- The canonical additive identification of a commutative ring with its
additive commutator quotient. -/
def mkAddEquiv : R ≃+ R♮ where
  toFun := mk
  invFun := QuotientAddGroup.lift (commutatorAddSubgroup R) (AddMonoidHom.id R) sorry
  left_inv := sorry
  right_inv := sorry
  map_add' := mk.map_add

/-- The canonical additive identification sends `x` to its class in `R♮`. -/
theorem mkAddEquiv_apply (x : R) : mkAddEquiv x = mk x := sorry

/-- The inverse of the canonical additive identification recovers a representative. -/
theorem mkAddEquiv_symm_mk (x : R) : mkAddEquiv.symm (mk x) = x := sorry

end Ring.CommutatorQuotient
