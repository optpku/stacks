module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.Perm.Sign
public import ReasLib.RepresentationTheory.IntegerCharacter

/-! # The sign character of the lifted symmetric group -/

@[expose] public section

universe u

namespace IntegerCharacter

/-- The sign character of the symmetric group, lifted to an arbitrary universe. -/
def permutationSign (n : ℕ) : ULift.{u} (Equiv.Perm (Fin n)) →* ℤˣ :=
  Equiv.Perm.sign.comp (MulEquiv.ulift (α := Equiv.Perm (Fin n))).toMonoidHom

/-- The lifted sign character evaluates as the sign of the underlying permutation. -/
theorem permutationSign_apply (n : ℕ) (σ : ULift.{u} (Equiv.Perm (Fin n))) :
    permutationSign n σ = Equiv.Perm.sign σ.down :=
  rfl

end IntegerCharacter
