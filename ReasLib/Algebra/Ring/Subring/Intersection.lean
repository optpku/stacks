module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Algebra structures for subrings and their intersections

This file supplies the canonical algebra structures induced by inclusions of
subrings of a commutative ring, together with the scalar towers associated to
a binary intersection.
-/

@[expose] public section

universe u

namespace Subring

variable {R : Type u} [CommRing R]

/-- The canonical algebra structure on an ambient commutative ring over one
of its subrings. -/
@[reducible]
def subtypeAlgebra (S : Subring R) : Algebra S R :=
  S.subtype.toAlgebra

/-- An ambient commutative ring is canonically an algebra over each of its
subrings. -/
instance instAlgebraSubtype (S : Subring R) : Algebra S R :=
  S.subtypeAlgebra

/-- A containment of subrings induces the canonical algebra structure on the
larger subring over the smaller one. -/
@[reducible]
def inclusionAlgebra {S T : Subring R} (h : S ≤ T) : Algebra S T :=
  (Subring.inclusion h).toAlgebra

/-- The left subring is canonically an algebra over its intersection with a
second subring. -/
instance instAlgebraInfLeft (A B : Subring R) : Algebra (A ⊓ B : Subring R) A :=
  inclusionAlgebra inf_le_left

/-- The right subring is canonically an algebra over its intersection with a
second subring. -/
instance instAlgebraInfRight (A B : Subring R) : Algebra (A ⊓ B : Subring R) B :=
  inclusionAlgebra inf_le_right

/-- The inclusions from a binary intersection through its left component to
the ambient ring form a scalar tower. -/
instance instIsScalarTowerInfLeftAmbient (A B : Subring R) :
    IsScalarTower (A ⊓ B : Subring R) A R :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The inclusions from a binary intersection through its right component to
the ambient ring form a scalar tower. -/
instance instIsScalarTowerInfRightAmbient (A B : Subring R) :
    IsScalarTower (A ⊓ B : Subring R) B R :=
  .of_algebraMap_eq fun _ ↦ rfl

end Subring
