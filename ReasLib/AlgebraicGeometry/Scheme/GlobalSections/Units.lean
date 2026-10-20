module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Unit quotients of global sections

This leaf owns the canonical quotient of global units by the units coming
from the base ring of a structure morphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The quotient of global units by scalar units for a morphism `f : X ⟶ Spec R`. -/
noncomputable abbrev unitsQuotient
    (f : X ⟶ Spec (CommRingCat.of R)) : Type u :=
  ((Scheme.globalSectionsRing X)ˣ) ⧸
    (Units.map (globalSectionsMap f).toMonoidHom).range

/-- The carrier of `unitsQuotient` is the explicit quotient of global units by scalar units. -/
theorem unitsQuotient_def
    (f : X ⟶ Spec (CommRingCat.of R)) :
    unitsQuotient f =
      (((Scheme.globalSectionsRing X)ˣ) ⧸
        (Units.map (globalSectionsMap f).toMonoidHom).range) := sorry

/-- The scalar-unit quotient is canonically a commutative group. -/
noncomputable instance instCommGroupUnitsQuotient
    (f : X ⟶ Spec (CommRingCat.of R)) : CommGroup (unitsQuotient f) :=
  QuotientGroup.Quotient.commGroup
    ((Units.map (globalSectionsMap f).toMonoidHom).range)

end AlgebraicGeometry.Scheme.Hom
