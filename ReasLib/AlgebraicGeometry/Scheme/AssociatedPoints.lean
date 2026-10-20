module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints

/-!
# Associated points of schemes

This leaf specializes associated points of modules to the structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.RingedSpace

variable (X : Scheme.{u})

/-- The associated points of `X` are the associated points of its structure sheaf. -/
def associatedPoints : Set X :=
  Scheme.Modules.associatedPoints
    (SheafOfModules.unit X.ringCatSheaf : RingedSpace.Modules X.toRingedSpace)

/-- Membership in `X.associatedPoints` is the associated-prime condition for
the stalk of the structure sheaf. -/
theorem mem_associatedPoints_iff (x : X) :
    x ∈ X.associatedPoints ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat (SheafOfModules.unit X.ringCatSheaf :
            RingedSpace.Modules X.toRingedSpace) (x : X.toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme
