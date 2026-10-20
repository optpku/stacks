module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

/-!
# Associated points of scheme modules

This leaf owns the stalkwise associated-point set of a module on a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.RingedSpace

variable {X : Scheme.{u}}

/-- The associated points `Ass(F)` of a scheme module `F` are the points whose stalk has its
maximal ideal as an associated prime. -/
def associatedPoints (F : X.Modules) : Set X :=
  {x : X | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
    associatedPrimesOfModule (X.presheaf.stalk x)
      (RingedSpace.stalkModuleCat F (x : X.toRingedSpace))}

/-- Membership in `associatedPoints F` is the associated-prime condition at
the stalk over the given point. -/
theorem mem_associatedPoints_iff (F : X.Modules) (x : X) :
    x ∈ associatedPoints F ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat F (x : X.toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme.Modules
