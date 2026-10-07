module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints

@[expose] public section

universe u

/- Definition 31.2.1: canonical associated-point owners for scheme modules and schemes. -/
@[stacks 02OJ] #check
  (@AlgebraicGeometry.Scheme.Modules.associatedPoints :
    {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → Set X)

#check
  (@AlgebraicGeometry.Scheme.Modules.mem_associatedPoints_iff :
    {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → (x : X) →
      x ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints F ↔
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
          associatedPrimesOfModule (X.presheaf.stalk x)
            (AlgebraicGeometry.RingedSpace.stalkModuleCat F (x : X.toRingedSpace)))

#check
  (@AlgebraicGeometry.Scheme.associatedPoints :
    (X : AlgebraicGeometry.Scheme.{u}) → Set X)

#check
  (@AlgebraicGeometry.Scheme.mem_associatedPoints_iff :
    (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
      x ∈ X.associatedPoints ↔
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
          associatedPrimesOfModule (X.presheaf.stalk x)
            (AlgebraicGeometry.RingedSpace.stalkModuleCat
              (SheafOfModules.unit X.ringCatSheaf :
                AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)
              (x : X.toRingedSpace)))
