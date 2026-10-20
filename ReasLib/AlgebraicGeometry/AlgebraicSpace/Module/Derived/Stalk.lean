module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Derived étale stalks

The exact étale module-stalk functor sends derived modules on an algebraic space
to derived modules over the étale local ring at a geometric point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The étale module-stalk functor at a geometric point preserves finite limits. -/
instance sheafModuleStalkFunctor_preservesFiniteLimits (xbar : GeometricPoint X) :
    PreservesFiniteLimits
      ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)) :=
  sorry

/-- The étale module-stalk functor at a geometric point preserves finite colimits. -/
instance sheafModuleStalkFunctor_preservesFiniteColimits (xbar : GeometricPoint X) :
    PreservesFiniteColimits
      ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor (structureSheaf X)) :=
  sorry

/-- The derived étale stalk of `E` at a geometric point, as an object of the derived
category of modules over the étale local ring. -/
noncomputable def stalkDerived (xbar : GeometricPoint X) (E : ModuleDerived X) :
    DerivedCategory (ModuleCat (etaleLocalRing X xbar)) :=
  ((GeometricPoint.toSmallEtalePoint xbar).sheafModuleStalkFunctor
    (structureSheaf X)).mapDerivedCategory.obj E

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
