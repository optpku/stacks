/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Retracts
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage
public import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice

@[expose] public section

/-!
# Retracts of relatively perfect derived modules on schemes

Relative perfectness for flat, locally finitely presented scheme morphisms is stable under
retracts in the derived category of modules.
-/

open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

/-- The objects perfect relative to a flat, locally finitely presented scheme morphism are
stable under retracts. -/
instance perfectRelativeTo_isStableUnderRetracts (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))] :
    ObjectProperty.IsStableUnderRetracts (perfectRelativeTo f) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
