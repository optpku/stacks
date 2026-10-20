/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Tensor
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.35.5 (1): for a flat, locally finitely presented morphism of schemes,
every perfect object of `D(𝒪_X)` is perfect over the base. -/
@[stacks 0DI4] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect.isPerfectRelativeTo :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      {K : RingedSpace.ModuleDerived X.toRingedSpace},
      RingedSpace.ModuleDerived.IsPerfect K →
        AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f K)

/- Lemma 36.35.5 (2): for a flat, locally finitely presented morphism of schemes,
tensoring a perfect object by an object perfect over the base preserves relative perfectness. -/
@[stacks 0DI4] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPerfect.tensor_isPerfectRelativeTo :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      {K M : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect K →
        AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f M →
          AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f (K ⊗ᴸ M))
