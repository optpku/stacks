/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.35.6: for a flat, locally finitely presented morphism of schemes,
relative perfectness is preserved by arbitrary scheme base change. -/
@[stacks 0DI5] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo.baseChange :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f] (g : S' ⟶ S)
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (pullback.snd f g).toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase (pullback.snd f g).toShHom).restrict U.isOpenEmbedding))],
      (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) →
      AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f K →
        AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo
          (pullback.snd f g)
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
            (pullback.fst f g).toShHom).obj K))
