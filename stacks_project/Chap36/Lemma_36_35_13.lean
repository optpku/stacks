/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Lemma 36.35.13: for a flat, locally finitely presented morphism `f : X ⟶ S` and a
pseudo-coherent derived `𝒪_X`-module `E`, relative perfectness is equivalent to local
boundedness below of `E` and of its derived pullback to every scheme-theoretic fiber. -/
@[stacks 0GEH] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [∀ U : TopologicalSpace.Opens (AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := AlgebraicGeometry.RingedSpace.Modules
            ((AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent E),
        AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f E ↔
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow E ∧
            ∀ s : S, AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow
              ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
                (f.fiberι s).toShHom).obj E))
