/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/- Compatibility check for the source-facing API. -/
#check (AlgebraicGeometry.Scheme.RelativeDualizingComplex :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))],
    (W : (pullback f f).Opens) → (δ : X ⟶ W.toScheme) → [IsClosedImmersion δ] →
    (hδ : δ ≫ W.ι = pullback.diagonal f) →
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] →
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)] →
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal] →
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)) → Type (u + 1))
