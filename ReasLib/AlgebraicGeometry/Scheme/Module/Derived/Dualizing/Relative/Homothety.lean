/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.AffineRestriction
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative.Homothety

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- For a flat, locally finitely presented morphism, the homothety morphism of a relative
dualizing complex from the tensor unit to its derived internal endomorphism object is an
isomorphism. -/
theorem homothetyIsIso
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H_W : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (C : Scheme.RelativeDualizingComplex f W δ hδ H_W)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) :
    IsIso (@MonoidalClosed.curry' (RingedSpace.ModuleDerived X.toRingedSpace) _ _
      C.complex C.complex (H_X.closed C.complex) (𝟙 C.complex)) := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
