/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.OverField

@[expose] public section

open CategoryTheory DerivedCategory.TStructure

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.SchemeOverField

open RingedSpace RingedSpace.ModuleDerived

/- Example 36.35.2 (1): over a field, relative perfection for a derived module on a
finite-presentation scheme is equivalent to boundedness and pseudo-coherence. -/
@[stacks 0DI1] #check
  (AlgebraicGeometry.SchemeOverField.isPerfectOver_iff_bounded_and_pseudoCoherent :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Scheme.Hom.FinitePresentation X.hom]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase X.hom.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase X.hom.toShHom).restrict U.isOpenEmbedding))]
      (E : ModuleDerived X.left.toRingedSpace),
      IsPerfectOver X.hom.toShHom E ↔
        t.bounded E ∧ RingedSpace.ModuleDerived.IsPseudoCoherent E)

/- Example 36.35.2 (2): over a field, relative perfection for a derived module on a
finite-presentation scheme is equivalent to bounded coherent cohomology. This is a relative
condition and does not assert perfectness on every fibre. -/
@[stacks 0DI1] #check
  (AlgebraicGeometry.SchemeOverField.isPerfectOver_iff_bounded_and_coherentCohomology :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
      [Scheme.Hom.FinitePresentation X.hom]
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase X.hom.toShHom).carrier,
        CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase X.hom.toShHom).restrict U.isOpenEmbedding))]
      (E : ModuleDerived X.left.toRingedSpace),
      IsPerfectOver X.hom.toShHom E ↔
        t.bounded E ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (Scheme.ringCatSheaf X.left)) E)

end AlgebraicGeometry.SchemeOverField
