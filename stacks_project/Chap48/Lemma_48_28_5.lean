/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap48.Definition_48_28_1_RelativeDualizingComplex

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/- Lemma 48.28.5 -/
@[stacks 0E2X] #check (AlgebraicGeometry.Scheme.RelativeDualizingComplex.existsRelativeDualizingComplex :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [Flat f] → [LocallyOfFinitePresentation f] →
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))] →
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] →
    ∃ (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme)
      (h_closed : IsClosedImmersion δ)
      (hδ : δ ≫ W.ι = pullback.diagonal f)
      (monoidalW : MonoidalCategory
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
      (laxPushforward : @CategoryTheory.Functor.LaxMonoidal
        (RingedSpace.ModuleDerived X.toRingedSpace) inferInstance inferInstance
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace) inferInstance monoidalW
        (RingedSpace.moduleDerivedPushforward δ.toShHom))
      (H : @MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)
        inferInstance monoidalW),
      Nonempty (@Scheme.RelativeDualizingComplex X S f inferInstance inferInstance inferInstance W δ
        h_closed hδ inferInstance monoidalW laxPushforward H))

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
