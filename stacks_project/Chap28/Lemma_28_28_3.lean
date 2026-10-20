/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Associated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.28.3: for an ample invertible module `L` and its section-ring projective
morphism `f`, the associated sheaf of the full integer-graded twisted-section module pulls
back naturally to every quasicoherent module, and the induced degree-zero global-sections
composite is the canonical zeroth-twist identification. -/
@[stacks 01QJ] #check
  (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.exists_pullback_associatedTwistedFunctor_iso :
    ∀ {X : Scheme.{u}} (L : X.Modules) [Scheme.Modules.Invertible L]
      [Scheme.Modules.IsAmple L]
      (f : X ⟶ Proj (RingedSpace.GradedSections.grading L))
      (hf : Scheme.Modules.IsSectionRingProjMap L f),
      ∃ e :
        (ObjectProperty.ι (fun F : X.Modules ↦ F.IsQuasicoherent) ⋙
            Scheme.Modules.GradedSections.associatedTwistedFunctor L ⋙
            Scheme.Modules.pullback f) ≅
          ObjectProperty.ι (fun F : X.Modules ↦ F.IsQuasicoherent),
        ∀ (F : ObjectProperty.FullSubcategory
            (fun F : X.Modules ↦ F.IsQuasicoherent))
          (m : Scheme.Modules.GradedSections.twistedInternalGrading L F.obj 0),
          ((Scheme.Modules.globalSectionsPullback f
                (Scheme.Modules.GradedSections.associatedTwistedSheaf L F.obj) ≫
              Scheme.Modules.globalSectionsMap (e.hom.app F)).hom)
              (Scheme.Modules.GradedSections.degreeZeroToAssociatedTwistedGlobalSections
                L F.obj m) =
            Scheme.Modules.GradedSections.twistedDegreeZeroIso L F.obj m)
