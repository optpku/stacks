/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Associated.Multiplication
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 28.28.4: for an ample invertible module and its section-ring projective morphism,
the normalized pullback comparison for associated twisted-section sheaves carries canonical
multiplication by an integral twist to the tensor product of the two comparison components. -/
@[stacks 01QK] #check
  (AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap.pullback_associatedTwisted_mul_comm :
    ∀ {X : Scheme.{u}} (L : X.Modules) [Scheme.Modules.Invertible L]
      [Scheme.Modules.IsAmple L]
      (f : X ⟶ Proj (RingedSpace.GradedSections.grading L))
      (hf : Scheme.Modules.IsSectionRingProjMap L f)
      (e :
        (ObjectProperty.ι (fun G : X.Modules ↦ G.IsQuasicoherent) ⋙
            Scheme.Modules.GradedSections.associatedTwistedFunctor L ⋙
              Scheme.Modules.pullback f) ≅
          ObjectProperty.ι (fun G : X.Modules ↦ G.IsQuasicoherent))
      (h_e :
        ∀ (G : ObjectProperty.FullSubcategory
            (fun G : X.Modules ↦ G.IsQuasicoherent))
          (m : Scheme.Modules.GradedSections.twistedInternalGrading L G.obj 0),
          ((Scheme.Modules.globalSectionsPullback f
                (Scheme.Modules.GradedSections.associatedTwistedSheaf L G.obj) ≫
              Scheme.Modules.globalSectionsMap (e.hom.app G)).hom)
              (Scheme.Modules.GradedSections.degreeZeroToAssociatedTwistedGlobalSections
                L G.obj m) =
            Scheme.Modules.GradedSections.twistedDegreeZeroIso L G.obj m)
      (F : X.Modules) (hF : F.IsQuasicoherent) (n : ℤ)
      (hLn : (L ^⊗ n).IsQuasicoherent)
      (hFLn : (F ⊗ L ^⊗ n).IsQuasicoherent)
      (C : Scheme.Modules.GradedSections.AssociatedTwistedMultiplication L F),
      Scheme.Modules.pullbackTensorMap f (C.hom n) ≫
          e.hom.app ⟨F ⊗ L ^⊗ n, hFLn⟩ =
        e.hom.app ⟨F, hF⟩ ⊗ₘ e.hom.app ⟨L ^⊗ n, hLn⟩)
