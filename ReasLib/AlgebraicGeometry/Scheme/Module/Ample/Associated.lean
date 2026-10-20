module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Associated

/-!
# Associated twisted-section sheaves for ample modules

For the projective-spectrum morphism determined by an ample invertible module, the sheaf
associated to the full twisted-section module pulls back naturally to the original
quasi-coherent module.  The comparison is normalized by its degree-zero map on global sections.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap

variable {X : Scheme.{u}}

/-- Along the section-ring projective morphism of an ample invertible module, the associated
sheaves of full twisted-section modules pull back naturally to quasi-coherent modules, and the
induced degree-zero composite is the canonical zeroth-twist identification. -/
theorem exists_pullback_associatedTwistedFunctor_iso
    (L : X.Modules) [Invertible L] [IsAmple L]
    (f : X ⟶ Proj (RingedSpace.GradedSections.grading L))
    (hf : IsSectionRingProjMap L f) :
    ∃ e :
      (ObjectProperty.ι (fun F : X.Modules ↦ F.IsQuasicoherent) ⋙
          GradedSections.associatedTwistedFunctor L ⋙ pullback f) ≅
        ObjectProperty.ι (fun F : X.Modules ↦ F.IsQuasicoherent),
      ∀ (F : ObjectProperty.FullSubcategory
          (fun F : X.Modules ↦ F.IsQuasicoherent))
        (m : GradedSections.twistedInternalGrading L F.obj 0),
        ((globalSectionsPullback f
              (GradedSections.associatedTwistedSheaf L F.obj) ≫
            globalSectionsMap (e.hom.app F)).hom)
            (GradedSections.degreeZeroToAssociatedTwistedGlobalSections
              L F.obj m) =
          GradedSections.twistedDegreeZeroIso L F.obj m := sorry

end AlgebraicGeometry.Scheme.Modules.IsSectionRingProjMap
