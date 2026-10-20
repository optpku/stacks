module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Localization
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Localization
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Restriction

/-! # Cohomological descent for hypercoverings of a presheaf -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open CategoryTheory.HypercoveringOf CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.CohomologyOverPresheaf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [HasEqualizers C] [HasPullbacks C]
variable (G : Cᵒᵖ ⥤ Type (max w v))

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasWeakSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasSheafify (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}]
variable [∀ P : (G.Elementsᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{max w v},
    (Presheaf.localizationForget G).op.HasPointwiseRightKanExtension P]

variable (K : HypercoveringOf J G)

/-- The canonical augmentation from the original total site to the localization at the target. -/
abbrev augmentationForget :
    Grothendieck (overSiteDiagram K.simplicial) ⥤ G.Elementsᵒᵖ :=
  toLocalizedTotalSite J K ⋙ totalForget (toLocalizedSimplicial J K)

/-- The augmentation followed by localization is the original total-site projection. -/
theorem augmentationForget_comp_localizationForget :
    augmentationForget J G K ⋙ Presheaf.localizationForget G =
      totalForget K.simplicial := sorry

/-- The original total-site augmentation to the localization is continuous. -/
instance augmentationForget_isContinuous :
    (augmentationForget J G K).IsContinuous
      (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G) := sorry

/-- The original total-site augmentation to the localization is cocontinuous. -/
instance augmentationForget_isCocontinuous :
    (augmentationForget J G K).IsCocontinuous
      (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G) := sorry

/-- Inverse image along the original total-site augmentation. -/
abbrev localizedInverseImage :
    Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⥤
      Sheaf
        (overSiteTotalTopology J K.simplicial)
        AddCommGrpCat.{max w v} :=
  (augmentationForget J G K).sheafPushforwardContinuous
    AddCommGrpCat.{max w v} (overSiteTotalTopology J K.simplicial)
    (Presheaf.localizationSite J G)

/-- Inverse image along the composite of augmentation and localization. -/
abbrev totalInverseImage :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      Sheaf
        (overSiteTotalTopology J K.simplicial)
        AddCommGrpCat.{max w v} :=
  Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
    localizedInverseImage J G K

variable [HasWeakSheafify
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [HasSheafify
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [HasGlobalSectionsFunctor
    (overSiteTotalTopology J K.simplicial)
    AddCommGrpCat.{max w v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤
      AddCommGrpCat.{max w v},
    (augmentationForget J G K).op.HasPointwiseRightKanExtension P]

/-- The exact presentation of inverse image along the original total-site augmentation. -/
abbrev localizedInverseImageExact :
    Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⥤ₑ
      Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v} :=
  siteAbelianInverseImageExact.{max u v w, max u v w, max u v w, v, max w v}
    (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G)
    (augmentationForget J G K)

/-- Inverse image along the augmentation preserves constant abelian sheaves. -/
def localizedConstantSheafCompInverseImageIso :
    constantSheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v} ⋙
      localizedInverseImage J G K ≅
    constantSheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v} :=
  (augmentationForget J G K).constantSheafRestrictionIso
    (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G)
    AddCommGrpCat.{max w v}

/-- Pullback followed by the constant-sheaf comparison commutes with sheaf morphisms. -/
theorem gammaLocalizationInverseImageComparison_laws
    {E E' : Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}}
    (f : E ⟶ E') (h : constantIntegerSheaf.{max u v w, v, max w v} (Presheaf.localizationSite J G) ⟶ E) :
    (localizedConstantSheafCompInverseImageIso J G K).inv.app
        (AddCommGrpCat.of (ULift.{max w v} ℤ)) ≫
      (localizedInverseImage J G K).map (h ≫ f) =
    ((localizedConstantSheafCompInverseImageIso J G K).inv.app
        (AddCommGrpCat.of (ULift.{max w v} ℤ)) ≫
      (localizedInverseImage J G K).map h) ≫
      (localizedInverseImage J G K).map f := sorry

/-- The underived augmentation comparison on global sections in the constant-integer Hom model. -/
def gammaLocalizationInverseImageComparison :
    globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G) ⟶
      localizedInverseImage J G K ⋙
        globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial) where
  app E := AddCommGrpCat.ofHom
    ((Preadditive.leftComp _
      ((localizedConstantSheafCompInverseImageIso J G K).inv.app
        (AddCommGrpCat.of (ULift.{max w v} ℤ)))).comp
      (localizedInverseImageExact J G K).obj.mapAddHom)
  naturality _ _ f := by
    ext h
    exact gammaLocalizationInverseImageComparison_laws J G K f h

/-- The augmentation comparison pulls back a morphism and precomposes with the canonical
constant-integer comparison. -/
theorem gammaLocalizationInverseImageComparison_app
    (E : Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})
    (f : constantIntegerSheaf.{max u v w, v, max w v} (Presheaf.localizationSite J G) ⟶ E) :
    (gammaLocalizationInverseImageComparison J G K).app E f =
      (localizedConstantSheafCompInverseImageIso J G K).inv.app
          (AddCommGrpCat.of (ULift.{max w v} ℤ)) ≫
        (localizedInverseImage J G K).map f := rfl

/-- The underived total comparison is the composite of the localization and augmentation maps. -/
theorem rGammaOverPresheafTotalComparison_underived_app
    (E : Sheaf J AddCommGrpCat.{max w v}) :
    (homFunctorLocalizationComparison J G ≫
        whiskerLeft (Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v})
          (gammaLocalizationInverseImageComparison J G K)).app E =
      (homFunctorLocalizationComparison J G).app E ≫
        (gammaLocalizationInverseImageComparison J G K).app
          ((Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).obj E) := rfl

variable [HasDerivedCategory.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w} AddCommGrpCat.{max u v w}]
variable [HasDerivedCategory.{max u v w}
    (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{max u v w}
    (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v})]
variable [(globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(localizedInverseImageExact J G K).obj.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]
variable [(globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w v}))]
variable [((localizedInverseImageExact J G K).obj ⋙
      globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v}))]

/-- The bounded-below augmentation comparison with exact derived inverse image on the original
total site of the hypercovering. -/
def rGammaLocalizationInverseImageComparison :
    Functor.RightDerived.Bounded.functor
      (globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)) ⟶
    siteAbelianInverseImageBoundedBelowDerived.{max u v w, max u v w, max u v w, v, max w v, max u v w, max u v w}
      (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G)
      (augmentationForget J G K) ⋙
    Functor.RightDerived.Bounded.functor
      (globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)) :=
  Functor.RightDerived.Bounded.map
    (show globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G) ⟶
      (localizedInverseImageExact J G K).obj ⋙
        globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial) from
      gammaLocalizationInverseImageComparison J G K) ≫
    Functor.RightDerived.Composition.BoundedBelow.comparison
      (localizedInverseImageExact J G K).obj
      (globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)) ≫
    whiskerRight
      (ExactFunctor.Derived.Plus.rightDerivedIso (localizedInverseImageExact J G K)).hom
      (Functor.RightDerived.Bounded.functor
        (globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)))

/-- Bounded-below cohomological descent for a hypercovering after localization at its target. -/
instance rGammaLocalizationInverseImageComparison_app_isIso
    (E : DerivedCategory.Plus
      (Sheaf (Presheaf.localizationSite J G) AddCommGrpCat.{max w v})) :
    IsIso ((rGammaLocalizationInverseImageComparison J G K).app E) := sorry

variable [(homFunctor.{w, v, u} J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
variable [(Presheaf.elementsOpInverseImage J G AddCommGrpCat.{max w v} ⋙
      globalSectionsHomFunctor.{max w v} (Presheaf.localizationSite J G)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

set_option maxHeartbeats 800000 in
/-- The composite bounded-below cohomology comparison along localization and augmentation. -/
def rGammaOverPresheafTotalComparison :
    derivedFunctor.{max u v w, w, v, u} J G ⟶
      (siteAbelianInverseImageBoundedBelowDerived.{max u v w, v, u, v, max w v, max u v w, max u v w} (Presheaf.localizationSite J G) J
        (Presheaf.localizationForget G) ⋙
       siteAbelianInverseImageBoundedBelowDerived.{max u v w, max u v w, max u v w, v,
        max w v, max u v w, max u v w}
        (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G)
        (augmentationForget J G K)) ⋙
      Functor.RightDerived.Bounded.functor
        (globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)) :=
  rGammaOverPresheafLocalizationComparison J G ≫
    whiskerLeft
      (siteAbelianInverseImageBoundedBelowDerived.{max u v w, v, u, v, max w v, max u v w, max u v w} (Presheaf.localizationSite J G) J
        (Presheaf.localizationForget G))
      (rGammaLocalizationInverseImageComparison J G K) ≫
    (associator
      (siteAbelianInverseImageBoundedBelowDerived.{max u v w, v, u, v, max w v, max u v w, max u v w} (Presheaf.localizationSite J G) J
        (Presheaf.localizationForget G))
      (siteAbelianInverseImageBoundedBelowDerived.{max u v w, max u v w, max u v w, v,
        max w v, max u v w, max u v w}
        (overSiteTotalTopology J K.simplicial) (Presheaf.localizationSite J G)
        (augmentationForget J G K))
      (Functor.RightDerived.Bounded.functor
        (globalSectionsHomFunctor.{max w v} (overSiteTotalTopology J K.simplicial)))).inv

/-- The bounded-below total cohomology comparison of a presheaf hypercovering is invertible. -/
instance rGammaOverPresheafTotalComparison_app_isIso
    (E : DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    IsIso ((rGammaOverPresheafTotalComparison J G K).app E) := sorry

end CategoryTheory.Sheaf.CohomologyOverPresheaf
