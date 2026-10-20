module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre

/-!
# Derived comparison of étale and pro-étale module sheaves

Canonical inverse image on module sheaves and its bounded-below derived action,
with the right-derived direct image and the cohomological essential-image subcategory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]

/-- Module sheaves on the small pro-étale site form a Grothendieck abelian category. -/
instance proEtModuleSheaf_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) := by
  have : (equivSmallModel.{u + 1} X.ProEt).symm.inverse.IsDenseSubsite
      (ProEt.topology X)
      ((equivSmallModel.{u + 1} X.ProEt).inverse.inducedTopology (ProEt.topology X)) :=
    inferInstanceAs ((equivSmallModel.{u + 1} X.ProEt).functor.IsDenseSubsite
      (ProEt.topology X)
      ((equivSmallModel.{u + 1} X.ProEt).inverse.inducedTopology (ProEt.topology X)))
  have : HasSheafify
      ((equivSmallModel.{u + 1} X.ProEt).inverse.inducedTopology (ProEt.topology X))
      (ModuleCat.{u + 1} Λ) :=
    (equivSmallModel.{u + 1} X.ProEt).symm.hasSheafify _ (ProEt.topology X)
      (ModuleCat.{u + 1} Λ)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1}
      (ProEt.topology X) (ModuleCat.{u + 1} Λ)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the left Kan extension on module presheaves is a colimit over
the corresponding costructured-arrow category. -/
private def etaleToProEtModuleLanEvaluationIso (Y : X.ProEtᵒᵖ) :
    (etaleToProEt X).op.lan ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ (ModuleCat.{u + 1} Λ)).obj Y ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} Λ)).obj
        (CostructuredArrow.proj (etaleToProEt X).op Y) ⋙ colim :=
  NatIso.ofComponents (fun F =>
    (etaleToProEt X).op.leftKanExtensionObjIsoColimit F Y) (fun {F₁ F₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (etaleToProEt X).op F₁ Y).hom_ext
    intro T
    have h₂ := congr_app ((etaleToProEt X).op.lanUnit.naturality φ) T.left
    change φ.app T.left ≫ ((etaleToProEt X).op.leftKanExtensionUnit F₂).app T.left =
      ((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.lan.map φ).app ((etaleToProEt X).op.obj T.left) at h₂
    change
      (((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₁).map T.hom) ≫
          (((etaleToProEt X).op.lan.map φ).app Y ≫
            ((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₂ Y).hom) =
      (((etaleToProEt X).op.leftKanExtensionUnit F₁).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₁).map T.hom) ≫
          (((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₁ Y).hom ≫
            colim.map (Functor.whiskerLeft (CostructuredArrow.proj _ Y) φ))
    simp only [Category.assoc, NatTrans.naturality_assoc,
      ← reassoc_of% h₂, Functor.ι_leftKanExtensionObjIsoColimit_hom_assoc]
    change φ.app T.left ≫
        ((etaleToProEt X).op.leftKanExtensionUnit F₂).app T.left ≫
        ((etaleToProEt X).op.leftKanExtension F₂).map T.hom ≫
        ((etaleToProEt X).op.leftKanExtensionObjIsoColimit F₂ Y).hom =
      colimit.ι _ T ≫ colimMap (Functor.whiskerLeft (CostructuredArrow.proj _ Y) φ)
    rw [Functor.ι_leftKanExtensionObjIsoColimit_hom, ι_colimMap]
    rfl)

variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]

/-- Inverse image of module sheaves from the small étale site to the small
pro-étale site preserves finite limits. -/
instance etaleToProEtPullback_module_preservesFiniteLimits :
    PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)) := by
  have : PreservesFiniteLimits
      ((etaleToProEt X).op.lan :
        (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤ X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) := by
    have : AB5OfSize.{u, u + 1} (ModuleCat.{u + 1} Λ) :=
      AB5OfSize_of_univLE (ModuleCat.{u + 1} Λ)
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u + 1}
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation _ J
    intro Y
    have : IsFiltered (CostructuredArrow (etaleToProEt X).op Y) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence (etaleToProEt X) (unop Y))
    exact preservesLimitsOfShape_of_natIso (etaleToProEtModuleLanEvaluationIso X Λ Y).symm
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- Inverse image of module sheaves from the small étale site to the small
pro-étale site preserves finite colimits. -/
instance etaleToProEtPullback_module_preservesFiniteColimits :
    PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)) := by
  have : PreservesColimitsOfSize.{0, 0}
      (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)) :=
    (etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- Direct image of module sheaves along the étale-to-pro-étale comparison is additive. -/
instance etaleToProEtSheaf_module_additive :
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ)).Additive := by
  have : (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)).Additive :=
    ExactFunctor.additive (ExactFunctor.of (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)))
  exact (etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ)).right_adjoint_additive

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

/-- Direct image of module sheaves admits a right-derived functor on the
bounded-below derived category. -/
instance etaleToProEtSheaf_module_hasRightDerivedFunctor :
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  exact Functor.HasRightDerivedFunctor.mk'
    (α := (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ)).rightDerivedFunctorPlusUnit)

/-- The bounded-below right-derived direct image of module sheaves. -/
def etaleToProEt_modulePlusPushforward :
    DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Adjunction.Derived.Plus.right (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ))

/-- The essential image of canonical inverse image on module sheaves. -/
abbrev etaleToProEtModuleEssImage :
    ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Functor.essImage (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))

/-- Restriction of right-derived direct image to bounded-below objects with
cohomology in the essential image of inverse image. -/
def etaleToProEt_modulePlusPushforwardRestrict :
    DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι ⋙
    etaleToProEt_modulePlusPushforward X Λ

/-- The canonical adjunction unit on étale module sheaves is invertible. -/
instance etaleToProEt_sheafAdjunction_module_unit_app_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ)).unit.app F) :=
  sorry

/-- The bounded-below derived action of canonical inverse image on module sheaves. -/
def etaleToProEt_modulePlusPullback :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Adjunction.Derived.Plus.left
    (ExactFunctor.of (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)))

/-- The canonical bounded-below derived adjunction between inverse image and
right-derived direct image on module sheaves. -/
def etaleToProEt_modulePlusAdjunction :
    etaleToProEt_modulePlusPullback X Λ ⊣ etaleToProEt_modulePlusPushforward X Λ :=
  Adjunction.Derived.Plus.adjunction
    (ExactFunctor.of (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)))
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ))
    (etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ))

/-- Every cohomology sheaf of derived inverse image belongs to the essential
image of inverse image on module sheaves. -/
theorem etaleToProEt_modulePlusPullback_mapsTo
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)
      ((etaleToProEt_modulePlusPullback X Λ).obj K) :=
  sorry

/-- Derived inverse image with codomain restricted to objects whose cohomology
sheaves belong to its underived essential image. -/
def etaleToProEt_modulePlusPullbackLift :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ) :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).lift
    (etaleToProEt_modulePlusPullback X Λ) (etaleToProEt_modulePlusPullback_mapsTo X Λ)

/-- Including the restricted derived inverse image recovers derived inverse image. -/
def etaleToProEt_modulePlusPullbackLift_compι :
    etaleToProEt_modulePlusPullbackLift X Λ ⋙
      (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι ≅
        etaleToProEt_modulePlusPullback X Λ :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).liftCompιIso
    (etaleToProEt_modulePlusPullback X Λ) (etaleToProEt_modulePlusPullback_mapsTo X Λ)

/-- The derived adjunction unit is invertible on every bounded-below étale
complex of module sheaves. -/
instance etaleToProEt_modulePlusAdjunction_unit_app_isIso
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((etaleToProEt_modulePlusAdjunction X Λ).unit.app K) :=
  sorry

/-- The essential image of inverse image on module sheaves is a weak Serre class. -/
instance etaleToProEtModuleEssImage_isWeakSerre :
    IsWeakSerreClass (etaleToProEtModuleEssImage X Λ) :=
  sorry

/-- The derived adjunction counit is invertible on bounded-below complexes whose
cohomology sheaves belong to the essential image of inverse image. -/
instance etaleToProEt_modulePlusAdjunction_counit_app_isIso
    (K : DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ)) :
    IsIso
      ((etaleToProEt_modulePlusAdjunction X Λ).counit.app
        ((DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι.obj K)) :=
  sorry

/-- Derived inverse image is an equivalence onto bounded-below complexes whose
cohomology sheaves belong to its underived essential image, with quasi-inverse
given by restricted right-derived direct image. -/
instance etaleToProEt_modulePlusPullbackLift_isEquivalence :
    Functor.IsEquivalence (etaleToProEt_modulePlusPullbackLift X Λ) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
