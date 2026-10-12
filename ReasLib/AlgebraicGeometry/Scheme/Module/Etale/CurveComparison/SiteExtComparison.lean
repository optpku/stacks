/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.HomDerivedExt
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.MappedResolutionComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite ComplexShape
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualSiteExt
variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [Y.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- The actual underlying additive sheaf functor. -/
abbrev moduleForget := sheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Evaluation of additive sheaves on the identity étale object. -/
def abSections : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op (globalEtale Y))

/-- Additive sections preserve addition on maps. -/
instance abSections_additive : (abSections Y).Additive := sorry

/-- Module sections preserve addition on maps. -/
instance moduleSections_additive : (AmbientAssociatedSheaf.sections (X := Y) Λ).Additive := sorry

/-- Forgetting module structure is exact on sheaves; injective preservation is not asserted. -/
instance moduleForget_preservesFiniteLimits : PreservesFiniteLimits (moduleForget Y Λ) := sorry

/-- Forgetting module structure preserves finite colimits of sheaves. -/
instance moduleForget_preservesFiniteColimits : PreservesFiniteColimits (moduleForget Y Λ) := sorry

/-- The two underived sections routes have literally the same underlying section maps. -/
def forgetSectionsIso :
    AmbientAssociatedSheaf.sections (X := Y) Λ ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      moduleForget Y Λ ⋙ abSections Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The actual constant integer sheaf that corepresents global additive sections. -/
abbrev integerSheaf : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Hom from the integer sheaf is identified with sections by evaluation at one
through the constant-sheaf adjunction (expressed using the canonical H-zero equivalence). -/
def homSectionsIso : ActualHomDerivedExt.homFunctor (integerSheaf Y) ≅ abSections Y :=
  NatIso.ofComponents
    (fun F ↦ (Ext.addEquiv₀.symm.trans
      (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal @Etale Y))).toAddCommGrpIso)
    (fun _ ↦ sorry)

variable [EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- The normalized additive sections/Ext comparison uses actual derived Hom and resolution classes. -/
def abDerivedSectionsExtIso (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((abSections Y).rightDerived n).obj F ≅ (Sheaf.functorH Y.smallEtaleTopology n).obj F :=
  ((NatIso.rightDerived (homSectionsIso Y) n).app F).symm ≪≫
    ActualHomDerivedExt.rightDerivedIso (integerSheaf Y) (injectiveResolution F) n

/-- Forgetting module coefficients commutes with homology through its exact functor comparison. -/
def forgetHomologyIso (K : CochainComplex (ModuleCat.{u + 1} Λ) ℕ) (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (K.homology n) ≅
      (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex (up ℕ)).obj K).homology n :=
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
      ((HomologicalComplex.homologyFunctorIso _ (up ℕ) n).app K) ≪≫
    ((K.sc n).mapHomologyIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ (up ℕ) n).app
      (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex (up ℕ)).obj K)).symm

/-- The section-complex comparison applies the actual underived scalar-forgetting isomorphism termwise. -/
def sectionsComplexIso {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (I : InjectiveResolution F) :
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex (up ℕ)).obj
        (((AmbientAssociatedSheaf.sections (X := Y) Λ).mapHomologicalComplex (up ℕ)).obj I.cocomplex) ≅
      ((abSections Y).mapHomologicalComplex (up ℕ)).obj
        (ActualMappedResolution.complex (moduleForget Y Λ) I) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (forgetSectionsIso Y Λ).app (I.cocomplex.X n))
    (fun _ _ _ ↦ sorry)

/-- The actual map from derived module sections to derived additive sections:
compare the mapped source resolution to an additive injective resolution by injective lifts. -/
def derivedForgetMap (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((AmbientAssociatedSheaf.sections (X := Y) Λ).rightDerived n).obj F) ⟶
      ((abSections Y).rightDerived n).obj ((moduleForget Y Λ).obj F) :=
  let I := injectiveResolution F
  let J := injectiveResolution ((moduleForget Y Λ).obj F)
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      (I.isoRightDerivedObj (AmbientAssociatedSheaf.sections (X := Y) Λ) n).hom ≫
    (forgetHomologyIso Λ
      (((AmbientAssociatedSheaf.sections (X := Y) Λ).mapHomologicalComplex (up ℕ)).obj I.cocomplex) n).hom ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (up ℕ) n).map
      ((sectionsComplexIso Y Λ I).hom ≫
        ((abSections Y).mapHomologicalComplex (up ℕ)).map
          (ActualMappedResolution.map (moduleForget Y Λ) I J)) ≫
    (J.isoRightDerivedObj (abSections Y) n).inv

/-- Underlying additive sheaves of injective module sheaves are sections-acyclic.
Consequently the specified comparison, rather than an arbitrary iso, is invertible. -/
instance derivedForgetMap_isIso (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    IsIso (derivedForgetMap Y Λ F n) := sorry

/-- The actual derived module-sections/Ext map before repackaging its scalar compatibility. -/
def moduleToSiteAddMap (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :=
  derivedForgetMap Y Λ F n ≫ (abDerivedSectionsExtIso Y ((moduleForget Y Λ).obj F) n).hom

/-- Scalar endomorphisms commute with the specified resolution and Ext comparisons. -/
theorem moduleToSiteAddMap_smul (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (a : Λ) (x : ((AmbientAssociatedSheaf.sections (X := Y) Λ).rightDerived n).obj F) :
    ((moduleToSiteAddMap Y Λ F n).hom (a • x) : (siteModuleCohomologyModuleFunctor
        (J := Y.smallEtaleTopology) (A := Λ) n).obj F) =
      siteModuleCohomologySMul n F a ((moduleToSiteAddMap Y Λ F n).hom x) := sorry

/-- The canonical comparison to the exact existing site-Ext cohomology API. -/
def moduleToSiteMap (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    ((AmbientAssociatedSheaf.sections (X := Y) Λ).rightDerived n).obj F ⟶
      (siteModuleCohomologyModuleFunctor (J := Y.smallEtaleTopology) (A := Λ) n).obj F :=
  ModuleCat.ofHom
    { toFun := (moduleToSiteAddMap Y Λ F n).hom
      map_add' := (moduleToSiteAddMap Y Λ F n).hom.map_add
      map_smul' := moduleToSiteAddMap_smul Y Λ F n }

/-- The linear comparison is invertible because its specified underlying additive map is. -/
instance moduleToSiteMap_isIso (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    IsIso (moduleToSiteMap Y Λ F n) := sorry

/-- The actual module-valued derived-sections/site-Ext isomorphism. -/
def moduleToSiteIso (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :=
  @asIso _ _ _ _ (moduleToSiteMap Y Λ F n) (moduleToSiteMap_isIso Y Λ F n)

/-- The specified resolution/Ext comparison is natural in coefficient sheaf maps. -/
theorem moduleToSiteMap_naturality
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G) (n : ℕ) :
    ((AmbientAssociatedSheaf.sections (X := Y) Λ).rightDerived n).map f ≫ moduleToSiteMap Y Λ G n =
      moduleToSiteMap Y Λ F n ≫
        (siteModuleCohomologyModuleFunctor (J := Y.smallEtaleTopology) (A := Λ) n).map f := sorry

/-- The actual natural identification of derived module sections with the current site-Ext API. -/
def moduleToSiteNatIso (n : ℕ) :
    (AmbientAssociatedSheaf.sections (X := Y) Λ).rightDerived n ≅
      siteModuleCohomologyModuleFunctor (J := Y.smallEtaleTopology) (A := Λ) n :=
  NatIso.ofComponents (fun F ↦ moduleToSiteIso Y Λ F n) (fun f ↦ moduleToSiteMap_naturality Y Λ f n)

end ActualSiteExt
