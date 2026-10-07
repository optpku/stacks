module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernClass
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.Algebra.Homology.Embedding.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogarithmicForms

variable {X S : Scheme.{u}}

/-- The unbounded derived global-sections functor on additive sheaves is additive. -/
theorem derivedGlobalSections_additive (X : Scheme.{u}) :
    (Functor.RightDerived.Homotopy.functor
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).Additive := sorry

/-- Additive global sections have pointwise right-derived values at quasi-isomorphisms. -/
theorem derivedGlobalSections_hasPointwiseRightDerived (X : Scheme.{u}) :
    (Functor.Homotopy.toDerived
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (up ℤ)) := sorry

attribute [instance] derivedGlobalSections_additive derivedGlobalSections_hasPointwiseRightDerived

/-- Additive hypercohomology of the relative de Rham complex. -/
abbrev additiveCohomology (f : X ⟶ S) (degree : ℤ) : AddCommGrpCat.{u} :=
  Functor.RightDerived.Homotopy.cochainCohomology
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((additiveComplex f).extend embeddingUpNat) degree

/-- Logarithmic one-forms concentrated in degree one, extended to integer degrees. -/
abbrev singleLogarithmicComplex (f : X ⟶ S) :=
  ((HomologicalComplex.single _ (up ℕ) 1).obj
    (logarithmicForms f 1 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).extend
      embeddingUpNat

/-- The shifted single of logarithmic one-forms realizes the target of a first Ext class. -/
def singleLogarithmicShiftIso (f : X ⟶ S) :
    ((DerivedCategory.singleFunctor
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 0).obj
        (logarithmicForms f 1))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.Q.obj (singleLogarithmicComplex f))⟦(2 : ℤ)⟧ :=
  (shiftFunctor _ (1 : ℤ)).mapIso
      (((DerivedCategory.singleFunctors
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).shiftIso 1 0 1 rfl).app
          (logarithmicForms f 1)).symm ≪≫
    ((shiftFunctorAdd _ (1 : ℤ) (1 : ℤ)).app _).symm ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        (DerivedCategory.Q.mapIso
          (HomologicalComplex.extendSingleIso embeddingUpNat
            (logarithmicForms f 1 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            1 (1 : ℤ) rfl).symm)

/-- The distinguished degree-zero derived section of the constant integer sheaf. -/
def integerDerivedSection (X : Scheme.{u}) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Functor.RightDerived.Homotopy.functor
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology X)))) :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((Functor.Homotopy.singleIso
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 0).inv.app
        (CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology X)) ≫
      (Functor.RightDerived.Homotopy.unit
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).app
          ((HomotopyCategory.singleFunctor _ 0).obj
            (CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology X))))).hom
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{u} 0).inv.app
      ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology X)))).hom
          (Sheaf.constantIntegerSheafGlobalSection (Opens.grothendieckTopology X)))

/-- The Ext realization of first logarithmic cohomology in degree-two hypercohomology. -/
def singleCohomologyComparison (f : X ⟶ S) :
    AddCommGrpCat.of (H f 1 1) ⟶
      Functor.RightDerived.Homotopy.cochainCohomology
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (singleLogarithmicComplex f) 2 :=
  let sections := Functor.RightDerived.Homotopy.functor
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let target := DerivedCategory.Q.obj (singleLogarithmicComplex f)
  let shiftComparison := (sections.commShiftIso (2 : ℤ)).hom.app target
  let morphisms := (Preadditive.rightComp _ shiftComparison).comp
    (sections.mapAddHom.comp
      ((Preadditive.rightComp _ (singleLogarithmicShiftIso f).hom).comp
        Abelian.Ext.homAddEquiv.toAddMonoidHom))
  let evaluation := (AddMonoidHom.eval (integerDerivedSection X)).comp
    (AddCommGrpCat.homAddEquiv.toAddMonoidHom.comp
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapAddHom.comp morphisms))
  AddCommGrpCat.ofHom
    ((((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).shiftIso
      (2 : ℤ) 0 2 rfl).hom.app (sections.obj target)).hom.comp evaluation)

/-- First logarithmic sheaf cohomology agrees with the degree-two hypercohomology of its
single complex through the additive, pointwise-derived global-sections construction. -/
theorem singleCohomologyComparison_isIso (f : X ⟶ S) :
    IsIso (singleCohomologyComparison f) := sorry

-- Local instance justification (defeq pin): the comparison is built in the coefficient-module derived-category presentation used by de Rham cohomology.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

-- Local instance justification (defeq pin): the module-valued and additive global-sections models use their named canonical additive and total-derived structures.
attribute [local instance] moduleGlobalSectionsFunctor_additive
  moduleGlobalSectionsAdditiveFunctor_additive moduleGlobalSectionsToDerived_hasRightDerivedFunctor
  moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor

/-- Forgetting coefficients identifies the homotopy global-sections model with the derived
forgetful functor after module-valued global sections. -/
def moduleSectionsForgetIso (f : X ⟶ S) :
    moduleGlobalSectionsToDerived.{u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ≅
      moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⋙
        (forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}).mapDerivedCategory :=
  let site := RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom
  let forget := forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}
  -- Local instance justification (defeq pin): the homotopy composition comparison must use the named module global-sections additive structure at this coefficient site.
  letI : (moduleGlobalSectionsFunctor.{u} site).Additive :=
    moduleGlobalSectionsFunctor_additive site
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (eqToIso (moduleGlobalSectionsForget_eq site)).symm)
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (moduleGlobalSectionsFunctor.{u} site ⋙ forget)) (up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((moduleGlobalSectionsFunctor.{u} site).mapHomotopyCategory (up ℤ))
      forget.mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical comparison from derived additive sections to forgotten derived
coefficient-module sections, defined by the right-derived universal property. -/
def moduleSectionsForgetComparison (f : X ⟶ S) :
    ModuleSections.globalSourceDerived.{u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⟶
      moduleDerivedGlobalSections.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⋙
        (forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}).mapDerivedCategory :=
  let site := RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom
  let forget := forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}
  -- Local instance justification (defeq pin): the universal comparison uses the existing canonical right-derived source unit on this coefficient site.
  letI : (ModuleSections.globalSourceDerived.{u} site).IsRightDerivedFunctor
      (ModuleSections.globalSourceUnit.{u} site) (ModuleQis.{u} site) :=
    ModuleSections.globalSource_isRightDerived.{u} site
  (ModuleSections.globalSourceDerived.{u} site).rightDerivedDesc
    (ModuleSections.globalSourceUnit.{u} site) (ModuleQis.{u} site)
    (moduleDerivedGlobalSections.{u} site ⋙ forget.mapDerivedCategory)
    ((moduleSectionsForgetIso f).hom ≫
      Functor.whiskerRight
        (Functor.totalRightDerivedUnit (moduleGlobalSectionsToModuleDerived.{u} site)
          (moduleLocalization.{u} site) (ModuleQis.{u} site)) forget.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom)

/-- The comparison from additive de Rham hypercohomology to the underlying additive group
of coefficient-module de Rham cohomology. -/
def forgetCohomologyComparison (f : X ⟶ S) (degree : ℤ) :
    additiveCohomology f degree ⟶
      (forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}).obj
        (cohomology f degree) :=
  let site := RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom
  let forget := forget₂ (ModuleCat.{u} (coefficientRing f)) AddCommGrpCat.{u}
  let complex := (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat
  let derived := DerivedCategory.Q.obj complex
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} degree).map
    ((Functor.RightDerived.Homotopy.functor
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).map
      (DerivedCategory.Q.map
        (embeddingUpNat.mapAppIso (underlyingAbelianSheafFunctor.{u} site)
          (RingedSpace.DeRham.complex f.toLRSHom.toShHom)).inv ≫
        (underlyingAbelianSheafFunctor.{u} site).mapDerivedCategoryFactors.inv.app complex) ≫
      (ModuleSections.globalAppIso.{u} site derived).inv ≫
        (moduleSectionsForgetComparison f).app derived) ≫
    (Functor.MapDerivedCategory.homologyIso forget
      ((moduleDerivedGlobalSections.{u} site).obj derived) degree).hom

/-- Forgetting the coefficient-module structure does not change de Rham hypercohomology. -/
theorem forgetCohomologyComparison_isIso (f : X ⟶ S) (degree : ℤ) :
    IsIso (forgetCohomologyComparison f degree) := sorry

/-- The canonical realization of a logarithmic first-cohomology class through the actual
logarithmic-to-de Rham cochain map. -/
def canonicalToDeRhamCohomology (f : X ⟶ S) : H f 1 1 →+ cohomology f 2 :=
  (singleCohomologyComparison f ≫
    Functor.RightDerived.Homotopy.cochainCohomologyMap
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (HomologicalComplex.extendMap (toDeRham f 1) embeddingUpNat) 2 ≫
    forgetCohomologyComparison f 2).hom

/-- A supplied truncated logarithmic realization followed by the canonical Hodge map. -/
def toDeRhamCohomology (f : X ⟶ S) (comparison : ChernComparison f) :
    H f 1 1 →+ cohomology f 2 :=
  (hodgeMap f 1 2).hom.toAddMonoidHom.comp comparison.toTruncated

/-- The supplied realization is its truncated realization followed by the Hodge map. -/
theorem toDeRhamCohomology_def (f : X ⟶ S) (comparison : ChernComparison f) :
    toDeRhamCohomology f comparison =
      (hodgeMap f 1 2).hom.toAddMonoidHom.comp comparison.toTruncated := sorry

end AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
