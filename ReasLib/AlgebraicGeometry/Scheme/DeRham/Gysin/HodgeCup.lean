module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeCup
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Underlying
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.BoundedBelow
public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison

/-!
# Hodge Gysin maps and cup products

This module compares the coefficient-module presentation of Hodge cohomology with ordinary
sheaf cohomology, and records the identity of the ordinary Gysin image of a restricted class
with the Hodge cup product against the image of the unit class.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  ComplexShape TopologicalSpace Scheme.Hom
open Functor.RightDerived.Homotopy
open SheafOfModules.RingedSite.ExteriorPower

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

namespace Gysin

/-- Module-valued global sections on the coefficient site of a relative morphism. -/
noncomputable abbrev coefficientGlobalSections (f : X ⟶ S) :=
  RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)

/-- Additivity of coefficient-site module global sections. -/
theorem coefficientGlobalSections_additive (f : X ⟶ S) :
    (coefficientGlobalSections f).Additive :=
  RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)


/-- The nonnegative single-complex realization of a scheme module is canonically the
corresponding degree-zero object of the unbounded derived category. -/
noncomputable def moduleToDerivedIso (X : Scheme.{u}) (F : X.Modules) :
    (ModuleCech.moduleToDerived X).obj F ≅
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj
        ((Scheme.Modules.toRingedSpace X).obj F) :=
  DerivedCategory.Q.mapIso
    (((ComplexShape.embeddingUpNat.extendFunctor X.toRingedSpace.Modules).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.toRingedSpace X) (up ℕ) 0).app F)) ≪≫
      HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
        ((Scheme.Modules.toRingedSpace X).obj F) 0 0 rfl)

/-- A module sheaf regarded as a bounded-below cochain complex concentrated in degree zero. -/
noncomputable abbrev moduleSinglePlus (X : RingedSpace.{u}) (F : X.Modules) :=
  (CochainComplex.Plus.singleFunctor X.Modules 0).obj F

/-- The bounded-derived localization of a degree-zero module sheaf is the corresponding
degree-zero single object. -/
noncomputable def moduleSingleDerivedIso (X : RingedSpace.{u}) (F : X.Modules) :
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus X.Modules ⥤
      DerivedCategory.Plus X.Modules).obj
        ((HomotopyCategory.Plus.quotient X.Modules).obj (moduleSinglePlus X F)) ≅
      (DerivedCategory.Plus.singleFunctor X.Modules 0).obj F :=
  (DerivedCategory.Plus.Qh : HomotopyCategory.Plus X.Modules ⥤
    DerivedCategory.Plus X.Modules).mapIso
      ((CochainComplex.Plus.singleFunctorCompQuotientIso X.Modules 0).app F) ≪≫
    (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso X.Modules 0).app F

/-- Evaluation of module sheaves on the terminal open is additive. -/
theorem moduleSectionsAdditive (X : RingedSpace.{u}) :
    (SheafOfModules.evaluation X.ringCatSheaf
      (Opposite.op (⊤ : TopologicalSpace.Opens X.carrier))).Additive :=
  RingedSite.Hom.moduleSectionsEvaluation_additive
    (RingedSpace.opensRingedSite X) (⊤ : TopologicalSpace.Opens X.carrier)

/-- Forgetting a module sheaf to its underlying additive sheaf preserves injective objects. -/
theorem moduleUnderlyingPreservesInjectives (X : RingedSpace.{u}) :
    (RingedSite.Hom.underlyingAbelianSheafFunctor
      (RingedSpace.opensRingedSite X)).PreservesInjectiveObjects := sorry

/-- Forgetting modules over a ring preserves finite limits. -/
theorem moduleForgetPreservesFiniteLimits
    (R : Type u) [Ring R] :
    PreservesFiniteLimits (forget₂ (ModuleCat R) AddCommGrpCat) := sorry

/-- Forgetting modules over a ring preserves finite colimits. -/
theorem moduleForgetPreservesFiniteColimits
    (R : Type u) [Ring R] :
    PreservesFiniteColimits (forget₂ (ModuleCat R) AddCommGrpCat) := sorry


/-- Ordinary right-derived global sections of a module sheaf, with additivity supplied
explicitly. -/
noncomputable abbrev moduleSectionsRightDerived (X : RingedSpace.{u}) (q : ℕ) :
    X.Modules ⥤ ModuleCat (RingedSpace.globalSectionsRing X) :=
  @Functor.rightDerived _ _ _ _ _ _ _
    (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X) q

/-- Canonical bounded-below right derived functor of module-sections evaluation, with
additivity supplied explicitly. -/
noncomputable abbrev moduleSectionsBoundedDerived (X : RingedSpace.{u}) :=
  @Functor.RightDerived.Bounded.functor _ _ _ _ _ _ _ _
    (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
    (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
      inferInstance)

/-- Ordinary right-derived coefficient-module global sections, with additivity supplied
explicitly. -/
noncomputable abbrev coefficientRightDerived (f : X ⟶ S) (q : ℕ) :=
  @Functor.rightDerived _ _ _ _ _ _ _
    (coefficientGlobalSections f) (coefficientGlobalSections_additive f) q

/-- Canonical bounded-below right derived functor of coefficient global sections. -/
noncomputable abbrev coefficientBoundedDerived (f : X ⟶ S) :=
  @Functor.RightDerived.Bounded.functor _ _ _ _ _ _ _ _
    (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
    (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
      (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
      inferInstance)

/-- Unbounded total-derived global sections of a degree-zero module sheaf compute its ordinary
right-derived global sections. -/
noncomputable def moduleGlobalSingleCohomologyIso
    (X : RingedSpace.{u}) (F : X.Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor
      (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).obj
        ((RingedSpace.Module.Derived.GlobalSections.functor X).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      (moduleSectionsRightDerived X q).obj F :=
  (DerivedCategory.homologyFunctor
    (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).mapIso
      (@Functor.RightDerived.Homotopy.BoundedBelow.canonicalCochainValueIso _ _ _ _ _ _ _ _
        (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
        (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
          (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
          inferInstance)
        (RingedSite.Hom.moduleSectionsToDerived_hasRightDerivedFunctor
          (RingedSpace.opensRingedSite X) (⊤ : TopologicalSpace.Opens X.carrier))
        (moduleSinglePlus X F)).symm ≪≫
    (DerivedCategory.homologyFunctor
      (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).mapIso
      ((DerivedCategory.Plus.ι : DerivedCategory.Plus
        (ModuleCat (RingedSpace.globalSectionsRing X)) ⥤
          DerivedCategory (ModuleCat (RingedSpace.globalSectionsRing X))).mapIso
        ((moduleSectionsBoundedDerived X).mapIso
            (moduleSingleDerivedIso X F))) ≪≫
    @Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
      (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
        (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
        inferInstance)
      q F

/-- The exact functor forgetting a module over a ring to its additive group. -/
noncomputable def moduleForgetExact (R : Type u) [Ring R] :
    ModuleCat R ⥤ₑ AddCommGrpCat :=
  @ExactFunctor.of _ _ _ _ (forget₂ (ModuleCat R) AddCommGrpCat)
    (moduleForgetPreservesFiniteLimits R) (moduleForgetPreservesFiniteColimits R)

/-- The ordinary right-derived global-sections module has the canonical underlying additive
sheaf-cohomology object. -/
noncomputable def moduleCohomologyUnderlyingIso
    (X : RingedSpace.{u}) (F : X.Modules) (q : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X)) AddCommGrpCat).obj
        ((moduleSectionsRightDerived X q).obj F) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite X)).obj F) q) :=
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X)) AddCommGrpCat).mapIso
    (@Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
      (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
        (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
        inferInstance)
      q F).symm) ≪≫
  ((@Functor.RightDerived.Composition.BoundedBelow.ExactSecond.degreeIso
      _ _ _ _ _ _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsEvaluationFunctor X ⊤) (moduleSectionsAdditive X)
      (moduleForgetExact (RingedSpace.globalSectionsRing X))
      inferInstance inferInstance (q : ℤ)).app F) ≪≫
  (@Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
    (RingedSpace.moduleSectionsAsAbelianFunctor X ⊤)
    (RingedSpace.moduleSectionsAsAbelianFunctor_additive X ⊤)
    (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsAsAbelianFunctor X ⊤)
      (RingedSpace.moduleSectionsAsAbelianFunctor_additive X ⊤)
      inferInstance)
    q F) ≪≫
  ((@NatIso.rightDerived _ _ _ _ _ _ _
      (RingedSpace.moduleSectionsAsAbelianFunctor X ⊤)
      (RingedSpace.moduleSectionsEvaluationFunctor X ⊤ ⋙
        forget₂ (ModuleCat (RingedSpace.globalSectionsRing X)) AddCommGrpCat)
      (RingedSpace.moduleSectionsAsAbelianFunctor_additive X ⊤)
      { map_add :=
          ((congrArg (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X))
              AddCommGrpCat).map
            ((moduleSectionsAdditive X).map_add)).trans
            ((ExactFunctor.additive
              (moduleForgetExact (RingedSpace.globalSectionsRing X))).map_add)) }
      (RingedSite.Hom.ModuleSections.Underlying.sectionsForgetIso
        (RingedSpace.opensRingedSite X) ⊤) q).symm.app F) ≪≫
  ((@Functor.RightDerived.precompIso _ _ _ _ _ _ _ _ _
      (RingedSite.Hom.underlyingAbelianSheafFunctor (RingedSpace.opensRingedSite X))
      (siteAbelianSectionsFunctor (Opens.grothendieckTopology X.carrier) ⊤)
      (ExactFunctor.additive
        (RingedSite.Hom.underlyingAbelianSheafExactFunctor (RingedSpace.opensRingedSite X)))
      (siteAbelianSectionsFunctor_additive (Opens.grothendieckTopology X.carrier) ⊤)
      (moduleUnderlyingPreservesInjectives X) inferInstance inferInstance inferInstance
      q).app F) ≪≫
  ((SiteAbelianSectionsDerived.HPrime.rightDerivedSectionsIso
    (Opens.grothendieckTopology X.carrier) ⊤ q).symm.app
      ((RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.opensRingedSite X)).obj F)) ≪≫
  ((SiteAbelianSectionsDerived.HPrime.terminalIso
    (Opens.grothendieckTopology X.carrier) ⊤ isTerminalTop q).app
      ((RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.opensRingedSite X)).obj F))

/-- The global-derived realization of a module sheaf and its ordinary sheaf cohomology have
canonically isomorphic underlying additive groups. -/
noncomputable def derivedModelCohomologyIso
    (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj F))) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite X.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace X).obj F)) q) :=
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
    AddCommGrpCat).mapIso
      ((DerivedCategory.homologyFunctor
        (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q : ℤ)).mapIso
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).mapIso
            (moduleToDerivedIso X F)))) ≪≫
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
    AddCommGrpCat).mapIso (moduleGlobalSingleCohomologyIso X.toRingedSpace
      ((Scheme.Modules.toRingedSpace X).obj F) q)) ≪≫
  moduleCohomologyUnderlyingIso X.toRingedSpace
    ((Scheme.Modules.toRingedSpace X).obj F) q

/-- The coefficient ringed space underlying relative Hodge cohomology. -/
abbrev hodgeCoefficientSpace (f : X ⟶ S) : RingedSpace.{u} :=
  (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom).toRingedSpace

/-- A relative form viewed as a module over the inverse-image coefficient sheaf. -/
abbrev hodgeCoefficientForm (f : X ⟶ S) (p : ℕ) : (hodgeCoefficientSpace f).Modules :=
  (deRhamComplex f).X p

/-- A relative form over the coefficient sheaf, regarded as a bounded-below single complex. -/
noncomputable abbrev hodgeSinglePlus (f : X ⟶ S) (p : ℕ) :=
  (CochainComplex.Plus.singleFunctor
    (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) 0).obj
      (hodgeCoefficientForm f p)

/-- The bounded-derived single-complex model of a relative form is canonically its degree-zero
single object. -/
noncomputable def hodgeSingleDerivedIso (f : X ⟶ S) (p : ℕ) :
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus
      (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) ⥤
        DerivedCategory.Plus (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)).obj
      ((HomotopyCategory.Plus.quotient
        (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)).obj
          (hodgeSinglePlus f p)) ≅
      (DerivedCategory.Plus.singleFunctor
        (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) 0).obj
          (hodgeCoefficientForm f p) :=
  (DerivedCategory.Plus.Qh : HomotopyCategory.Plus
    (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) ⥤
      DerivedCategory.Plus
        (RingedSpace.DeRham.Modules f.toLRSHom.toShHom)).mapIso
    ((CochainComplex.Plus.singleFunctorCompQuotientIso
      (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) 0).app
        (hodgeCoefficientForm f p)) ≪≫
  (DerivedCategory.Plus.singleFunctor.fromHomotopy.iso
    (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) 0).app
      (hodgeCoefficientForm f p)

/-- The Hodge single-complex model is canonically the ordinary right-derived global-sections
model of the same coefficient module. -/
noncomputable def hodgeCohomologyRightDerivedIso (f : X ⟶ S) (p q : ℕ) :
    hodgeCohomologyObject f p (q : ℤ) ≅
      (coefficientRightDerived f q).obj
          (hodgeCoefficientForm f p) :=
  (DerivedCategory.homologyFunctor (coefficientModules f) (q : ℤ)).mapIso
      (@Functor.RightDerived.Homotopy.BoundedBelow.canonicalCochainValueIso _ _ _ _ _ _ _ _
        (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
        (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
          (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
          inferInstance)
        (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
        (hodgeSinglePlus f p)).symm ≪≫
    (DerivedCategory.homologyFunctor (coefficientModules f) (q : ℤ)).mapIso
      ((DerivedCategory.Plus.ι : DerivedCategory.Plus (coefficientModules f) ⥤
        DerivedCategory (coefficientModules f)).mapIso
          ((coefficientBoundedDerived f).mapIso
                (hodgeSingleDerivedIso f p))) ≪≫
    @Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
      (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
      (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
        (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
        inferInstance)
      q (hodgeCoefficientForm f p)

/-- Forgetting modules over the global coefficient ring is an exact functor to additive groups. -/
abbrev hodgeCoefficientForget (f : X ⟶ S) :
    coefficientModules f ⥤ₑ AddCommGrpCat :=
  moduleForgetExact (coefficientRing f)

/-- The composite of coefficient global sections with the exact forgetful functor is additive. -/
theorem coefficientGlobalSections_compForget_additive (f : X ⟶ S) :
    (coefficientGlobalSections f ⋙ (hodgeCoefficientForget f).obj).Additive where
  map_add {X Y} {g h} :=
    ((congrArg ((hodgeCoefficientForget f).obj.map)
        ((coefficientGlobalSections_additive f).map_add (f := g) (g := h))).trans
      ((ExactFunctor.additive (hodgeCoefficientForget f)).map_add))

/-- The composite of coefficient global sections with `forget₂` to additive groups is additive. -/
theorem coefficientGlobalSections_compForget₂_additive (f : X ⟶ S) :
    (coefficientGlobalSections f ⋙ forget₂ (coefficientModules f) AddCommGrpCat).Additive where
  map_add {X Y} {g h} :=
    ((congrArg (forget₂ (coefficientModules f) AddCommGrpCat).map
        ((coefficientGlobalSections_additive f).map_add (f := g) (g := h))).trans
      ((ExactFunctor.additive (moduleForgetExact (coefficientRing f))).map_add))

/-- Evaluation of coefficient-module sheaves on the terminal open is additive. -/
theorem hodgeCoefficientSectionsAdditive (f : X ⟶ S) :
    (SheafOfModules.evaluation
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).structureSheaf
      (Opposite.op (⊤ : TopologicalSpace.Opens X))).Additive :=
  RingedSite.Hom.moduleSectionsEvaluation_additive
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)
    (⊤ : TopologicalSpace.Opens X)

/-- Forgetting a coefficient-module sheaf to its underlying additive sheaf preserves
injective objects. -/
theorem hodgeUnderlyingPreservesInjectives (f : X ⟶ S) :
    (RingedSite.Hom.underlyingAbelianSheafFunctor
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).PreservesInjectiveObjects := sorry

/-- The underlying additive group of coefficient-module global sections is canonically the
global sections of the underlying additive sheaf. -/
noncomputable def hodgeGlobalSectionsForgetAppIso (f : X ⟶ S)
    (M : (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).ModuleCat) :
    (forget₂ (coefficientModules f) AddCommGrpCat).obj
        ((coefficientGlobalSections f).obj M) ≅
      (Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
        AddCommGrpCat).obj
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).obj M) :=
  preservesLimitIso (forget₂ (coefficientModules f) AddCommGrpCat)
      (RingedSite.Hom.moduleGlobalSectionsDiagram
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) M) ≪≫
    ((Sheaf.ΓNatIsoLim
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
      AddCommGrpCat).app
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).obj M)).symm

/-- The coefficient global-sections comparison is natural in the module sheaf. -/
theorem hodgeGlobalSectionsForgetAppIso_naturality (f : X ⟶ S)
    {M N : (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).ModuleCat}
    (g : M ⟶ N) :
    (forget₂ (coefficientModules f) AddCommGrpCat).map
          ((coefficientGlobalSections f).map g) ≫
        (hodgeGlobalSectionsForgetAppIso f N).hom =
      (hodgeGlobalSectionsForgetAppIso f M).hom ≫
        (Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
          AddCommGrpCat).map
          ((RingedSite.Hom.underlyingAbelianSheafFunctor
            (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).map g) := sorry

/-- The canonical natural comparison between coefficient-module and additive global sections. -/
noncomputable def hodgeGlobalSectionsForgetIso (f : X ⟶ S) :
    coefficientGlobalSections f ⋙
        forget₂ (coefficientModules f) AddCommGrpCat ≅
      RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⋙
        Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
          AddCommGrpCat :=
  NatIso.ofComponents (hodgeGlobalSectionsForgetAppIso f)
    (fun g ↦ hodgeGlobalSectionsForgetAppIso_naturality f g)

/-- The right-derived additive global-sections functor on the coefficient site computes
ordinary sheaf cohomology. -/
noncomputable def hodgeGlobalCohomologyIso (f : X ⟶ S) (q : ℕ) :
    (Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
      AddCommGrpCat).rightDerived q ≅
      Sheaf.functorH
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology q :=
  NatIso.rightDerived
      (Sheaf.ΓNatIsoSheafSectionsOfTerminal
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
        AddCommGrpCat (isTerminalTop : IsTerminal (⊤ : TopologicalSpace.Opens X))) q ≪≫
    (SiteAbelianSectionsDerived.HPrime.rightDerivedSectionsIso
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
      (⊤ : TopologicalSpace.Opens X) q).symm ≪≫
    SiteAbelianSectionsDerived.HPrime.terminalIso
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
      (⊤ : TopologicalSpace.Opens X) isTerminalTop q

/-- The underlying additive group of a Hodge cohomology object is ordinary cohomology of the
underlying relative-form sheaf. -/
noncomputable def hodgeCohomologyUnderlyingIso (f : X ⟶ S) (p q : ℕ) :
    (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f p (q : ℤ)) ≅
      AddCommGrpCat.of (Sheaf.H.{u} (additiveTerm f p) q) :=
  ((forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).mapIso
    (hodgeCohomologyRightDerivedIso f p q)) ≪≫
  ((forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).mapIso
    (@Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
      (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
      (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
        (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
        inferInstance)
      q (hodgeCoefficientForm f p)).symm) ≪≫
  ((@Functor.RightDerived.Composition.BoundedBelow.ExactSecond.degreeIso
      _ _ _ _ _ _ _ _ _ _ _ _
      (coefficientGlobalSections f) (coefficientGlobalSections_additive f)
      (hodgeCoefficientForget f) inferInstance inferInstance (q : ℤ)).app
    (hodgeCoefficientForm f p)) ≪≫
  (@Functor.RightDerived.Bounded.degree.degreeIsoRightDerived _ _ _ _ _ _ _ _ _
    (coefficientGlobalSections f ⋙ (hodgeCoefficientForget f).obj)
    (coefficientGlobalSections_compForget_additive f)
    (@Functor.RightDerived.Bounded.hasDerived _ _ _ _ _ _ _
      (coefficientGlobalSections f ⋙ (hodgeCoefficientForget f).obj)
      (coefficientGlobalSections_compForget_additive f)
      inferInstance)
    q (hodgeCoefficientForm f p)) ≪≫
  ((@NatIso.rightDerived _ _ _ _ _ _ _
      (coefficientGlobalSections f ⋙ forget₂ (coefficientModules f) AddCommGrpCat)
      (RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⋙
        Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
          AddCommGrpCat)
      (coefficientGlobalSections_compForget₂_additive f)
      { map_add :=
          ((congrArg
              (Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
                AddCommGrpCat).map
              ((ExactFunctor.additive
                (RingedSite.Hom.underlyingAbelianSheafExactFunctor
                  (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))).map_add)).trans
            ((Sheaf.globalSections_additive
              (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology).map_add)) }
      (hodgeGlobalSectionsForgetIso f) q).app
    (hodgeCoefficientForm f p)) ≪≫
  ((@Functor.RightDerived.precompIso _ _ _ _ _ _ _ _ _
      (RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (Sheaf.Γ (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom).siteTopology
        AddCommGrpCat)
      (ExactFunctor.additive
        (RingedSite.Hom.underlyingAbelianSheafExactFunctor
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
      inferInstance
      (hodgeUnderlyingPreservesInjectives f) inferInstance inferInstance inferInstance
      q).app (hodgeCoefficientForm f p)) ≪≫
  ((hodgeGlobalCohomologyIso f q).app
    ((RingedSite.Hom.underlyingAbelianSheafFunctor
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).obj
        (hodgeCoefficientForm f p)))

/-- Restricting the scalar action on a relative form leaves its underlying additive sheaf
unchanged. -/
noncomputable def hodgeFormUnderlyingIso (f : X ⟶ S) (p : ℕ) :
    (RingedSite.Hom.underlyingAbelianSheafFunctor
      (RingedSpace.opensRingedSite X.toRingedSpace)).obj
        (RingedSpace.DeRham.form f.toLRSHom.toShHom p) ≅
      additiveTerm f p :=
  Iso.refl _

/-- Cohomology of the coefficient-module form and of its exterior-power presentation are
canonically isomorphic as additive groups. -/
noncomputable def hodgeFormCohomologyIso (f : X ⟶ S) (p q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} (additiveTerm f p) q) ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite X.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace X).obj
              ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p)))) q) :=
  ((Sheaf.functorH (Opens.grothendieckTopology X.carrier) q).mapIso
    (hodgeFormUnderlyingIso f p).symm) ≪≫
  ((Sheaf.functorH (Opens.grothendieckTopology X.carrier) q).mapIso
    ((RingedSite.Hom.underlyingAbelianSheafFunctor
      (RingedSpace.opensRingedSite X.toRingedSpace)).mapIso
        (@asIso _ _ _ _ (formToExterior f p) (formToExteriorIsIso f p))))

/-- The canonical comparison from the exterior-form global-derived presentation used by the
Gysin map to the coefficient-module Hodge cohomology object. -/
noncomputable def hodgeModelIso (f : X ⟶ S) (p q : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) (q : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p))))) ≅
      (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f p (q : ℤ)) :=
  derivedModelCohomologyIso X
      ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p)) q ≪≫
    (hodgeFormCohomologyIso f p q).symm ≪≫
    (hodgeCohomologyUnderlyingIso f p q).symm

/-- The forward comparison `hodgeModelIso` is the composite through ordinary cohomology of the
exterior-form sheaf. -/
theorem hodgeModelIso_hom (f : X ⟶ S) (p q : ℕ) :
    (hodgeModelIso f p q).hom =
      (derivedModelCohomologyIso X
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p)) q).hom ≫
      (hodgeFormCohomologyIso f p q).inv ≫
      (hodgeCohomologyUnderlyingIso f p q).inv := sorry

/-- Cohomology on the terminal open is canonically global sheaf cohomology. -/
noncomputable def moduleCohomologyTerminalIso
    (X : RingedSpace.{u}) (F : X.Modules) (q : ℕ) :
    RingedSpace.moduleCohomology F q ≅
      AddCommGrpCat.of (Sheaf.H.{u}
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite X)).obj F) q) :=
  (eqToIso (Sheaf.cohomologyAtObjectFunctor_obj
    (Opens.grothendieckTopology X.carrier) ⊤ q
      ((RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.opensRingedSite X)).obj F))).symm ≪≫
  ((SiteAbelianSectionsDerived.HPrime.terminalIso
    (Opens.grothendieckTopology X.carrier) ⊤ isTerminalTop q).app
      ((RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.opensRingedSite X)).obj F))

/-- Hodge cohomology is canonically ordinary cohomology of the exterior-power relative-form
sheaf, after forgetting scalar actions. -/
noncomputable def hodgeOrdinaryCohomologyIso (f : X ⟶ S) (p q : ℕ) :
    (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f p (q : ℤ)) ≅
      RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p))) q :=
  hodgeCohomologyUnderlyingIso f p q ≪≫
    hodgeFormCohomologyIso f p q ≪≫
    (moduleCohomologyTerminalIso X.toRingedSpace
      ((Scheme.Modules.toRingedSpace X).obj
        ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f p))) q).symm

/-- Shifting a single sheaf from degree zero to degree `c` shifts derived global cohomology
from degree `q` to degree `q + c`. -/
noncomputable def shiftedSingleCohomologyIso
    (X : RingedSpace.{u}) (F : X.Modules) (c q : ℕ) :
    (DerivedCategory.homologyFunctor
      (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).obj
        ((RingedSpace.Module.Derived.GlobalSections.functor X).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      (DerivedCategory.homologyFunctor
        (ModuleCat (RingedSpace.globalSectionsRing X)) (q + c : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X).obj
            ((DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj F)) :=
  (DerivedCategory.homologyFunctor
    (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).mapIso
      ((RingedSpace.Module.Derived.GlobalSections.functor X).mapIso
        (((DerivedCategory.singleFunctors X.Modules).shiftIso
          (c : ℤ) 0 (c : ℤ) (Int.add_zero (c : ℤ))).symm.app F)) ≪≫
  (DerivedCategory.homologyFunctor
    (ModuleCat (RingedSpace.globalSectionsRing X)) (q : ℤ)).mapIso
      ((RingedSpace.Module.Derived.GlobalSections.functor X).commShiftIso
        (c : ℤ) |>.app
          ((DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj F)) ≪≫
  ((DerivedCategory.homologyFunctor
    (ModuleCat (RingedSpace.globalSectionsRing X)) 0).shiftIso
      (c : ℤ) (q : ℤ) (q + c : ℕ)
      ((Nat.cast_add c q).symm.trans
        (congrArg (fun n : ℕ ↦ (n : ℤ)) (Nat.add_comm c q)))).app
          ((RingedSpace.Module.Derived.GlobalSections.functor X).obj
            ((DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj F))

/-- The shifted source presentation of the Hodge Gysin map computes ordinary cohomology of the
pushforward relative-form sheaf. -/
noncomputable def hodgeRestrictionSourceIso
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (p q c : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))))) ≅
      RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q :=
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
    AddCommGrpCat).mapIso
      ((DerivedCategory.homologyFunctor
        (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
          (q + c : ℤ)).mapIso
        (((RingedSpace.Module.Derived.GlobalSections.pushforwardIso i.toShHom).app
          ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))) ≪≫
        ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).mapIso
          (pushforwardSingleIso i (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p) (c : ℤ)))))) ≪≫
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
    AddCommGrpCat).mapIso
      (shiftedSingleCohomologyIso X.toRingedSpace
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) c q).symm) ≪≫
  ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
    AddCommGrpCat).mapIso
      (moduleGlobalSingleCohomologyIso X.toRingedSpace
        ((Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q)) ≪≫
  moduleCohomologyUnderlyingIso X.toRingedSpace
      ((Scheme.Modules.toRingedSpace X).obj
        ((Scheme.Modules.pushforward i).obj
          (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q ≪≫
  (moduleCohomologyTerminalIso X.toRingedSpace
    ((Scheme.Modules.toRingedSpace X).obj
      ((Scheme.Modules.pushforward i).obj
        (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q).symm

/-- The canonical restriction of an ambient Hodge class to the shifted source presentation of
the ordinary-cohomology Gysin map. -/
noncomputable def hodgeRestriction
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p q : ℕ) :
    (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f p (q : ℤ)) ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))))) :=
  (hodgeOrdinaryCohomologyIso f p q).hom ≫
    restriction i f p q ≫
    (hodgeRestrictionSourceIso i f p q c).inv

/-- The map `hodgeRestriction` is ordinary restriction transported through the canonical Hodge
and shifted-source comparisons. -/
theorem hodgeRestriction_spec
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (c p q : ℕ) :
    hodgeRestriction i f c p q =
      (hodgeOrdinaryCohomologyIso f p q).hom ≫
        restriction i f p q ≫
        (hodgeRestrictionSourceIso i f p q c).inv := sorry

/-- The ordinary Hodge Gysin map after canonical restriction to the closed subscheme. -/
noncomputable def hodgeGysinAfterRestriction
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (α : hodgeCohomologyObject f p (q : ℤ)) :
    hodgeCohomologyObject f (p + c) ((q + c : ℕ) : ℤ) :=
  (hodgeRestriction i f c p q ≫
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).map (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c) ≫
    (hodgeModelIso f (p + c) (q + c)).hom) α

/-- The map `hodgeGysinAfterRestriction` is restriction, followed by the ordinary Hodge Gysin
map and the canonical comparison back to the Hodge model. -/
theorem hodgeGysinAfterRestriction_spec
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (α : hodgeCohomologyObject f p (q : ℤ)) :
    hodgeGysinAfterRestriction i f c p q α =
      (hodgeRestriction i f c p q ≫
        (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
          AddCommGrpCat).map (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c) ≫
        (hodgeModelIso f (p + c) (q + c)).hom) α := sorry

/-- The canonical unit in degree-zero Hodge cohomology. -/
noncomputable def hodgeOne (f : X ⟶ S) : hodgeCohomologyObject f 0 0 :=
  (hodgeOrdinaryCohomologyIso f 0 0).inv
    (relativeFormZeroOneCohomology f)

/-- The Hodge unit is the ordinary constant-one class transported through the canonical model
comparison. -/
theorem hodgeOne_spec (f : X ⟶ S) :
    (hodgeOrdinaryCohomologyIso f 0 0).hom (hodgeOne f) =
      relativeFormZeroOneCohomology f := sorry

/-- The ordinary Hodge fundamental class `γ^{0,0}(1)`. -/
noncomputable def hodgeFundamentalClassOne
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    hodgeCohomologyObject f c (c : ℤ) :=
  (eqToHom (congrArg (fun n : ℕ ↦ hodgeCohomologyObject f n (n : ℤ))
    (Nat.zero_add c))).hom
      (hodgeGysinAfterRestriction i f c 0 0 (hodgeOne f))

/-- The Hodge fundamental class is the ordinary Gysin image `γ^{0,0}(1)`. -/
theorem hodgeFundamentalClassOne_spec
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    hodgeFundamentalClassOne i f c =
      (eqToHom (congrArg (fun n : ℕ ↦ hodgeCohomologyObject f n (n : ℤ))
        (Nat.zero_add c))).hom
          (hodgeGysinAfterRestriction i f c 0 0 (hodgeOne f)) := sorry

/-- Point-free compatibility of the ordinary Hodge Gysin map after restriction with cup
product by the fundamental class. -/
theorem hodgeGysinAfterRestriction_eq_hodgeCup
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [derivedMonoidal : CategoryTheory.MonoidalCategory (coefficientDerived f)]
    [qhMonoidal : _root_.AlgebraicGeometry.Scheme.DeRham.CoefficientQhMonoidal f]
    [globalLaxMonoidal : (globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f) :
    (fun α ↦ hodgeGysinAfterRestriction i f c p q α) =
      fun α ↦
        Scheme.DeRham.hodgeCup f T α
          (hodgeFundamentalClassOne i f c) := sorry


/-- After restriction to a Koszul-regular closed immersion, the ordinary Hodge Gysin image of a
class equals the Hodge cup product of that class with the Gysin image of the unit. -/
theorem hodgeCohomologyMap_restriction
    {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    [derivedMonoidal : CategoryTheory.MonoidalCategory (coefficientDerived f)]
    [qhMonoidal : _root_.AlgebraicGeometry.Scheme.DeRham.CoefficientQhMonoidal f]
    [globalLaxMonoidal : (globalDerivedFunctor f).LaxMonoidal]
    (T : CoefficientTensorModel f)
    (α : hodgeCohomologyObject f p (q : ℤ)) :
    hodgeGysinAfterRestriction i f c p q α =
      Scheme.DeRham.hodgeCup f T α
        (hodgeFundamentalClassOne i f c) := sorry

end Gysin

end AlgebraicGeometry.Scheme.DeRham

end
