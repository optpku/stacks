module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DifferentialGradedAlgebra
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open RingedSite.Hom
open RingedSite.Hom.ModuleSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.DerivedPushforward

variable {X Y S T : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
  (q : Y ⟶ T) (h : S ⟶ T) (sq : CommSq f p q h)

/-- The commutative square of coefficient sheafed spaces induced by a square of schemes. -/
noncomputable abbrev coefficientSheafedSquare :
    CommSq f.toLRSHom.toShHom p.toLRSHom.toShHom
      q.toLRSHom.toShHom h.toLRSHom.toShHom :=
  sq.map (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace)

variable [((RingedSpace.DeRham.baseChangeHom
  (coefficientSheafedSquare f p q h sq)).modulePushforward.{u}).IsRightAdjoint]
variable [h_derived : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u}
    (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
  (ModuleQis.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{u, u, u, u, u, u}
    (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
  (ModuleQis.{u, u, u, u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))]
variable [DerivedAdjunction.HasPair.{u}
  (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))]
variable [moduleDerivedMonoidalP : MonoidalCategory
  (ModuleDerived.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [moduleDerivedMonoidalQ : MonoidalCategory
  (ModuleDerived.{u, u, u, u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))]
variable [(modulePullbackDerived.{u, u, u, u, u, u}
  (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))).OplaxMonoidal]
variable [(moduleLocalization.{u, u, u, u}
    (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).LaxMonoidal]
variable [MonoidalCategory
  (HomotopyCategory
    (RingedSite.ModuleCat.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ))]
variable [MonoidalCategory
  (HomotopyCategory
    (RingedSite.ModuleCat.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) (up ℤ))]
variable [moduleDerivedQhMonoidalP : (DerivedCategory.Qh :
    HomotopyCategory
      (RingedSite.ModuleCat.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ) ⥤
      ModuleDerived.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Monoidal]
variable [moduleDerivedQhMonoidalQ : (DerivedCategory.Qh :
    HomotopyCategory
      (RingedSite.ModuleCat.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) (up ℤ) ⥤
      ModuleDerived.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Monoidal]
variable [(HomotopyCategory.quotient
    (RingedSite.ModuleCat.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) (up ℤ)).LaxMonoidal]

/-- The tensorator for restriction along the coefficient-ring map of the square. -/
noncomputable def globalSectionsRestrictionTensorator (A B : coefficientModules p) :
    CategoryTheory.MonoidalCategory.tensorObj (C := coefficientModules q)
        ((globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (coefficientSheafedSquare f p q h sq))).obj A)
        ((globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (coefficientSheafedSquare f p q h sq))).obj B) ⟶
      (globalSectionsRestriction.{u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj
        (CategoryTheory.MonoidalCategory.tensorObj (C := coefficientModules p) A B) :=
  ((ModuleCat.extendRestrictScalarsAdj
    (globalSectionsMap
      (RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq))).hom).rightAdjointLaxMonoidal).μ A B

/-- For a commutative square of schemes, wedge multiplication induces the canonical relative
cup product on the derived direct image of the relative de Rham complex. -/
noncomputable def cupProduct :
    (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) ⊗
      (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) ⟶
      (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) :=
  RingedSite.Hom.modulePushforwardDerived.cupProduct
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))
      (derivedComplex p) (derivedComplex p) ≫
    (modulePushforwardDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq))).map (derivedDeRhamMultiplication p)

/-- The relative de Rham cup product is the canonical derived-pushforward tensorator followed
by the image of the derived de Rham multiplication. -/
theorem cupProduct_eq :
    cupProduct f p q h sq =
      RingedSite.Hom.modulePushforwardDerived.cupProduct
          (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))
          (derivedComplex p) (derivedComplex p) ≫
        (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (coefficientSheafedSquare f p q h sq))).map (derivedDeRhamMultiplication p) := sorry

/-- The canonical relative cup product on the derived direct image of the relative de Rham
complex is associative. -/
theorem cupProduct_assoc :
    (cupProduct f p q h sq ▷
        (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p)) ≫
        cupProduct f p q h sq =
      (α_
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))).hom ≫
        ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p) ◁
          cupProduct f p q h sq) ≫
        cupProduct f p q h sq := sorry

/-- Derived global sections on `Y` of the relative de Rham direct image. -/
noncomputable abbrev pushedGlobalDerivedObject :=
  (moduleDerivedGlobalSections.{u}
    (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).obj
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))

/-- The multiplication on derived global sections induced by the relative cup product. -/
noncomputable def pushedGlobalMultiplication
    [MonoidalCategory (coefficientDerived q)]
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).LaxMonoidal] :
    pushedGlobalDerivedObject f p q h sq ⊗
      pushedGlobalDerivedObject f p q h sq ⟶
      pushedGlobalDerivedObject f p q h sq :=
  Functor.LaxMonoidal.μ
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p)) ≫
    (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).map
        (cupProduct f p q h sq)

/-- The pushed global multiplication is the global-sections tensorator followed by the image
of `cupProduct`. -/
theorem pushedGlobalMultiplication_eq
    [MonoidalCategory (coefficientDerived q)]
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).LaxMonoidal] :
    pushedGlobalMultiplication f p q h sq =
      Functor.LaxMonoidal.μ
          (moduleDerivedGlobalSections.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).obj (derivedComplex p)) ≫
        (moduleDerivedGlobalSections.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).map
            (cupProduct f p q h sq) := sorry

/-- Cohomology of derived global sections of the relative de Rham direct image. -/
noncomputable abbrev pushedCohomology (n : ℤ) :=
  (DerivedCategory.homologyFunctor (coefficientModules q) n).obj
    (pushedGlobalDerivedObject f p q h sq)

/-- The homotopy-level source of the derived global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonSource
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    ModuleHomotopy.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
    globalSectionsRestrictionDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))

/-- The homotopy-level target of the derived global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonTarget
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    ModuleHomotopy.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  (RingedSpace.DeRham.baseChangeHom
      (coefficientSheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ) ⋙
    moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)

/-- The derived source of the global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonSourceDerived :
    ModuleDerived.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
    globalSectionsRestrictionDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))

/-- The derived target of the global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonTargetDerived :
    ModuleDerived.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  modulePushforwardDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)) ⋙
    moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)

/-- The canonical right-derived unit for the source comparison functor. -/
noncomputable def pushedComparisonSourceUnit
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    pushedComparisonSource f p q h sq ⟶
      moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
        pushedComparisonSourceDerived f p q h sq :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))) ≫
    (Functor.associator
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))).hom

/-- The canonical right-derived unit for the target comparison functor. -/
noncomputable def pushedComparisonTargetUnit
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    pushedComparisonTarget f p q h sq ⟶
      moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
        pushedComparisonTargetDerived f p q h sq :=
  Functor.whiskerLeft
      ((RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))) ≫
    (Functor.associator
      ((RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≫
    (Functor.associator
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))).hom

/-- The homotopy-level natural isomorphism underlying the comparison for the given square. -/
noncomputable def pushedComparisonHomotopyIso
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    pushedComparisonSource f p q h sq ≅ pushedComparisonTarget f p q h sq :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing p)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq)))) ≪≫
    Functor.isoWhiskerLeft
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).mapDerivedCategoryFactorsh) ≪≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (moduleGlobalSectionsFunctor.{u}
              (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
            globalSectionsRestriction.{u, u, u, u, u, u}
              (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))))
        (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomotopyCategory
        (moduleGlobalSectionsPushforwardNatIso.{u}
          (RingedSpace.DeRham.baseChangeHom (coefficientSheafedSquare f p q h sq))) (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq)).modulePushforward.{u} ⋙
            moduleGlobalSectionsFunctor.{u}
              (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    (Functor.associator
      ((RingedSpace.DeRham.baseChangeHom
        (coefficientSheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)))

/-- The specialized source is a right-derived model of restricted global sections. -/
noncomputable instance pushedComparisonSource_isRightDerived
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    (pushedComparisonSourceDerived f p q h sq).IsRightDerivedFunctor
      (pushedComparisonSourceUnit f p q h sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

/-- The specialized target is a right-derived model of global sections after direct image. -/
noncomputable instance pushedComparisonTarget_isRightDerived
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    (pushedComparisonTargetDerived f p q h sq).IsRightDerivedFunctor
      (pushedComparisonTargetUnit f p q h sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

/-- The canonical derived global-sections/direct-image comparison specialized to the square. -/
noncomputable def pushedDerivedGlobalSectionsIso
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    pushedComparisonSourceDerived f p q h sq ≅
      pushedComparisonTargetDerived f p q h sq :=
  Functor.rightDerivedNatIso
    (pushedComparisonSourceDerived f p q h sq)
    (pushedComparisonTargetDerived f p q h sq)
    (pushedComparisonSourceUnit f p q h sq)
    (pushedComparisonTargetUnit f p q h sq)
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (pushedComparisonHomotopyIso f p q h sq)

/-- The derived global-sections comparison is the right-derived transport of the canonical
homotopy-level comparison. -/
theorem pushedDerivedGlobalSectionsIso_eq
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    :
    pushedDerivedGlobalSectionsIso f p q h sq =
      Functor.rightDerivedNatIso
        (pushedComparisonSourceDerived f p q h sq)
        (pushedComparisonTargetDerived f p q h sq)
        (pushedComparisonSourceUnit f p q h sq)
        (pushedComparisonTargetUnit f p q h sq)
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
        (pushedComparisonHomotopyIso f p q h sq) := sorry

/-- The canonical global-sections and exact restriction comparison between pushed cohomology
and relative de Rham cohomology with scalars restricted to `q⁻¹ᴼᵏ_T`. -/
noncomputable def pushedCohomologyIso
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    (n : ℤ) :
    pushedCohomology f p q h sq n ≅
      (globalSectionsRestriction.{u}
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).obj (cohomology p n) :=
  (DerivedCategory.homologyFunctor (coefficientModules q) n).mapIso
      ((pushedDerivedGlobalSectionsIso f p q h sq).app (derivedComplex p)).symm ≪≫
    ModuleCat.RestrictScalars.homologyIso
      (globalSectionsMap
        (RingedSpace.DeRham.baseChangeHom
          (coefficientSheafedSquare f p q h sq))).hom (globalDerivedObject p) n

/-- The pushed cohomology comparison is induced by the derived global-sections comparison and
exact restriction of scalars. -/
theorem pushedCohomologyIso_eq
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    (n : ℤ) :
    pushedCohomologyIso f p q h sq n =
      (DerivedCategory.homologyFunctor (coefficientModules q) n).mapIso
          ((pushedDerivedGlobalSectionsIso f p q h sq).app (derivedComplex p)).symm ≪≫
        ModuleCat.RestrictScalars.homologyIso
          (globalSectionsMap
            (RingedSpace.DeRham.baseChangeHom
              (coefficientSheafedSquare f p q h sq))).hom (globalDerivedObject p) n := sorry

/-- The degreewise cohomology product induced by the relative cup product after derived global
sections on `Y`. -/
noncomputable def pushedCohomologyCupProduct
    [MonoidalCategory (coefficientDerived q)]
    [∀ G₁ G₂ : GradedObject ℤ (coefficientModules q), GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    [HomotopyCategory.Koszul.TensorDescends (C := coefficientModules q)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules q) (up ℤ) ⥤
      coefficientDerived q).Monoidal]
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).LaxMonoidal]
    (i j : ℤ) :
    CategoryTheory.MonoidalCategory.tensorObj (C := coefficientModules q)
        ((DerivedCategory.homologyFunctor (coefficientModules q) i).obj
          (pushedGlobalDerivedObject f p q h sq))
        ((DerivedCategory.homologyFunctor (coefficientModules q) j).obj
          (pushedGlobalDerivedObject f p q h sq)) ⟶
      (DerivedCategory.homologyFunctor (coefficientModules q) (i + j)).obj
        (pushedGlobalDerivedObject f p q h sq) :=
  CategoryTheory.derivedCohomologyProductWith
      (hD := ModuleCat.hasDerivedCategory (coefficientRing q))
      (coefficientTensorModel q) i j
      (pushedGlobalDerivedObject f p q h sq)
      (pushedGlobalDerivedObject f p q h sq) ≫
    (DerivedCategory.homologyFunctor (coefficientModules q) (i + j)).map
      (((coefficientTensorModel q).tensorIsoObj
          (pushedGlobalDerivedObject f p q h sq)
          (pushedGlobalDerivedObject f p q h sq)).inv ≫
        pushedGlobalMultiplication f p q h sq)

/-- The pushed cohomology product is obtained from the canonical derived tensor comparison and
the multiplication induced by `cupProduct`. -/
theorem pushedCohomologyCupProduct_eq
    [MonoidalCategory (coefficientDerived q)]
    [∀ G₁ G₂ : GradedObject ℤ (coefficientModules q), GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    [HomotopyCategory.Koszul.TensorDescends (C := coefficientModules q)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules q) (up ℤ) ⥤
      coefficientDerived q).Monoidal]
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).LaxMonoidal]
    (i j : ℤ) :
    pushedCohomologyCupProduct f p q h sq i j =
      CategoryTheory.derivedCohomologyProductWith
          (hD := ModuleCat.hasDerivedCategory (coefficientRing q))
          (coefficientTensorModel q) i j
          (pushedGlobalDerivedObject f p q h sq)
          (pushedGlobalDerivedObject f p q h sq) ≫
        (DerivedCategory.homologyFunctor (coefficientModules q) (i + j)).map
          (((coefficientTensorModel q).tensorIsoObj
              (pushedGlobalDerivedObject f p q h sq)
              (pushedGlobalDerivedObject f p q h sq)).inv ≫
            pushedGlobalMultiplication f p q h sq) := sorry

/-- Through the canonical derived-global-sections and exact restriction-of-scalars comparisons,
the product induced by `cupProduct` is the relative de Rham cohomology cup product. -/
theorem pushedCohomologyCupProduct_compatibility
    [MonoidalCategory (coefficientDerived p)]
    [MonoidalCategory (coefficientDerived q)]
    [∀ G₁ G₂ : GradedObject ℤ (coefficientModules p), GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules p),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    [∀ G₁ G₂ : GradedObject ℤ (coefficientModules q), GradedObject.HasTensor G₁ G₂]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
    [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules q),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
    [HomotopyCategory.Koszul.TensorDescends (C := coefficientModules p)]
    [HomotopyCategory.Koszul.TensorDescends (C := coefficientModules q)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
      coefficientDerived p).Monoidal]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules q) (up ℤ) ⥤
      coefficientDerived q).Monoidal]
    [(moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).LaxMonoidal]
    [(globalDerivedFunctor p).LaxMonoidal]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).Additive]
    [(moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).Additive]
    (i j : ℤ) :
    pushedCohomologyCupProduct f p q h sq i j ≫
        (pushedCohomologyIso f p q h sq (i + j)).hom =
      (CategoryTheory.MonoidalCategory.tensorHom
          (pushedCohomologyIso f p q h sq i).hom
          (pushedCohomologyIso f p q h sq j).hom) ≫
        globalSectionsRestrictionTensorator f p q h sq
          (cohomology p i) (cohomology p j) ≫
        (globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (coefficientSheafedSquare f p q h sq))).map
          (cohomologyCupProduct p i j) := sorry

end AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
