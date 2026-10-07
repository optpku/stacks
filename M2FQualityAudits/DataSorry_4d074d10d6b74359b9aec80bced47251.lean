module

import Lean

public import stacks_project.Chap50.Remark_50_4_2_DeRhamAlgebra
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal
open RingedSite.Hom
open RingedSite.Hom.ModuleSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Remark 50.4.2 (1): `Ωᵈᴿ[p]` is a sheaf of differential graded
`p⁻¹ᴼᵏ_S`-algebras. -/
@[stacks 0FU6] #check @AlgebraicGeometry.Scheme.DeRham.deRhamDGA

/-- Graded coefficient modules admit the tensor products used in Koszul totalization. -/
instance coefficientHasTensor {X S : Scheme.{u}} (p : X ⟶ S)
    (G₁ G₂ : GradedObject ℤ (coefficientModules p)) :
    GradedObject.HasTensor G₁ G₂ := sorry

/-- Left-associated triples of graded coefficient modules satisfy tensor coherence. -/
instance coefficientHasGoodTensor12 {X S : Scheme.{u}} (p : X ⟶ S)
    (G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p)) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ := sorry

/-- Right-associated triples of graded coefficient modules satisfy tensor coherence. -/
instance coefficientHasGoodTensor23 {X S : Scheme.{u}} (p : X ⟶ S)
    (G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p)) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ := sorry

/-- Fourfold graded coefficient-module tensors satisfy the required extensionality. -/
instance coefficientHasTensor4ObjExt {X S : Scheme.{u}} (p : X ⟶ S)
    (G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules p)) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ := sorry

variable {X Y S T : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
  (q : Y ⟶ T) (h : S ⟶ T) (sq : CommSq f p q h)

/-- The commutative square of sheafed spaces underlying a commutative square of schemes. -/
theorem sheafedSquare (sq : CommSq f p q h) :
    CommSq f.toLRSHom.toShHom p.toLRSHom.toShHom
      q.toLRSHom.toShHom h.toLRSHom.toShHom := sorry

variable [MonoidalCategory
  (ModuleDerived.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [Functor.LaxMonoidal
  (moduleLocalization.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [MonoidalCategory
  (ModuleDerived.{u, u, u, u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))]
variable [((RingedSpace.DeRham.baseChangeHom
  (sheafedSquare f p q h sq)).modulePushforward.{u}).IsRightAdjoint]
variable [h_derived : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u, u, u, u, u, u}
    (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))
  (ModuleQis.{u, u, u, u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{u, u, u, u, u, u}
    (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))
  (ModuleQis.{u, u, u, u} (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))]
variable [DerivedAdjunction.HasPair.{u}
  (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))]
variable [(modulePullbackDerived.{u, u, u, u, u, u}
  (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))).OplaxMonoidal]

/-- The canonical tensorator on derived direct image, transported across the derived
pullback--pushforward adjunction. -/
noncomputable def derivedPushforwardTensorator (A B :
    ModuleDerived.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) :
    (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj A ⊗
        (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj B ⟶
      (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (A ⊗ B) :=
  ((moduleDerivedAdjunction.{u}
    (RingedSpace.DeRham.baseChangeHom
      (sheafedSquare f p q h sq))).rightAdjointLaxMonoidal).μ A B

/-- The tensorator for restriction along the coefficient-ring map of the square. -/
noncomputable def globalSectionsRestrictionTensorator (A B : coefficientModules p) :
    (globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj A ⊗
        (globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj B ⟶
      (globalSectionsRestriction.{u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (A ⊗ B) :=
  ((ModuleCat.extendRestrictScalarsAdj
    (globalSectionsMap
      (RingedSpace.DeRham.baseChangeHom
        (sheafedSquare f p q h sq))).hom).rightAdjointLaxMonoidal).μ A B

/-- Remark 50.4.2 (2): for a commutative square of schemes, the differential graded
`p⁻¹ᴼᵏ_S`-algebra structure on `Ωᵈᴿ[p]` induces the canonical relative cup product on its
derived direct image in the derived category over `q⁻¹ᴼᵏ_T`. -/
@[stacks 0FU6]
noncomputable def cupProduct :
    (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj (derivedComplex p) ⊗
        (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj (derivedComplex p) ⟶
      (modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (derivedComplex p) :=
  derivedPushforwardTensorator f p q h sq (derivedComplex p) (derivedComplex p) ≫
    (modulePushforwardDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom
        (sheafedSquare f p q h sq))).map (derivedDeRhamMultiplication p)

/-- The relative de Rham cup product is the canonical derived-pushforward tensorator followed
by the image of the derived de Rham multiplication. -/
theorem cupProduct_eq :
    cupProduct f p q h sq =
      derivedPushforwardTensorator f p q h sq
          (derivedComplex p) (derivedComplex p) ≫
        (modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).map (derivedDeRhamMultiplication p) := sorry

/-- Remark 50.4.2 (3): the canonical relative cup product on the derived direct image of
`Ωᵈᴿ[p]` is associative. -/
@[stacks 0FU6]
theorem cupProduct_assoc :
    cupProduct f p q h sq ▷
          (modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).obj (derivedComplex p) ≫
        cupProduct f p q h sq =
      (α_ ((modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj (derivedComplex p))
        ((modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj (derivedComplex p))
        ((modulePushforwardDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).obj (derivedComplex p))).hom ≫
        (modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).obj (derivedComplex p) ◁
          cupProduct f p q h sq ≫
        cupProduct f p q h sq := sorry

/-- Derived global sections on `Y` of the relative de Rham direct image. -/
noncomputable abbrev pushedGlobalDerivedObject :=
  (moduleDerivedGlobalSections.{u}
    (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).obj
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (derivedComplex p))

/-- `pushedGlobalDerivedObject` is derived global sections of the canonical direct image. -/
theorem pushedGlobalDerivedObject_def :
    pushedGlobalDerivedObject f p q h sq =
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).obj
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).obj (derivedComplex p)) := sorry

variable [qDerivedMonoidal : MonoidalCategory (coefficientDerived q)]
variable [Functor.LaxMonoidal
  (moduleDerivedGlobalSections.{u}
    (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))]

/-- The multiplication on derived global sections induced by the relative cup product. -/
noncomputable def pushedGlobalMultiplication :
    pushedGlobalDerivedObject f p q h sq ⊗ pushedGlobalDerivedObject f p q h sq ⟶
      pushedGlobalDerivedObject f p q h sq :=
  Functor.LaxMonoidal.μ
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (derivedComplex p))
      ((modulePushforwardDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (derivedComplex p)) ≫
    (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).map
        (cupProduct f p q h sq)

/-- The pushed global multiplication is the global-sections tensorator followed by the image
of `cupProduct`. -/
theorem pushedGlobalMultiplication_eq :
    pushedGlobalMultiplication f p q h sq =
      Functor.LaxMonoidal.μ
          (moduleDerivedGlobalSections.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).obj (derivedComplex p))
          ((modulePushforwardDerived.{u, u, u, u, u, u}
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).obj (derivedComplex p)) ≫
        (moduleDerivedGlobalSections.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).map
            (cupProduct f p q h sq) := sorry

/-- Cohomology of derived global sections of the relative de Rham direct image. -/
noncomputable abbrev pushedCohomology (n : ℤ) :=
  (DerivedCategory.homologyFunctor (coefficientModules q) n).obj
    (pushedGlobalDerivedObject f p q h sq)

/-- `pushedCohomology` is homology of the pushed derived global-sections object. -/
theorem pushedCohomology_def (n : ℤ) :
    pushedCohomology f p q h sq n =
      (DerivedCategory.homologyFunctor (coefficientModules q) n).obj
        (pushedGlobalDerivedObject f p q h sq) := sorry

/-- The homotopy-level source of the derived global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonSource :
    ModuleHomotopy.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
    globalSectionsRestrictionDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))

/-- The homotopy-level target of the derived global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonTarget :
    ModuleHomotopy.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  (RingedSpace.DeRham.baseChangeHom
      (sheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ) ⋙
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
      (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))

/-- The derived target of the global-sections comparison for the given square. -/
noncomputable abbrev pushedComparisonTargetDerived :
    ModuleDerived.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⥤
      ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom) :=
  modulePushforwardDerived.{u, u, u, u, u, u}
      (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)) ⋙
    moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)

/-- The canonical right-derived unit for the source comparison functor. -/
noncomputable def pushedComparisonSourceUnit :
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
        (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))) ≫
    (Functor.associator
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))).hom

/-- The canonical right-derived unit for the target comparison functor. -/
noncomputable def pushedComparisonTargetUnit :
    pushedComparisonTarget f p q h sq ⟶
      moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom) ⋙
        pushedComparisonTargetDerived f p q h sq :=
  Functor.whiskerLeft
      ((RingedSpace.DeRham.baseChangeHom
        (sheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))) ≫
    (Functor.associator
      ((RingedSpace.DeRham.baseChangeHom
        (sheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{u, u, u, u, u, u}
          (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))
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
        (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom))).hom

/-- The homotopy-level natural isomorphism underlying the comparison for the given square. -/
noncomputable def pushedComparisonHomotopyIso :
    pushedComparisonSource f p q h sq ≅ pushedComparisonTarget f p q h sq :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing p)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq)))) ≪≫
    Functor.isoWhiskerLeft
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).mapDerivedCategoryFactorsh) ≪≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).mapHomotopyCategory (up ℤ))
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
              (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))))
        (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomotopyCategory
        (moduleGlobalSectionsPushforwardNatIso.{u}
          (RingedSpace.DeRham.baseChangeHom (sheafedSquare f p q h sq))) (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          ((RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq)).modulePushforward.{u} ⋙
            moduleGlobalSectionsFunctor.{u}
              (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)))
        (up ℤ)).symm
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)) ≪≫
    (Functor.associator
      ((RingedSpace.DeRham.baseChangeHom
        (sheafedSquare f p q h sq)).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{u} (coefficientRing q)) (up ℤ) ⥤
          ModuleSections.Derived.{u}
            (RingedSpace.DeRham.coefficientSite q.toLRSHom.toShHom)))

/-- The specialized source is a right-derived model of restricted global sections. -/
noncomputable instance pushedComparisonSource_isRightDerived :
    (pushedComparisonSourceDerived f p q h sq).IsRightDerivedFunctor
      (pushedComparisonSourceUnit f p q h sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

/-- The specialized target is a right-derived model of global sections after direct image. -/
noncomputable instance pushedComparisonTarget_isRightDerived :
    (pushedComparisonTargetDerived f p q h sq).IsRightDerivedFunctor
      (pushedComparisonTargetUnit f p q h sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) := sorry

/-- The canonical derived global-sections/direct-image comparison specialized to the square. -/
noncomputable def pushedDerivedGlobalSectionsIso :
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
theorem pushedDerivedGlobalSectionsIso_eq :
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
noncomputable def pushedCohomologyIso (n : ℤ) :
    pushedCohomology f p q h sq n ≅
      (globalSectionsRestriction.{u}
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).obj (cohomology p n) :=
  (DerivedCategory.homologyFunctor (coefficientModules q) n).mapIso
      ((pushedDerivedGlobalSectionsIso f p q h sq).app (derivedComplex p)).symm ≪≫
    ModuleCat.RestrictScalars.homologyIso
      (globalSectionsMap
        (RingedSpace.DeRham.baseChangeHom
          (sheafedSquare f p q h sq))).hom (globalDerivedObject p) n

/-- The pushed cohomology comparison is induced by the derived global-sections comparison and
exact restriction of scalars. -/
theorem pushedCohomologyIso_eq (n : ℤ) :
    pushedCohomologyIso f p q h sq n =
      (DerivedCategory.homologyFunctor (coefficientModules q) n).mapIso
          ((pushedDerivedGlobalSectionsIso f p q h sq).app (derivedComplex p)).symm ≪≫
        ModuleCat.RestrictScalars.homologyIso
          (globalSectionsMap
            (RingedSpace.DeRham.baseChangeHom
              (sheafedSquare f p q h sq))).hom (globalDerivedObject p) n := sorry

variable [qQhMonoidal : (DerivedCategory.Qh :
  HomotopyCategory (coefficientModules q) (up ℤ) ⥤ coefficientDerived q).Monoidal]

/-- The degreewise cohomology product induced by the relative cup product after derived global
sections on `Y`. -/
noncomputable def pushedCohomologyCupProduct
    (M : CoefficientTensorModel q) (i j : ℤ) :
    pushedCohomology f p q h sq i ⊗ pushedCohomology f p q h sq j ⟶
      pushedCohomology f p q h sq (i + j) :=
  @CategoryTheory.derivedCohomologyProduct (coefficientRing q)
      (coefficientGlobalSectionsCommRing q) qDerivedMonoidal qQhMonoidal M i j
      (pushedGlobalDerivedObject f p q h sq)
      (pushedGlobalDerivedObject f p q h sq) ≫
    (DerivedCategory.homologyFunctor (coefficientModules q) (i + j)).map
      ((M.tensorIsoObj
        (pushedGlobalDerivedObject f p q h sq)
        (pushedGlobalDerivedObject f p q h sq)).inv ≫
          pushedGlobalMultiplication f p q h sq)

/-- The pushed cohomology product is obtained from the canonical derived tensor comparison and
the multiplication induced by `cupProduct`. -/
theorem pushedCohomologyCupProduct_eq
    (M : CoefficientTensorModel q) (i j : ℤ) :
    pushedCohomologyCupProduct f p q h sq M i j =
      @CategoryTheory.derivedCohomologyProduct (coefficientRing q)
          (coefficientGlobalSectionsCommRing q) qDerivedMonoidal qQhMonoidal M i j
          (pushedGlobalDerivedObject f p q h sq)
          (pushedGlobalDerivedObject f p q h sq) ≫
        (DerivedCategory.homologyFunctor (coefficientModules q) (i + j)).map
          ((M.tensorIsoObj
            (pushedGlobalDerivedObject f p q h sq)
            (pushedGlobalDerivedObject f p q h sq)).inv ≫
              pushedGlobalMultiplication f p q h sq) := sorry

/-- Remark 50.4.2 (4): through the canonical derived-global-sections and exact
restriction-of-scalars comparisons, the product induced by `cupProduct` is the relative de Rham
cohomology cup product of Lemma 50.4.1. -/
@[stacks 0FU6]
theorem pushedCohomologyCupProduct_compatibility
    [pDerivedMonoidal : MonoidalCategory (coefficientDerived p)]
    [pQhMonoidal : (DerivedCategory.Qh :
      HomotopyCategory (coefficientModules p) (up ℤ) ⥤ coefficientDerived p).Monoidal]
    [(globalDerivedFunctor p).LaxMonoidal]
    (Mp : CoefficientTensorModel p) (Mq : CoefficientTensorModel q) (i j : ℤ) :
    pushedCohomologyCupProduct f p q h sq Mq i j ≫
        (pushedCohomologyIso f p q h sq (i + j)).hom =
      ((pushedCohomologyIso f p q h sq i).hom ⊗ₘ
          (pushedCohomologyIso f p q h sq j).hom) ≫
        globalSectionsRestrictionTensorator f p q h sq
          (cohomology p i) (cohomology p j) ≫
        (globalSectionsRestriction.{u}
          (RingedSpace.DeRham.baseChangeHom
            (sheafedSquare f p q h sq))).map
          (cohomologyCupProduct p Mp i j) := sorry

end AlgebraicGeometry.Scheme.DeRham


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
