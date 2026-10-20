/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek

/-!
# Derived module lower shriek along lisse-étale and flat-fppf inclusions

Geometric specializations of derived module lower shriek along the fully
faithful inclusions of Lemma 103.14.4. Because the ReasLib
`moduleLowerShriek.derived` leaf currently fails to synthesize
`HasDerivedCategory` on ring-sheaf presentations, inverse image is
`exactFunctor.mapDerivedCategory` and lower shriek is `totalLeftDerived` of
the underived homotopy presentation at coefficient universe `z`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open ComplexShape
open RingedSite.Cocontinuous

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The standard derived-category structure on modules over a ring-sheaf
presentation of an algebraic-stack site. -/
instance instHasDerivedCategory_moduleCat_ofRingSheaf
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (O : Sheaf J RingCat.{u})
    [UnivLE.{u + 1, z}] :
    HasDerivedCategory.{max (u + 1) (z + 1)}
      (RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J O)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory (RingedSite.ofRingSheaf J O)

/-- Coefficient-`z` module inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImageCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (etaleStructureSheaf X) ⥤
      SheafOfModules.{z} (lisseEtaleStructureSheaf X) :=
  moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
    (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Coefficient-`z` module lower shriek along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleLowerShriekCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (lisseEtaleStructureSheaf X) ⥤
      SheafOfModules.{z} (etaleStructureSheaf X) :=
  moduleLowerShriek (J := lisseEtaleTopology X) (K := X.etaleTopology)
    (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Coefficient-`z` module inverse image along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImageCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (structureSheaf X) ⥤
      SheafOfModules.{z} (flatFppfStructureSheaf X) :=
  moduleInverseImage (J := flatFppfTopology X) (K := inheritedFppfTopology X)
    (flatFppfInclusion X) (structureSheaf X)

/-- Coefficient-`z` module lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfModuleLowerShriekCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (flatFppfStructureSheaf X) ⥤
      SheafOfModules.{z} (structureSheaf X) :=
  moduleLowerShriek (J := flatFppfTopology X) (K := inheritedFppfTopology X)
    (flatFppfInclusion X) (structureSheaf X)

/-- Coefficient-`z` lisse-étale module lower shriek is additive. -/
instance lisseEtaleModuleLowerShriekCoeff.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleLowerShriekCoeff X).Additive :=
  moduleLowerShriek.additive (J := lisseEtaleTopology X)
    (K := X.etaleTopology) (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Coefficient-`z` lisse-étale module inverse image is additive. -/
instance lisseEtaleModuleInverseImageCoeff.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleModuleInverseImageCoeff X).Additive := sorry

/-- Coefficient-`z` flat-fppf module lower shriek is additive. -/
instance flatFppfModuleLowerShriekCoeff.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleLowerShriekCoeff X).Additive :=
  moduleLowerShriek.additive (J := flatFppfTopology X)
    (K := inheritedFppfTopology X) (flatFppfInclusion X) (structureSheaf X)

/-- Coefficient-`z` flat-fppf module inverse image is additive. -/
instance flatFppfModuleInverseImageCoeff.additive (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfModuleInverseImageCoeff X).Additive := sorry

/-- Bundled exact coefficient-`z` module inverse image along the lisse-étale
inclusion. -/
abbrev lisseEtaleModuleInverseImageExact (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤ₑ
      RingedSite.ModuleCat.{z} (lisseEtaleRingedSite X) :=
  moduleInverseImage.exactFunctor (J := lisseEtaleTopology X)
    (K := X.etaleTopology) (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Homotopy-to-derived presentation of lisse-étale module inverse image. -/
abbrev lisseEtaleModuleInverseImageToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤
      RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X) :=
  (lisseEtaleModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (lisseEtaleRingedSite X)

/-- Homotopy-to-derived presentation of lisse-étale module lower shriek. -/
abbrev lisseEtaleModuleLowerShriekToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (lisseEtaleRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) :=
  (lisseEtaleModuleLowerShriekCoeff X).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))

/-- The homotopy-to-derived lisse-étale module inverse image has a total
right-derived functor. -/
instance lisseEtaleModuleInverseImageToDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasRightDerivedFunctor (lisseEtaleModuleInverseImageToDerived X)
      (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) := sorry

/-- The homotopy-to-derived lisse-étale module lower shriek has a total
left-derived functor. -/
instance lisseEtaleModuleLowerShriekToDerived.hasLeftDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasLeftDerivedFunctor (lisseEtaleModuleLowerShriekToDerived X)
      (RingedSite.Hom.ModuleQis.{z} (lisseEtaleRingedSite X)) := sorry

/-- Derived module inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤
      RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X) :=
  ExactFunctor.mapDerivedCategory (lisseEtaleModuleInverseImageExact X)

/-- Derived module lower shriek from the lisse-étale site to the associated
étale site. -/
abbrev lisseEtaleModuleLowerShriekDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) :=
  Functor.totalLeftDerived (lisseEtaleModuleLowerShriekToDerived X)
    (RingedSite.Hom.moduleLocalization (lisseEtaleRingedSite X))
    (RingedSite.Hom.ModuleQis.{z} (lisseEtaleRingedSite X))

/-- The homotopy lisse-étale module lower-shriek/inverse-image adjunction
descends to derived categories. -/
instance lisseEtaleModuleLowerShriekDerived.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (lisseEtaleModuleLowerShriekCoeff X).mapHomotopyCategory (up ℤ))
      (F := (lisseEtaleModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
      (RingedSite.Hom.ModuleQis.{z} (lisseEtaleRingedSite X))
      (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
      (L1 := RingedSite.Hom.moduleLocalization (lisseEtaleRingedSite X))
      (L2 := RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) := sorry

/-- The total-derived lisse-étale module lower-shriek/inverse-image
adjunction. -/
def lisseEtaleModuleLowerShriekDerived.totalAdjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleModuleLowerShriekDerived X ⊣
      (lisseEtaleModuleInverseImageToDerived X).totalRightDerived
        (RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
        (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleLowerShriek.adjunction (J := lisseEtaleTopology X)
        (K := X.etaleTopology) (lisseEtaleInclusion X)
        (etaleStructureSheaf X)))
    (RingedSite.Hom.ModuleQis.{z} (lisseEtaleRingedSite X))
    (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))

/-- Exact derived lisse-étale module inverse image is a right-derived functor. -/
instance lisseEtaleModuleInverseImageDerived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (lisseEtaleModuleInverseImageDerived X).IsRightDerivedFunctor
      (lisseEtaleModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) := sorry

/-- The total-right-derived lisse-étale module inverse image agrees with the
exact derived inverse image. -/
def lisseEtaleModuleInverseImageTotalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (lisseEtaleModuleInverseImageToDerived X).totalRightDerived
        (RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
        (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) ≅
      lisseEtaleModuleInverseImageDerived X :=
  Functor.rightDerivedNatIso
    ((lisseEtaleModuleInverseImageToDerived X).totalRightDerived
      (RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
      (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))))
    (lisseEtaleModuleInverseImageDerived X)
    ((lisseEtaleModuleInverseImageToDerived X).totalRightDerivedUnit
      (RingedSite.Hom.moduleLocalization (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
      (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))))
    (lisseEtaleModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
    (RingedSite.Hom.ModuleQis.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)))
    (Iso.refl _)

namespace lisseEtaleModuleLowerShriekDerived

/-- Derived lisse-étale module lower shriek is left adjoint to exact derived
module inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleModuleLowerShriekDerived X ⊣
      lisseEtaleModuleInverseImageDerived X :=
  (totalAdjunction X).ofNatIsoRight
    (lisseEtaleModuleInverseImageTotalDerivedIso X)

/-- Hom-sets out of derived lisse-étale module lower shriek are morphisms into
derived restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X))
    (G : RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X))) :
    ((lisseEtaleModuleLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (lisseEtaleModuleInverseImageDerived X).obj G) :=
  (adjunction X).homEquiv F G

end lisseEtaleModuleLowerShriekDerived

/-- The unit `id ⟶ g^* Lg_!` is an isomorphism on derived lisse-étale modules. -/
instance lisseEtaleModuleLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X)) :
    IsIso ((lisseEtaleModuleLowerShriekDerived.adjunction X).unit.app F) :=
  sorry

/-- Derived inverse image after derived lisse-étale module lower shriek is the
identity functor. -/
def lisseEtaleModuleLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleModuleLowerShriekDerived X ⋙
      lisseEtaleModuleInverseImageDerived X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      (asIso ((lisseEtaleModuleLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

/-- Bundled exact coefficient-`z` module inverse image along the flat-fppf
inclusion. -/
abbrev flatFppfModuleInverseImageExact (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.ModuleCat.{z} (ringedSite X) ⥤ₑ
      RingedSite.ModuleCat.{z} (flatFppfRingedSite X) :=
  moduleInverseImage.exactFunctor (J := flatFppfTopology X)
    (K := inheritedFppfTopology X) (flatFppfInclusion X) (structureSheaf X)

/-- Homotopy-to-derived presentation of flat-fppf module inverse image. -/
abbrev flatFppfModuleInverseImageToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (ringedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X) :=
  (flatFppfModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (flatFppfRingedSite X)

/-- Homotopy-to-derived presentation of flat-fppf module lower shriek. -/
abbrev flatFppfModuleLowerShriekToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (flatFppfRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (ringedSite X) :=
  (flatFppfModuleLowerShriekCoeff X).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (ringedSite X)

/-- The homotopy-to-derived flat-fppf module inverse image has a total
right-derived functor. -/
instance flatFppfModuleInverseImageToDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasRightDerivedFunctor (flatFppfModuleInverseImageToDerived X)
      (RingedSite.Hom.ModuleQis.{z} (ringedSite X)) := sorry

/-- The homotopy-to-derived flat-fppf module lower shriek has a total
left-derived functor. -/
instance flatFppfModuleLowerShriekToDerived.hasLeftDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasLeftDerivedFunctor (flatFppfModuleLowerShriekToDerived X)
      (RingedSite.Hom.ModuleQis.{z} (flatFppfRingedSite X)) := sorry

/-- Derived module inverse image along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (ringedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X) :=
  ExactFunctor.mapDerivedCategory (flatFppfModuleInverseImageExact X)

/-- Derived module lower shriek from the flat-fppf site to the inherited fppf
site. -/
abbrev flatFppfModuleLowerShriekDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (ringedSite X) :=
  Functor.totalLeftDerived (flatFppfModuleLowerShriekToDerived X)
    (RingedSite.Hom.moduleLocalization (flatFppfRingedSite X))
    (RingedSite.Hom.ModuleQis.{z} (flatFppfRingedSite X))

/-- The homotopy flat-fppf module lower-shriek/inverse-image adjunction descends
to derived categories. -/
instance flatFppfModuleLowerShriekDerived.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (flatFppfModuleLowerShriekCoeff X).mapHomotopyCategory (up ℤ))
      (F := (flatFppfModuleInverseImageCoeff X).mapHomotopyCategory (up ℤ))
      (RingedSite.Hom.ModuleQis.{z} (flatFppfRingedSite X))
      (RingedSite.Hom.ModuleQis.{z} (ringedSite X))
      (L1 := RingedSite.Hom.moduleLocalization (flatFppfRingedSite X))
      (L2 := RingedSite.Hom.moduleLocalization (ringedSite X)) := sorry

/-- The total-derived flat-fppf module lower-shriek/inverse-image adjunction. -/
def flatFppfModuleLowerShriekDerived.totalAdjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfModuleLowerShriekDerived X ⊣
      (flatFppfModuleInverseImageToDerived X).totalRightDerived
        (RingedSite.Hom.moduleLocalization (ringedSite X))
        (RingedSite.Hom.ModuleQis.{z} (ringedSite X)) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleLowerShriek.adjunction (J := flatFppfTopology X)
        (K := inheritedFppfTopology X) (flatFppfInclusion X)
        (structureSheaf X)))
    (RingedSite.Hom.ModuleQis.{z} (flatFppfRingedSite X))
    (RingedSite.Hom.ModuleQis.{z} (ringedSite X))

/-- Exact derived flat-fppf module inverse image is a right-derived functor. -/
instance flatFppfModuleInverseImageDerived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (flatFppfModuleInverseImageDerived X).IsRightDerivedFunctor
      (flatFppfModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
      (RingedSite.Hom.ModuleQis.{z} (ringedSite X)) := sorry

/-- The total-right-derived flat-fppf module inverse image agrees with the exact
derived inverse image. -/
def flatFppfModuleInverseImageTotalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (flatFppfModuleInverseImageToDerived X).totalRightDerived
        (RingedSite.Hom.moduleLocalization (ringedSite X))
        (RingedSite.Hom.ModuleQis.{z} (ringedSite X)) ≅
      flatFppfModuleInverseImageDerived X :=
  Functor.rightDerivedNatIso
    ((flatFppfModuleInverseImageToDerived X).totalRightDerived
      (RingedSite.Hom.moduleLocalization (ringedSite X))
      (RingedSite.Hom.ModuleQis.{z} (ringedSite X)))
    (flatFppfModuleInverseImageDerived X)
    ((flatFppfModuleInverseImageToDerived X).totalRightDerivedUnit
      (RingedSite.Hom.moduleLocalization (ringedSite X))
      (RingedSite.Hom.ModuleQis.{z} (ringedSite X)))
    (flatFppfModuleInverseImageExact X).obj.mapDerivedCategoryFactorsh.inv
    (RingedSite.Hom.ModuleQis.{z} (ringedSite X))
    (Iso.refl _)

namespace flatFppfModuleLowerShriekDerived

/-- Derived flat-fppf module lower shriek is left adjoint to exact derived
module inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfModuleLowerShriekDerived X ⊣
      flatFppfModuleInverseImageDerived X :=
  (totalAdjunction X).ofNatIsoRight
    (flatFppfModuleInverseImageTotalDerivedIso X)

/-- Hom-sets out of derived flat-fppf module lower shriek are morphisms into
derived restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X))
    (G : RingedSite.Hom.ModuleDerived.{z} (ringedSite X)) :
    ((flatFppfModuleLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (flatFppfModuleInverseImageDerived X).obj G) :=
  (adjunction X).homEquiv F G

end flatFppfModuleLowerShriekDerived

/-- The unit `id ⟶ g^* Lg_!` is an isomorphism on derived flat-fppf modules. -/
instance flatFppfModuleLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X)) :
    IsIso ((flatFppfModuleLowerShriekDerived.adjunction X).unit.app F) :=
  sorry

/-- Derived inverse image after derived flat-fppf module lower shriek is the
identity functor. -/
def flatFppfModuleLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfModuleLowerShriekDerived X ⋙
      flatFppfModuleInverseImageDerived X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      (asIso ((flatFppfModuleLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

end AlgebraicGeometry.AlgebraicStack
