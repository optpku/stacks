/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.Lemma_103_14_2_Sites
public import stacks_project.Chap103.Lemma_103_14_2_Topos

/-!
# Derived abelian lower shriek along lisse-étale and flat-fppf inclusions

The unbounded left derived functors of abelian sheaf pullback along the fully
faithful inclusions of Lemma 103.14.2. The right adjoint is exact derived
inverse image, and the unit encodes `g⁻¹ Lg_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor
open ComplexShape

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Sheafification of abelian sheaves on the associated étale site. -/
instance etaleTopology_hasSheafify (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify X.etaleTopology AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the associated étale site. -/
instance etaleTopology_hasWeakSheafify (X : GroupoidsOver S) [AlgebraicStack X] :
    HasWeakSheafify X.etaleTopology AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the lisse-étale site. -/
instance lisseEtaleTopology_hasSheafify (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the lisse-étale site. -/
instance lisseEtaleTopology_hasWeakSheafify (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasWeakSheafify (lisseEtaleTopology X) AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the inherited fppf site. -/
instance inheritedFppfTopology_hasSheafify (X : GroupoidsOver S) :
    HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the inherited fppf site. -/
instance inheritedFppfTopology_hasWeakSheafify (X : GroupoidsOver S) :
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the flat-fppf site. -/
instance flatFppfTopology_hasSheafify (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (flatFppfTopology X) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the flat-fppf site. -/
instance flatFppfTopology_hasWeakSheafify (X : GroupoidsOver S)
    [AlgebraicStack X] :
    HasWeakSheafify (flatFppfTopology X) AddCommGrpCat.{z} := sorry

/-- Left Kan extensions of abelian presheaves along the lisse-étale inclusion. -/
instance lisseEtaleInclusion.op_hasLeftKanExtension (X : GroupoidsOver S)
    [AlgebraicStack X] (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (lisseEtaleInclusion X).op.HasLeftKanExtension P := sorry

/-- Left Kan extensions of abelian presheaves along the flat-fppf inclusion. -/
instance flatFppfInclusion.op_hasLeftKanExtension (X : GroupoidsOver S)
    [AlgebraicStack X] (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (flatFppfInclusion X).op.HasLeftKanExtension P := sorry

/-- Abelian sheaf pullback along the lisse-étale inclusion is additive. -/
instance lisseEtaleAbelianLowerShriek_additive (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((lisseEtaleInclusion X).sheafPullback AddCommGrpCat.{z}
        (lisseEtaleTopology X) X.etaleTopology).Additive := sorry

/-- Continuous pushforward of abelian sheaves along the lisse-étale inclusion is
additive. -/
instance lisseEtaleAbelianInverseImage_additive (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
        (lisseEtaleTopology X) X.etaleTopology).Additive := sorry

/-- Abelian sheaf pullback along the flat-fppf inclusion is additive. -/
instance flatFppfAbelianLowerShriek_additive (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((flatFppfInclusion X).sheafPullback AddCommGrpCat.{z}
        (flatFppfTopology X) (inheritedFppfTopology X)).Additive := sorry

/-- Continuous pushforward of abelian sheaves along the flat-fppf inclusion is
additive. -/
instance flatFppfAbelianInverseImage_additive (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
        (flatFppfTopology X) (inheritedFppfTopology X)).Additive := sorry

/-- Derived inverse image of abelian sheaves along the lisse-étale inclusion. -/
abbrev lisseEtaleAbelianInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
    (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)

/-- The homotopy-to-derived presentation of abelian lower shriek along the
lisse-étale inclusion. -/
abbrev lisseEtaleAbelianLowerShriekToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    HomotopyCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) :=
  ((lisseEtaleInclusion X).sheafPullback AddCommGrpCat.{z}
        (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total left-derived abelian lower-shriek functor along the
lisse-étale inclusion. -/
instance lisseEtaleAbelianLowerShriekToDerived.hasLeftDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasLeftDerivedFunctor (lisseEtaleAbelianLowerShriekToDerived X)
      (HomotopyCategory.quasiIso
        (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The homotopy inverse image of abelian sheaves along the lisse-étale inclusion
has a total right-derived functor. -/
instance lisseEtaleAbelianInverseImageToDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasRightDerivedFunctor
      (((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- Derived abelian lower shriek along the lisse-étale inclusion. -/
abbrev lisseEtaleAbelianLowerShriekDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) :=
  Functor.totalLeftDerived (lisseEtaleAbelianLowerShriekToDerived X)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) (up ℤ))

/-- The homotopy abelian lower-shriek/inverse-image adjunction along the
lisse-étale inclusion descends to derived categories. -/
instance lisseEtaleAbelianLowerShriekDerived.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := ((lisseEtaleInclusion X).sheafPullback AddCommGrpCat.{z}
          (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory (up ℤ))
      (F := ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh
        (C := Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh
        (C := Sheaf X.etaleTopology AddCommGrpCat.{z})) := sorry

/-- The total-derived abelian lower-shriek/inverse-image adjunction along the
lisse-étale inclusion. -/
def lisseEtaleAbelianLowerShriekDerived.totalAdjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleAbelianLowerShriekDerived X ⊣
      ((((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
              (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory
            (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      ((lisseEtaleInclusion X).sheafAdjunctionContinuous AddCommGrpCat.{z}
        (lisseEtaleTopology X) X.etaleTopology))
    (HomotopyCategory.quasiIso
      (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))

/-- Exact derived lisse-étale abelian inverse image is a right-derived functor. -/
instance lisseEtaleAbelianInverseImageDerived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (lisseEtaleAbelianInverseImageDerived X).IsRightDerivedFunctor
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology
          (lisseEtaleInclusion X)).obj.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The total-right-derived lisse-étale abelian inverse image agrees with the
exact derived inverse image. -/
def lisseEtaleAbelianInverseImageTotalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory
          (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))) ≅
      lisseEtaleAbelianInverseImageDerived X :=
  Functor.rightDerivedNatIso
    ((((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory
          (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)))
    (lisseEtaleAbelianInverseImageDerived X)
    ((((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (lisseEtaleTopology X) X.etaleTopology).mapHomotopyCategory
          (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X)).obj.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso
      (Sheaf X.etaleTopology AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

namespace lisseEtaleAbelianLowerShriekDerived

/-- Derived lisse-étale abelian lower shriek is left adjoint to exact derived
inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleAbelianLowerShriekDerived X ⊣
      lisseEtaleAbelianInverseImageDerived X :=
  (lisseEtaleAbelianLowerShriekDerived.totalAdjunction X).ofNatIsoRight
    (lisseEtaleAbelianInverseImageTotalDerivedIso X)

/-- Hom-sets out of derived lisse-étale abelian lower shriek are morphisms into
derived restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}))
    (G : DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z})) :
    ((lisseEtaleAbelianLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (lisseEtaleAbelianInverseImageDerived X).obj G) :=
  (adjunction X).homEquiv F G

end lisseEtaleAbelianLowerShriekDerived

/-- The unit `id ⟶ g⁻¹ Lg_!` is an isomorphism on derived lisse-étale abelian
sheaves. -/
instance lisseEtaleAbelianLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z})) :
    IsIso ((lisseEtaleAbelianLowerShriekDerived.adjunction X).unit.app F) :=
  sorry

/-- Derived inverse image after derived lisse-étale abelian lower shriek is the
identity functor. -/
def lisseEtaleAbelianLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleAbelianLowerShriekDerived X ⋙
      lisseEtaleAbelianInverseImageDerived X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      (asIso
          ((lisseEtaleAbelianLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

/-- Derived inverse image of abelian sheaves along the flat-fppf inclusion. -/
abbrev flatFppfAbelianInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
    (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)

/-- The homotopy-to-derived presentation of abelian lower shriek along the
flat-fppf inclusion. -/
abbrev flatFppfAbelianLowerShriekToDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    HomotopyCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  ((flatFppfInclusion X).sheafPullback AddCommGrpCat.{z}
        (flatFppfTopology X) (inheritedFppfTopology X)).mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total left-derived abelian lower-shriek functor along the
flat-fppf inclusion. -/
instance flatFppfAbelianLowerShriekToDerived.hasLeftDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasLeftDerivedFunctor (flatFppfAbelianLowerShriekToDerived X)
      (HomotopyCategory.quasiIso
        (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The homotopy inverse image of abelian sheaves along the flat-fppf inclusion
has a total right-derived functor. -/
instance flatFppfAbelianInverseImageToDerived.hasRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    Functor.HasRightDerivedFunctor
      (((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (flatFppfTopology X)
            (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- Derived abelian lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfAbelianLowerShriekDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  Functor.totalLeftDerived (flatFppfAbelianLowerShriekToDerived X)
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) (up ℤ))

/-- The homotopy abelian lower-shriek/inverse-image adjunction along the
flat-fppf inclusion descends to derived categories. -/
instance flatFppfAbelianLowerShriekDerived.hasPair
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := ((flatFppfInclusion X).sheafPullback AddCommGrpCat.{z}
          (flatFppfTopology X)
          (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ))
      (F := ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (flatFppfTopology X)
          (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh
        (C := Sheaf (flatFppfTopology X) AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh
        (C := Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})) := sorry

/-- The total-derived abelian lower-shriek/inverse-image adjunction along the
flat-fppf inclusion. -/
def flatFppfAbelianLowerShriekDerived.totalAdjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfAbelianLowerShriekDerived X ⊣
      ((((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
              (flatFppfTopology X)
              (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      ((flatFppfInclusion X).sheafAdjunctionContinuous AddCommGrpCat.{z}
        (flatFppfTopology X) (inheritedFppfTopology X)))
    (HomotopyCategory.quasiIso
      (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))

/-- Exact derived flat-fppf abelian inverse image is a right-derived functor. -/
instance flatFppfAbelianInverseImageDerived.isRightDerived
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    (flatFppfAbelianInverseImageDerived X).IsRightDerivedFunctor
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
          (flatFppfTopology X) (inheritedFppfTopology X)
          (flatFppfInclusion X)).obj.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The total-right-derived flat-fppf abelian inverse image agrees with the
exact derived inverse image. -/
def flatFppfAbelianInverseImageTotalDerivedIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    ((((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (flatFppfTopology X)
            (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))) ≅
      flatFppfAbelianInverseImageDerived X :=
  Functor.rightDerivedNatIso
    ((((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (flatFppfTopology X)
            (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)))
    (flatFppfAbelianInverseImageDerived X)
    ((((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
            (flatFppfTopology X)
            (inheritedFppfTopology X)).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z}
        (flatFppfTopology X) (inheritedFppfTopology X)
        (flatFppfInclusion X)).obj.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso
      (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

namespace flatFppfAbelianLowerShriekDerived

/-- Derived flat-fppf abelian lower shriek is left adjoint to exact derived
inverse image. -/
def adjunction (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfAbelianLowerShriekDerived X ⊣
      flatFppfAbelianInverseImageDerived X :=
  (flatFppfAbelianLowerShriekDerived.totalAdjunction X).ofNatIsoRight
    (flatFppfAbelianInverseImageTotalDerivedIso X)

/-- Hom-sets out of derived flat-fppf abelian lower shriek are morphisms into
derived restriction. -/
def homEquiv (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}))
    (G : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})) :
    ((flatFppfAbelianLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (flatFppfAbelianInverseImageDerived X).obj G) :=
  (adjunction X).homEquiv F G

end flatFppfAbelianLowerShriekDerived

/-- The unit `id ⟶ g⁻¹ Lg_!` is an isomorphism on derived flat-fppf abelian
sheaves. -/
instance flatFppfAbelianLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z})) :
    IsIso ((flatFppfAbelianLowerShriekDerived.adjunction X).unit.app F) :=
  sorry

/-- Derived inverse image after derived flat-fppf abelian lower shriek is the
identity functor. -/
def flatFppfAbelianLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfAbelianLowerShriekDerived X ⋙
      flatFppfAbelianInverseImageDerived X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      (asIso
          ((flatFppfAbelianLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

end AlgebraicGeometry.AlgebraicStack
