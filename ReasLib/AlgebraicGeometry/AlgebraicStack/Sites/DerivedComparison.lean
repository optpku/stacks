/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Inclusion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived.LowerShriek

@[expose] public section

attribute [instance] RingedSite.Cocontinuous.moduleLowerShriek.additive
  RingedSite.Cocontinuous.moduleLowerShriek.toDerived.hasLeftDerived
  RingedSite.Cocontinuous.moduleLowerShriek.derived.hasPair

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- Inverse image of the étale structure sheaf along the lisse-étale inclusion. -/
abbrev lisseEtaleInverseImageRingSheaf (Z : GroupoidsOver S) [AlgebraicStack Z] :
    Sheaf (lisseEtaleTopology Z) RingCat.{u} :=
  inverseImageRingSheaf (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Inverse image of the fppf structure sheaf along the flat-fppf inclusion. -/
abbrev flatFppfInverseImageRingSheaf (Z : GroupoidsOver S) [AlgebraicStack Z] :
    Sheaf (flatFppfTopology Z) RingCat.{u} :=
  inverseImageRingSheaf (flatFppfInclusion Z) (structureSheaf Z)

/-- Inverse image of `etaleSiteHom_structureSheafMap φ` along the lisse-étale inclusion
of `X`. -/
def lisseEtaleStructureSheafMap (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    lisseEtaleInverseImageRingSheaf X ⟶
      ((lisseEtaleMap φ).sheafPushforwardContinuous RingCat.{u}
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj
        (lisseEtaleInverseImageRingSheaf Y) :=
  ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
      (lisseEtaleTopology X) X.etaleTopology).map (etaleSiteHom_structureSheafMap φ)

/-- The lisse-étale coefficient map is an isomorphism. -/
instance lisseEtaleStructureSheafMap.instIsIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    IsIso (lisseEtaleStructureSheafMap φ) := sorry

/-- Inverse image of `structureSheafMap φ` along the flat-fppf inclusion of
`X`. -/
def flatFppfStructureSheafMap (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    flatFppfInverseImageRingSheaf X ⟶
      ((flatFppfMap φ).sheafPushforwardContinuous RingCat.{u}
        (flatFppfTopology X) (flatFppfTopology Y)).obj
        (flatFppfInverseImageRingSheaf Y) :=
  ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
      (flatFppfTopology X) (inheritedFppfTopology X)).map (structureSheafMap φ)

/-- The flat-fppf coefficient map is an isomorphism. -/
instance flatFppfStructureSheafMap.instIsIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    IsIso (flatFppfStructureSheafMap φ) := sorry

/-- Pushforward of modules along `etaleSiteHom_structureSheafMap` preserves finite
limits. -/
instance etaleModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (etaleSiteHom_structureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `etaleSiteHom_structureSheafMap` preserves finite
colimits. -/
instance etaleModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (etaleSiteHom_structureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `lisseEtaleStructureSheafMap` preserves finite
limits. -/
instance lisseEtaleModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (lisseEtaleStructureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `lisseEtaleStructureSheafMap` preserves finite
colimits. -/
instance lisseEtaleModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (lisseEtaleStructureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `structureSheafMap` preserves finite
limits. -/
instance fppfModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (structureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `structureSheafMap` preserves finite
colimits. -/
instance fppfModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (structureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `flatFppfStructureSheafMap` preserves finite
limits. -/
instance flatFppfModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (flatFppfStructureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `flatFppfStructureSheafMap` preserves finite
colimits. -/
instance flatFppfModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (flatFppfStructureSheafMap φ)) :=
  sorry

/-- Exact étale module inverse image landing in `Mod(𝒪_X)`. -/
abbrev etaleExactInverseImage (φ : X ⟶ Y) :
    RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf Y.etaleTopology (etaleStructureSheaf Y)) ⥤ₑ
      RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) :=
  ExactFunctor.of (SheafOfModules.pushforward.{z} (etaleSiteHom_structureSheafMap φ))

/-- Exact lisse-étale module inverse image along the coefficient iso. -/
abbrev lisseEtaleExactInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
          (lisseEtaleInverseImageRingSheaf Y)) ⥤ₑ
      RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology X)
          (lisseEtaleInverseImageRingSheaf X)) :=
  ExactFunctor.of (SheafOfModules.pushforward.{z} (lisseEtaleStructureSheafMap φ))

/-- Exact fppf module inverse image landing in `Mod(𝒪_X)`. -/
abbrev fppfExactInverseImage (φ : X ⟶ Y) :
    RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Y) (structureSheaf Y)) ⥤ₑ
      RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)) :=
  ExactFunctor.of (SheafOfModules.pushforward.{z} (structureSheafMap φ))

/-- Exact flat-fppf module inverse image along the coefficient iso. -/
abbrev flatFppfExactInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Y)
          (flatFppfInverseImageRingSheaf Y)) ⥤ₑ
      RingedSite.ModuleCat.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology X)
          (flatFppfInverseImageRingSheaf X)) :=
  ExactFunctor.of (SheafOfModules.pushforward.{z} (flatFppfStructureSheafMap φ))

/-- Derived étale inverse image landing in `D(𝒪_X)`. -/
abbrev etaleDerivedInverseImage (φ : X ⟶ Y) :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf Y.etaleTopology (etaleStructureSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) :=
  (etaleExactInverseImage.{u, z} φ).mapDerivedCategory

/-- Derived lisse-étale inverse image landing in modules over `(g')⁻¹ 𝒪_X`. -/
abbrev lisseEtaleDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
          (lisseEtaleInverseImageRingSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology X)
          (lisseEtaleInverseImageRingSheaf X)) :=
  (lisseEtaleExactInverseImage.{u, z} φ).mapDerivedCategory

/-- Derived fppf inverse image landing in `D(𝒪_X)`. -/
abbrev fppfDerivedInverseImage (φ : X ⟶ Y) :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Y) (structureSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)) :=
  (fppfExactInverseImage.{u, z} φ).mapDerivedCategory

/-- Derived flat-fppf inverse image landing in modules over `(g')⁻¹ 𝒪_X`. -/
abbrev flatFppfDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Y)
          (flatFppfInverseImageRingSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology X)
          (flatFppfInverseImageRingSheaf X)) :=
  (flatFppfExactInverseImage.{u, z} φ).mapDerivedCategory

/-- Derived inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleInclusionDerivedInverseImage (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf Z.etaleTopology (etaleStructureSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Z)
          (lisseEtaleInverseImageRingSheaf Z)) :=
  moduleInverseImage.derived (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived inverse image along the flat-fppf inclusion. -/
abbrev flatFppfInclusionDerivedInverseImage (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Z) (structureSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Z)
          (flatFppfInverseImageRingSheaf Z)) :=
  moduleInverseImage.derived (flatFppfInclusion Z) (structureSheaf Z)

/-- Derived module lower shriek along the lisse-étale inclusion. -/
abbrev lisseEtaleInclusionDerivedLowerShriek (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Z)
          (lisseEtaleInverseImageRingSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf Z.etaleTopology (etaleStructureSheaf Z)) :=
  moduleLowerShriek.derived (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived module lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfInclusionDerivedLowerShriek (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Z)
          (flatFppfInverseImageRingSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Z) (structureSheaf Z)) :=
  moduleLowerShriek.derived (flatFppfInclusion Z) (structureSheaf Z)

/-- Derived lower shriek along the lisse-étale inclusion is left adjoint to
derived inverse image. -/
def lisseEtaleInclusionDerivedLowerShriek.adjunction (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    lisseEtaleInclusionDerivedLowerShriek Z ⊣
      lisseEtaleInclusionDerivedInverseImage Z :=
  moduleLowerShriek.derived.adjunction (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived lower shriek along the flat-fppf inclusion is left adjoint to
derived inverse image. -/
def flatFppfInclusionDerivedLowerShriek.adjunction (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    flatFppfInclusionDerivedLowerShriek Z ⊣
      flatFppfInclusionDerivedInverseImage Z :=
  moduleLowerShriek.derived.adjunction (flatFppfInclusion Z) (structureSheaf Z)

/-- Underived commuting isomorphism of the two composite exact inverse images
on the lisse-étale square. -/
def lisseEtaleInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    (moduleInverseImage.exactFunctor.{z} (lisseEtaleInclusion Y) (etaleStructureSheaf Y)).comp
      (lisseEtaleExactInverseImage.{u, z} φ) ≅
    (etaleExactInverseImage.{u, z} φ).comp
      (moduleInverseImage.exactFunctor.{z} (lisseEtaleInclusion X) (etaleStructureSheaf X)) :=
  ObjectProperty.isoMk _
    (SheafOfModules.pushforwardComp (lisseEtaleStructureSheafMap φ)
        (𝟙 (lisseEtaleInverseImageRingSheaf Y)) ≪≫
      (SheafOfModules.pushforwardComp (𝟙 (lisseEtaleInverseImageRingSheaf X))
        (etaleSiteHom_structureSheafMap φ)).symm)

/-- Underived commuting isomorphism of the two composite exact inverse images
on the flat-fppf square. -/
def flatFppfInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    (moduleInverseImage.exactFunctor.{z} (flatFppfInclusion Y) (structureSheaf Y)).comp
      (flatFppfExactInverseImage.{u, z} φ) ≅
    (fppfExactInverseImage.{u, z} φ).comp
      (moduleInverseImage.exactFunctor.{z} (flatFppfInclusion X) (structureSheaf X)) :=
  ObjectProperty.isoMk _
    (SheafOfModules.pushforwardComp (flatFppfStructureSheafMap φ)
        (𝟙 (flatFppfInverseImageRingSheaf Y)) ≪≫
      (SheafOfModules.pushforwardComp (𝟙 (flatFppfInverseImageRingSheaf X))
        (structureSheafMap φ)).symm)

/-- The derived inverse-image square of the lisse-étale functoriality square,
after transport along `etaleSiteHom_structureSheafMap`. -/
def lisseEtaleDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    TwoSquare
      (lisseEtaleInclusionDerivedInverseImage Y)
      (etaleDerivedInverseImage φ)
      (lisseEtaleDerivedInverseImage φ)
      (lisseEtaleInclusionDerivedInverseImage X) :=
  (ExactFunctor.MapDerivedCategory.squareIso
    (moduleInverseImage.exactFunctor.{z} (lisseEtaleInclusion Y) (etaleStructureSheaf Y))
    (lisseEtaleExactInverseImage.{u, z} φ) (etaleExactInverseImage.{u, z} φ)
    (moduleInverseImage.exactFunctor.{z} (lisseEtaleInclusion X) (etaleStructureSheaf X))
    (lisseEtaleInverseImageExactCompIso φ)).hom

/-- The derived lower-shriek comparison of the lisse-étale functoriality square. -/
def lisseEtaleDerivedLowerShriekComparisonNatTrans (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    lisseEtaleDerivedInverseImage φ ⋙
      lisseEtaleInclusionDerivedLowerShriek X ⟶
      lisseEtaleInclusionDerivedLowerShriek Y ⋙
        etaleDerivedInverseImage φ :=
  DerivedBaseChange.mapOfRight
    (lisseEtaleInclusionDerivedLowerShriek.adjunction Y)
    (lisseEtaleInclusionDerivedLowerShriek.adjunction X)
    (lisseEtaleDerivedInverseImageSquare φ)

/-- The derived inverse-image square of the flat-fppf functoriality square,
after transport along `structureSheafMap`. -/
def flatFppfDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    TwoSquare
      (flatFppfInclusionDerivedInverseImage Y)
      (fppfDerivedInverseImage φ)
      (flatFppfDerivedInverseImage φ)
      (flatFppfInclusionDerivedInverseImage X) :=
  (ExactFunctor.MapDerivedCategory.squareIso
    (moduleInverseImage.exactFunctor.{z} (flatFppfInclusion Y) (structureSheaf Y))
    (flatFppfExactInverseImage.{u, z} φ) (fppfExactInverseImage.{u, z} φ)
    (moduleInverseImage.exactFunctor.{z} (flatFppfInclusion X) (structureSheaf X))
    (flatFppfInverseImageExactCompIso φ)).hom

/-- The derived lower-shriek comparison of the flat-fppf functoriality square. -/
def flatFppfDerivedLowerShriekComparisonNatTrans (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    flatFppfDerivedInverseImage φ ⋙
      flatFppfInclusionDerivedLowerShriek X ⟶
      flatFppfInclusionDerivedLowerShriek Y ⋙
        fppfDerivedInverseImage φ :=
  DerivedBaseChange.mapOfRight
    (flatFppfInclusionDerivedLowerShriek.adjunction Y)
    (flatFppfInclusionDerivedLowerShriek.adjunction X)
    (flatFppfDerivedInverseImageSquare φ)

/-- Derived étale inverse image of abelian sheaves. -/
abbrev etaleAbelianDerivedInverseImage (φ : X ⟶ Y) :
    DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} X.etaleTopology Y.etaleTopology (toFunctor φ)

/-- Derived lisse-étale inverse image of abelian sheaves. -/
abbrev lisseEtaleAbelianDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) (lisseEtaleTopology Y)
    (lisseEtaleMap φ)

/-- Derived fppf inverse image of abelian sheaves. -/
abbrev fppfAbelianDerivedInverseImage (φ : X ⟶ Y) :
    DerivedCategory (Sheaf (inheritedFppfTopology Y) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (inheritedFppfTopology X) (inheritedFppfTopology Y)
    (toFunctor φ)

/-- Derived flat-fppf inverse image of abelian sheaves. -/
abbrev flatFppfAbelianDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (flatFppfTopology Y)
    (flatFppfMap φ)

/-- Derived abelian lower shriek along the lisse-étale inclusion. -/
abbrev lisseEtaleAbelianLowerShriekDerived (Z : GroupoidsOver S) [AlgebraicStack Z] :
    DerivedCategory (Sheaf (lisseEtaleTopology Z) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf Z.etaleTopology AddCommGrpCat.{z}) :=
  Functor.AbelianLowerShriek.derived (lisseEtaleTopology Z) Z.etaleTopology
    (lisseEtaleInclusion Z)

/-- Derived abelian lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfAbelianLowerShriekDerived (Z : GroupoidsOver S) [AlgebraicStack Z] :
    DerivedCategory (Sheaf (flatFppfTopology Z) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology Z) AddCommGrpCat.{z}) :=
  Functor.AbelianLowerShriek.derived (flatFppfTopology Z) (inheritedFppfTopology Z)
    (flatFppfInclusion Z)

/-- Underived commuting isomorphism of the two composite exact inverse images
of abelian sheaves on the lisse-étale square. -/
def lisseEtaleAbelianInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology Y) Y.etaleTopology
        (lisseEtaleInclusion Y)).comp
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) (lisseEtaleTopology Y)
        (lisseEtaleMap φ)) ≅
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} X.etaleTopology Y.etaleTopology (toFunctor φ)).comp
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X)) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- Underived commuting isomorphism of the two composite exact inverse images
of abelian sheaves on the flat-fppf square. -/
def flatFppfAbelianInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y)).comp
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (flatFppfTopology Y)
        (flatFppfMap φ)) ≅
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (inheritedFppfTopology X) (inheritedFppfTopology Y)
        (toFunctor φ)).comp
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (inheritedFppfTopology X)
        (flatFppfInclusion X)) :=
  ObjectProperty.isoMk _ (Iso.refl _)

/-- The derived inverse-image square of abelian sheaves on the lisse-étale
functoriality square. -/
def lisseEtaleAbelianDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    TwoSquare (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (lisseEtaleTopology Y) Y.etaleTopology
        (lisseEtaleInclusion Y))
      (etaleAbelianDerivedInverseImage φ)
      (lisseEtaleAbelianDerivedInverseImage φ)
      (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X)) :=
  (ExactFunctor.MapDerivedCategory.squareIso
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology Y) Y.etaleTopology
        (lisseEtaleInclusion Y))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) (lisseEtaleTopology Y)
        (lisseEtaleMap φ))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} X.etaleTopology Y.etaleTopology (toFunctor φ))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X))
      (lisseEtaleAbelianInverseImageExactCompIso φ)).hom

/-- The derived lower-shriek comparison of abelian sheaves on the lisse-étale
functoriality square. -/
def lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    lisseEtaleAbelianDerivedInverseImage φ ⋙ lisseEtaleAbelianLowerShriekDerived X ⟶
      lisseEtaleAbelianLowerShriekDerived Y ⋙ etaleAbelianDerivedInverseImage φ :=
  DerivedBaseChange.mapOfRight
    (Functor.AbelianLowerShriek.derived.adjunction (lisseEtaleTopology Y) Y.etaleTopology
      (lisseEtaleInclusion Y))
    (Functor.AbelianLowerShriek.derived.adjunction (lisseEtaleTopology X) X.etaleTopology
      (lisseEtaleInclusion X))
    (lisseEtaleAbelianDerivedInverseImageSquare φ)

/-- The derived inverse-image square of abelian sheaves on the flat-fppf
functoriality square. -/
def flatFppfAbelianDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    TwoSquare
      (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y))
      (fppfAbelianDerivedInverseImage φ)
      (flatFppfAbelianDerivedInverseImage φ)
      (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (inheritedFppfTopology X)
        (flatFppfInclusion X)) :=
  (ExactFunctor.MapDerivedCategory.squareIso
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (flatFppfTopology Y)
        (flatFppfMap φ))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (inheritedFppfTopology X) (inheritedFppfTopology Y)
        (toFunctor φ))
      (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} (flatFppfTopology X) (inheritedFppfTopology X)
        (flatFppfInclusion X))
      (flatFppfAbelianInverseImageExactCompIso φ)).hom

/-- The derived lower-shriek comparison of abelian sheaves on the flat-fppf
functoriality square. -/
def flatFppfAbelianDerivedLowerShriekComparisonNatTrans (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    flatFppfAbelianDerivedInverseImage φ ⋙ flatFppfAbelianLowerShriekDerived X ⟶
      flatFppfAbelianLowerShriekDerived Y ⋙ fppfAbelianDerivedInverseImage φ :=
  DerivedBaseChange.mapOfRight
    (Functor.AbelianLowerShriek.derived.adjunction (flatFppfTopology Y) (inheritedFppfTopology Y)
      (flatFppfInclusion Y))
    (Functor.AbelianLowerShriek.derived.adjunction (flatFppfTopology X) (inheritedFppfTopology X)
      (flatFppfInclusion X))
    (flatFppfAbelianDerivedInverseImageSquare φ)

/-- The canonical lisse-étale module lower-shriek comparison. -/
def lisseEtaleDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Smooth φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
        (lisseEtaleInverseImageRingSheaf Y))) :
    (lisseEtaleInclusionDerivedLowerShriek X).obj
      ((lisseEtaleDerivedInverseImage φ).obj G) ⟶
      (etaleDerivedInverseImage φ).obj
        ((lisseEtaleInclusionDerivedLowerShriek Y).obj G) :=
  (lisseEtaleDerivedLowerShriekComparisonNatTrans φ).app G

/-- The lisse-étale module comparison is an isomorphism. -/
instance lisseEtaleDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : DerivedCategory (SheafOfModules.{z} (lisseEtaleInverseImageRingSheaf Y))) :
    IsIso (lisseEtaleDerivedLowerShriekComparison φ G) := sorry

/-- The canonical flat-fppf module lower-shriek comparison. -/
def flatFppfDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Flat φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (flatFppfTopology Y)
        (flatFppfInverseImageRingSheaf Y))) :
    (flatFppfInclusionDerivedLowerShriek X).obj
      ((flatFppfDerivedInverseImage φ).obj G) ⟶
      (fppfDerivedInverseImage φ).obj
        ((flatFppfInclusionDerivedLowerShriek Y).obj G) :=
  (flatFppfDerivedLowerShriekComparisonNatTrans φ).app G

/-- The flat-fppf module comparison is an isomorphism. -/
instance flatFppfDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ]
    (G : DerivedCategory (SheafOfModules.{z} (flatFppfInverseImageRingSheaf Y))) :
    IsIso (flatFppfDerivedLowerShriekComparison φ G) := sorry

/-- The canonical lisse-étale abelian-sheaf lower-shriek comparison. -/
def lisseEtaleAbelianDerivedLowerShriekComparison (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})) :
    (lisseEtaleAbelianLowerShriekDerived X).obj
      ((lisseEtaleAbelianDerivedInverseImage φ).obj G) ⟶
      (etaleAbelianDerivedInverseImage φ).obj
        ((lisseEtaleAbelianLowerShriekDerived Y).obj G) :=
  (lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans φ).app G

/-- The lisse-étale abelian comparison is an isomorphism. -/
instance lisseEtaleAbelianDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Smooth φ]
    (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})) :
    IsIso (lisseEtaleAbelianDerivedLowerShriekComparison φ G) := sorry

/-- The canonical flat-fppf abelian-sheaf lower-shriek comparison. -/
def flatFppfAbelianDerivedLowerShriekComparison (φ : X ⟶ Y) [AlgebraicStack.Flat φ]
    (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})) :
    (flatFppfAbelianLowerShriekDerived X).obj
      ((flatFppfAbelianDerivedInverseImage φ).obj G) ⟶
      (fppfAbelianDerivedInverseImage φ).obj
        ((flatFppfAbelianLowerShriekDerived Y).obj G) :=
  (flatFppfAbelianDerivedLowerShriekComparisonNatTrans φ).app G

/-- The flat-fppf abelian comparison is an isomorphism. -/
instance flatFppfAbelianDerivedLowerShriekComparison.isIso (φ : X ⟶ Y)
    [AlgebraicStack.Flat φ]
    (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})) :
    IsIso (flatFppfAbelianDerivedLowerShriekComparison φ G) := sorry

end AlgebraicGeometry.AlgebraicStack
