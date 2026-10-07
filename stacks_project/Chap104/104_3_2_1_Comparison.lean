module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap103.«103_15_1_1_Map»
public import stacks_project.Chap104.«104_3_2_1_Sites»

/-!
# Derived lower-shriek comparison of a site square

A strictly commutative square of continuous and cocontinuous functors of sites
determines the left mate
`(f')⁻¹ ⋙ L(g')_! ⟶ Lg_! ⋙ f⁻¹`
of the derived inverse-image square along the two derived lower-shriek
adjunctions. Because the ReasLib derived inverse-image/lower-shriek
leaf currently fails to synthesize `HasDerivedCategory` on ring-sheaf
presentations, module inverse image along inclusions is
`exactFunctor.mapDerivedCategory` and module lower shriek is
`totalLeftDerived` of the underived homotopy presentation, left adjoint
via the total-derived pair. Coefficient inverse images are
`ExactFunctor.of (SheafOfModules.pushforward coeff)` on derived
categories, and the comparison is `DerivedBaseChange.mapOfRight`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous

open scoped Bicategory
open ComplexShape

noncomputable section

universe z uC vC w u

namespace AlgebraicGeometry.AlgebraicStack

section CoefficientDerived

variable {C D : Type uC} [Category.{vC} C] [Category.{vC} D]

/-- The standard derived-category structure on modules over a ring-sheaf
presentation. -/
instance instHasDerivedCategory_moduleCat_ofRingSheaf
    (J : GrothendieckTopology C) (O : Sheaf J RingCat.{w})
    [UnivLE.{max uC vC, z}] :
    HasDerivedCategory.{max (max (max uC vC) w) (z + 1)}
      (RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J O)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory (RingedSite.ofRingSheaf J O)

/-- Derived module inverse image along a continuous functor and a coefficient
morphism of ring sheaves. -/
abbrev derivedCoefficientInverseImage
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : C ⥤ D) [f.IsContinuous J K]
    {S₀ : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (α : S₀ ⟶ (f.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [PreservesFiniteLimits (SheafOfModules.pushforward.{z} α)]
    [PreservesFiniteColimits (SheafOfModules.pushforward.{z} α)]
    [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf K R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf J S₀) :=
  (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory

/-- The derived square induced by an isomorphism of composites of exact module
functors on ring-sheaf presentations. -/
abbrev derivedExactSquare
    {C₁ C₂ C₃ C₄ : Type uC}
    [Category.{vC} C₁] [Category.{vC} C₂] [Category.{vC} C₃] [Category.{vC} C₄]
    {J₁ : GrothendieckTopology C₁} {R₁ : Sheaf J₁ RingCat.{w}}
    {J₂ : GrothendieckTopology C₂} {R₂ : Sheaf J₂ RingCat.{w}}
    {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ RingCat.{w}}
    {J₄ : GrothendieckTopology C₄} {R₄ : Sheaf J₄ RingCat.{w}}
    [UnivLE.{max uC vC, z}]
    (F : RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₁ R₁) ⥤ₑ
      RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₂ R₂))
    (G : RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₂ R₂) ⥤ₑ
      RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₄ R₄))
    (H : RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₁ R₁) ⥤ₑ
      RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₃ R₃))
    (I : RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₃ R₃) ⥤ₑ
      RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf J₄ R₄))
    (e : F.comp G ≅ H.comp I) :
    TwoSquare F.mapDerivedCategory H.mapDerivedCategory
      G.mapDerivedCategory I.mapDerivedCategory :=
  (ExactFunctor.MapDerivedCategory.squareIso F G H I e).hom

end CoefficientDerived

section DerivedModuleShriek

variable {C D : Type uC} [Category.{vC} C] [Category.{vC} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Module lower shriek along a continuous and cocontinuous site functor is
additive. -/
instance moduleLowerShriek_additive
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    (moduleLowerShriek (J := J) (K := K) f R).Additive :=
  moduleLowerShriek.additive (J := J) (K := K) f R

/-- Homotopy-to-derived presentation of module inverse image. -/
abbrev moduleInverseImageToDerived
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleHomotopy.{z} (moduleInverseImage.target (K := K) R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.source (J := J) (K := K) f R) :=
  (moduleInverseImage (J := J) (K := K) f R).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (moduleInverseImage.source (J := J) (K := K) f R)

/-- Homotopy-to-derived presentation of module lower shriek. -/
abbrev moduleLowerShriekToDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleHomotopy.{z}
        (moduleInverseImage.source (J := J) (K := K) f R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.target (K := K) R) :=
  (moduleLowerShriek (J := J) (K := K) f R).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization (moduleInverseImage.target (K := K) R)

/-- The homotopy-to-derived module inverse image has a total right-derived
functor. -/
instance moduleInverseImageToDerived.hasRightDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    Functor.HasRightDerivedFunctor (moduleInverseImageToDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R)) :=
  sorry

/-- The homotopy-to-derived module lower shriek has a total left-derived
functor. -/
instance moduleLowerShriekToDerived.hasLeftDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    Functor.HasLeftDerivedFunctor (moduleLowerShriekToDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R)) :=
  sorry

/-- Exact derived module inverse image along a continuous and cocontinuous site
functor. -/
abbrev derivedModuleInverseImage
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.target (K := K) R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.source (J := J) (K := K) f R) :=
  (moduleInverseImage.exactFunctor (J := J) (K := K) f R).mapDerivedCategory

/-- Total left-derived module lower shriek along a continuous and cocontinuous
site functor. -/
abbrev derivedModuleLowerShriek
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.source (J := J) (K := K) f R) ⥤
      RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.target (K := K) R) :=
  Functor.totalLeftDerived (moduleLowerShriekToDerived (J := J) (K := K) f R)
    (RingedSite.Hom.moduleLocalization (moduleInverseImage.source (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R))

/-- The homotopy module lower-shriek/inverse-image adjunction descends to
derived categories. -/
instance derivedModuleLowerShriek.hasPair
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (moduleLowerShriek (J := J) (K := K) f R).mapHomotopyCategory (up ℤ))
      (F := (moduleInverseImage (J := J) (K := K) f R).mapHomotopyCategory (up ℤ))
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R))
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R))
      (L1 := RingedSite.Hom.moduleLocalization
        (moduleInverseImage.source (J := J) (K := K) f R))
      (L2 := RingedSite.Hom.moduleLocalization
        (moduleInverseImage.target (K := K) R)) :=
  sorry

/-- The total-derived module lower-shriek/inverse-image adjunction. -/
def derivedModuleLowerShriek.totalAdjunction
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    derivedModuleLowerShriek (J := J) (K := K) f R ⊣
      (moduleInverseImageToDerived (J := J) (K := K) f R).totalRightDerived
        (RingedSite.Hom.moduleLocalization (moduleInverseImage.target (K := K) R))
        (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R)) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleLowerShriek.adjunction (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R))

/-- The total-right-derived module inverse image agrees with the exact derived
inverse image. -/
def derivedModuleInverseImage.totalDerivedIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    (moduleInverseImageToDerived (J := J) (K := K) f R).totalRightDerived
        (RingedSite.Hom.moduleLocalization (moduleInverseImage.target (K := K) R))
        (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R)) ≅
      derivedModuleInverseImage (J := J) (K := K) f R :=
  Functor.rightDerivedNatIso
    ((moduleInverseImageToDerived (J := J) (K := K) f R).totalRightDerived
      (RingedSite.Hom.moduleLocalization (moduleInverseImage.target (K := K) R))
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R)))
    (derivedModuleInverseImage (J := J) (K := K) f R)
    ((moduleInverseImageToDerived (J := J) (K := K) f R).totalRightDerivedUnit
      (RingedSite.Hom.moduleLocalization (moduleInverseImage.target (K := K) R))
      (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R)))
    (moduleInverseImage.exactFunctor (J := J) (K := K) f R).obj.mapDerivedCategoryFactorsh.inv
    (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.target (K := K) R))
    (Iso.refl _)

/-- Derived module lower shriek is left adjoint to exact derived inverse
image. -/
def derivedModuleLowerShriek.adjunction
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}] :
    derivedModuleLowerShriek (J := J) (K := K) f R ⊣
      derivedModuleInverseImage (J := J) (K := K) f R :=
  (derivedModuleLowerShriek.totalAdjunction (J := J) (K := K) f R).ofNatIsoRight
    (derivedModuleInverseImage.totalDerivedIso (J := J) (K := K) f R)

/-- The Hom equivalence of derived module lower shriek against exact derived
inverse image. -/
def derivedModuleLowerShriek.homEquiv
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uC vC, z}]
    (M : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.source (J := J) (K := K) f R))
    (N : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.target (K := K) R)) :
    ((derivedModuleLowerShriek (J := J) (K := K) f R).obj M ⟶ N) ≃
      (M ⟶ (derivedModuleInverseImage (J := J) (K := K) f R).obj N) :=
  (derivedModuleLowerShriek.adjunction (J := J) (K := K) f R).homEquiv M N

end DerivedModuleShriek

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- A 1-morphism is cocontinuous for the associated étale topologies. -/
instance toFunctor.instIsCocontinuous_etale (φ : X ⟶ Y) :
    (toFunctor φ).IsCocontinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous (toCartesianBasedFunctor φ)
    (StandardTopology.etale.overTopology S)

/-- A 1-morphism is continuous for the inherited fppf topologies. -/
instance toFunctor.instIsContinuous_inheritedFppf (φ : X ⟶ Y) :
    (toFunctor φ).IsContinuous (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  CartesianBasedFunctor.inheritedTopology.isContinuous (toCartesianBasedFunctor φ)
    (Scheme.fppfTopology.over S)

/-- A 1-morphism is cocontinuous for the inherited fppf topologies. -/
instance toFunctor.instIsCocontinuous_inheritedFppf (φ : X ⟶ Y) :
    (toFunctor φ).IsCocontinuous (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous (toCartesianBasedFunctor φ)
    (Scheme.fppfTopology.over S)

/-- Inverse image of the étale structure sheaf of `Y` along a 1-morphism. -/
abbrev etaleInverseImageRingSheaf (φ : X ⟶ Y) :
    Sheaf X.etaleTopology RingCat.{u} :=
  ((toFunctor φ).sheafPushforwardContinuous RingCat.{u}
      X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y)

/-- Inverse image of the fppf structure sheaf of `Y` along a 1-morphism. -/
abbrev fppfInverseImageRingSheaf (φ : X ⟶ Y) :
    Sheaf (inheritedFppfTopology X) RingCat.{u} :=
  inverseImageStructureSheaf φ

/-- Inverse image of the étale structure sheaf along the lisse-étale inclusion. -/
abbrev lisseEtaleInverseImageRingSheaf (Z : GroupoidsOver S) [AlgebraicStack Z] :
    Sheaf (lisseEtaleTopology Z) RingCat.{u} :=
  inverseImageRingSheaf (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Inverse image of the fppf structure sheaf along the flat-fppf inclusion. -/
abbrev flatFppfInverseImageRingSheaf (Z : GroupoidsOver S) [AlgebraicStack Z] :
    Sheaf (flatFppfTopology Z) RingCat.{u} :=
  inverseImageRingSheaf (flatFppfInclusion Z) (structureSheaf Z)

/-- The coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism on étale sites. -/
instance etaleStructureSheafMap.instIsIso (φ : X ⟶ Y) :
    IsIso (etaleStructureSheafMap φ) :=
  etaleStructureSheafMap_isIso φ

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` on inherited fppf sites. -/
abbrev fppfStructureSheafMap (φ : X ⟶ Y) :
    structureSheaf X ⟶ fppfInverseImageRingSheaf φ :=
  structureSheafMap φ

/-- The coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism on inherited fppf
sites. -/
instance fppfStructureSheafMap.instIsIso (φ : X ⟶ Y) :
    IsIso (fppfStructureSheafMap φ) :=
  structureSheafMap_isIso φ

/-- Inverse image of `etaleStructureSheafMap φ` along the lisse-étale inclusion
of `X`. -/
def lisseEtaleStructureSheafMap (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    lisseEtaleInverseImageRingSheaf X ⟶
      ((lisseEtaleMap φ).sheafPushforwardContinuous RingCat.{u}
        (lisseEtaleTopology X) (lisseEtaleTopology Y)).obj
        (lisseEtaleInverseImageRingSheaf Y) :=
  ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
      (lisseEtaleTopology X) X.etaleTopology).map (etaleStructureSheafMap φ)

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
      (flatFppfTopology X) (inheritedFppfTopology X)).map (fppfStructureSheafMap φ)

/-- The flat-fppf coefficient map is an isomorphism. -/
instance flatFppfStructureSheafMap.instIsIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    IsIso (flatFppfStructureSheafMap φ) := sorry

/-- Pushforward of modules along `etaleStructureSheafMap` preserves finite
limits. -/
instance etaleModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (etaleStructureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `etaleStructureSheafMap` preserves finite
colimits. -/
instance etaleModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (etaleStructureSheafMap φ)) :=
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

/-- Pushforward of modules along `fppfStructureSheafMap` preserves finite
limits. -/
instance fppfModuleInverseImage_preservesFiniteLimits (φ : X ⟶ Y) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{z} (fppfStructureSheafMap φ)) :=
  sorry

/-- Pushforward of modules along `fppfStructureSheafMap` preserves finite
colimits. -/
instance fppfModuleInverseImage_preservesFiniteColimits (φ : X ⟶ Y) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{z} (fppfStructureSheafMap φ)) :=
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
  ExactFunctor.of (SheafOfModules.pushforward.{z} (etaleStructureSheafMap φ))

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
  ExactFunctor.of (SheafOfModules.pushforward.{z} (fppfStructureSheafMap φ))

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
  derivedCoefficientInverseImage X.etaleTopology Y.etaleTopology
    (toFunctor φ) (etaleStructureSheafMap φ)

/-- Derived lisse-étale inverse image landing in modules over `(g')⁻¹ 𝒪_X`. -/
abbrev lisseEtaleDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
          (lisseEtaleInverseImageRingSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology X)
          (lisseEtaleInverseImageRingSheaf X)) :=
  derivedCoefficientInverseImage (lisseEtaleTopology X) (lisseEtaleTopology Y)
    (lisseEtaleMap φ) (lisseEtaleStructureSheafMap φ)

/-- Derived fppf inverse image landing in `D(𝒪_X)`. -/
abbrev fppfDerivedInverseImage (φ : X ⟶ Y) :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Y) (structureSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)) :=
  derivedCoefficientInverseImage (inheritedFppfTopology X)
    (inheritedFppfTopology Y) (toFunctor φ) (fppfStructureSheafMap φ)

/-- Derived flat-fppf inverse image landing in modules over `(g')⁻¹ 𝒪_X`. -/
abbrev flatFppfDerivedInverseImage (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Y)
          (flatFppfInverseImageRingSheaf Y)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology X)
          (flatFppfInverseImageRingSheaf X)) :=
  derivedCoefficientInverseImage (flatFppfTopology X) (flatFppfTopology Y)
    (flatFppfMap φ) (flatFppfStructureSheafMap φ)

/-- Derived inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleInclusionDerivedInverseImage (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf Z.etaleTopology (etaleStructureSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Z)
          (lisseEtaleInverseImageRingSheaf Z)) :=
  derivedModuleInverseImage (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived inverse image along the flat-fppf inclusion. -/
abbrev flatFppfInclusionDerivedInverseImage (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Z) (structureSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Z)
          (flatFppfInverseImageRingSheaf Z)) :=
  derivedModuleInverseImage (flatFppfInclusion Z) (structureSheaf Z)

/-- Derived module lower shriek along the lisse-étale inclusion. -/
abbrev lisseEtaleInclusionDerivedLowerShriek (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (lisseEtaleTopology Z)
          (lisseEtaleInverseImageRingSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf Z.etaleTopology (etaleStructureSheaf Z)) :=
  derivedModuleLowerShriek (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived module lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfInclusionDerivedLowerShriek (Z : GroupoidsOver S) [AlgebraicStack Z] :
    RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (flatFppfTopology Z)
          (flatFppfInverseImageRingSheaf Z)) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (RingedSite.ofRingSheaf (inheritedFppfTopology Z) (structureSheaf Z)) :=
  derivedModuleLowerShriek (flatFppfInclusion Z) (structureSheaf Z)

/-- Derived lower shriek along the lisse-étale inclusion is left adjoint to
derived inverse image. -/
def lisseEtaleInclusionDerivedLowerShriek.adjunction (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    lisseEtaleInclusionDerivedLowerShriek Z ⊣
      lisseEtaleInclusionDerivedInverseImage Z :=
  derivedModuleLowerShriek.adjunction (lisseEtaleInclusion Z) (etaleStructureSheaf Z)

/-- Derived lower shriek along the flat-fppf inclusion is left adjoint to
derived inverse image. -/
def flatFppfInclusionDerivedLowerShriek.adjunction (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    flatFppfInclusionDerivedLowerShriek Z ⊣
      flatFppfInclusionDerivedInverseImage Z :=
  derivedModuleLowerShriek.adjunction (flatFppfInclusion Z) (structureSheaf Z)

/-- Underived commuting isomorphism of the two composite exact inverse images
on the lisse-étale square. -/
def lisseEtaleInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    (moduleInverseImage.exactFunctor (lisseEtaleInclusion Y) (etaleStructureSheaf Y)).comp
      (lisseEtaleExactInverseImage φ) ≅
    (etaleExactInverseImage φ).comp
      (moduleInverseImage.exactFunctor (lisseEtaleInclusion X) (etaleStructureSheaf X)) :=
  ObjectProperty.isoMk _
    (SheafOfModules.pushforwardComp (lisseEtaleStructureSheafMap φ)
        (𝟙 (lisseEtaleInverseImageRingSheaf Y)) ≪≫
      (SheafOfModules.pushforwardComp (𝟙 (lisseEtaleInverseImageRingSheaf X))
        (etaleStructureSheafMap φ)).symm)

/-- Underived commuting isomorphism of the two composite exact inverse images
on the flat-fppf square. -/
def flatFppfInverseImageExactCompIso (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    (moduleInverseImage.exactFunctor (flatFppfInclusion Y) (structureSheaf Y)).comp
      (flatFppfExactInverseImage φ) ≅
    (fppfExactInverseImage φ).comp
      (moduleInverseImage.exactFunctor (flatFppfInclusion X) (structureSheaf X)) :=
  ObjectProperty.isoMk _
    (SheafOfModules.pushforwardComp (flatFppfStructureSheafMap φ)
        (𝟙 (flatFppfInverseImageRingSheaf Y)) ≪≫
      (SheafOfModules.pushforwardComp (𝟙 (flatFppfInverseImageRingSheaf X))
        (fppfStructureSheafMap φ)).symm)

/-- The derived inverse-image square of the lisse-étale functoriality square,
after transport along `etaleStructureSheafMap`. -/
def lisseEtaleDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    TwoSquare
      (lisseEtaleInclusionDerivedInverseImage Y)
      (etaleDerivedInverseImage φ)
      (lisseEtaleDerivedInverseImage φ)
      (lisseEtaleInclusionDerivedInverseImage X) :=
  derivedExactSquare
    (moduleInverseImage.exactFunctor (lisseEtaleInclusion Y) (etaleStructureSheaf Y))
    (lisseEtaleExactInverseImage φ)
    (etaleExactInverseImage φ)
    (moduleInverseImage.exactFunctor (lisseEtaleInclusion X) (etaleStructureSheaf X))
    (lisseEtaleInverseImageExactCompIso φ)

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

/-- The lisse-étale comparison is the mate-transpose of the transported
inverse-image square. -/
theorem lisseEtaleDerivedLowerShriekComparisonNatTrans_spec (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    mateEquiv
      (lisseEtaleInclusionDerivedLowerShriek.adjunction Y)
      (lisseEtaleInclusionDerivedLowerShriek.adjunction X)
      (TwoSquare.mk (lisseEtaleDerivedInverseImage φ)
        (lisseEtaleInclusionDerivedLowerShriek Y)
        (lisseEtaleInclusionDerivedLowerShriek X)
        (etaleDerivedInverseImage φ)
        (lisseEtaleDerivedLowerShriekComparisonNatTrans φ)) =
      lisseEtaleDerivedInverseImageSquare φ := sorry

/-- The derived inverse-image square of the flat-fppf functoriality square,
after transport along `structureSheafMap`. -/
def flatFppfDerivedInverseImageSquare (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    TwoSquare
      (flatFppfInclusionDerivedInverseImage Y)
      (fppfDerivedInverseImage φ)
      (flatFppfDerivedInverseImage φ)
      (flatFppfInclusionDerivedInverseImage X) :=
  derivedExactSquare
    (moduleInverseImage.exactFunctor (flatFppfInclusion Y) (structureSheaf Y))
    (flatFppfExactInverseImage φ)
    (fppfExactInverseImage φ)
    (moduleInverseImage.exactFunctor (flatFppfInclusion X) (structureSheaf X))
    (flatFppfInverseImageExactCompIso φ)

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

/-- The flat-fppf comparison is the mate-transpose of the transported
inverse-image square. -/
theorem flatFppfDerivedLowerShriekComparisonNatTrans_spec (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    mateEquiv
      (flatFppfInclusionDerivedLowerShriek.adjunction Y)
      (flatFppfInclusionDerivedLowerShriek.adjunction X)
      (TwoSquare.mk (flatFppfDerivedInverseImage φ)
        (flatFppfInclusionDerivedLowerShriek Y)
        (flatFppfInclusionDerivedLowerShriek X)
        (fppfDerivedInverseImage φ)
        (flatFppfDerivedLowerShriekComparisonNatTrans φ)) =
      flatFppfDerivedInverseImageSquare φ := sorry

/-- Sheafification of abelian sheaves on the associated étale site. -/
instance etaleTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasSheafify Z.etaleTopology AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the associated étale site. -/
instance etaleTopology_hasWeakSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasWeakSheafify Z.etaleTopology AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the lisse-étale site. -/
instance lisseEtaleTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasSheafify (lisseEtaleTopology Z) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the lisse-étale site. -/
instance lisseEtaleTopology_hasWeakSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasWeakSheafify (lisseEtaleTopology Z) AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the inherited fppf site. -/
instance inheritedFppfTopology_hasSheafify (Z : GroupoidsOver S) :
    HasSheafify (inheritedFppfTopology Z) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the inherited fppf site. -/
instance inheritedFppfTopology_hasWeakSheafify (Z : GroupoidsOver S) :
    HasWeakSheafify (inheritedFppfTopology Z) AddCommGrpCat.{z} := sorry

/-- Sheafification of abelian sheaves on the flat-fppf site. -/
instance flatFppfTopology_hasSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasSheafify (flatFppfTopology Z) AddCommGrpCat.{z} := sorry

/-- Weak sheafification of abelian sheaves on the flat-fppf site. -/
instance flatFppfTopology_hasWeakSheafify (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasWeakSheafify (flatFppfTopology Z) AddCommGrpCat.{z} := sorry

/-- Left Kan extensions of abelian presheaves along the lisse-étale inclusion. -/
instance lisseEtaleInclusion.op_hasLeftKanExtension (Z : GroupoidsOver S)
    [AlgebraicStack Z] (P : (lisseEtaleSite Z)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (lisseEtaleInclusion Z).op.HasLeftKanExtension P := sorry

/-- Left Kan extensions of abelian presheaves along the flat-fppf inclusion. -/
instance flatFppfInclusion.op_hasLeftKanExtension (Z : GroupoidsOver S)
    [AlgebraicStack Z] (P : (flatFppfSite Z)ᵒᵖ ⥤ AddCommGrpCat.{z}) :
    (flatFppfInclusion Z).op.HasLeftKanExtension P := sorry

/-- Abelian sheaf pullback along a continuous functor of sites is additive. -/
instance abelianLowerShriek_additive
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K']
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J' K').Additive := sorry

/-- Continuous pushforward of abelian sheaves is additive. -/
instance sheafPushforwardContinuous_additive
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] :
    (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive := sorry

/-- The homotopy-to-derived presentation of abelian lower shriek. -/
abbrev abelianLowerShriekToDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    HomotopyCategory (Sheaf J' AddCommGrpCat.{z}) (up ℤ) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J' K').mapHomotopyCategory
      (up ℤ) ⋙
    DerivedCategory.Qh

/-- Existence of the total left-derived abelian lower-shriek functor. -/
instance abelianLowerShriekToDerived.hasLeftDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    Functor.HasLeftDerivedFunctor (abelianLowerShriekToDerived J' K' f)
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- Total left-derived lower shriek of abelian sheaves. -/
abbrev abelianLowerShriekDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    DerivedCategory (Sheaf J' AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf K' AddCommGrpCat.{z}) :=
  Functor.totalLeftDerived (abelianLowerShriekToDerived J' K' f) DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))

/-- The homotopy inverse image of abelian sheaves has a total right-derived
functor. -/
instance abelianInverseImageToDerived.hasRightDerived
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    Functor.HasRightDerivedFunctor
      ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) := sorry

/-- The homotopy abelian lower-shriek/inverse-image adjunction descends to
derived categories. -/
instance abelianLowerShriekDerived.hasPair
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback f AddCommGrpCat.{z} J' K').mapHomotopyCategory
        (up ℤ))
      (F := (f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
      (L1 := DerivedCategory.Qh (C := Sheaf J' AddCommGrpCat.{z}))
      (L2 := DerivedCategory.Qh (C := Sheaf K' AddCommGrpCat.{z})) := sorry

/-- The total-derived abelian lower-shriek/inverse-image adjunction. -/
def abelianLowerShriekDerived.totalAdjunction
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    abelianLowerShriekDerived J' K' f ⊣
      ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f AddCommGrpCat.{z} J' K'))
    (HomotopyCategory.quasiIso (Sheaf J' AddCommGrpCat.{z}) (up ℤ))
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))

/-- The total-right-derived abelian inverse image agrees with the exact derived
inverse image. -/
def abelianInverseImageTotalDerivedIso
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    ((f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f :=
  Functor.rightDerivedNatIso
    (((f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f)
    (((f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ)))
    (siteAbelianInverseImageExact.{u + 1, u, u + 1, u, z} J' K' f).obj.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (Sheaf K' AddCommGrpCat.{z}) (up ℤ))
    (Iso.refl _)

/-- Derived abelian lower shriek is left adjoint to exact derived inverse image. -/
def abelianLowerShriekDerived.adjunction
    {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
    (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
    (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
    [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
    [HasWeakSheafify K' AddCommGrpCat.{z}]
    [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P] :
    abelianLowerShriekDerived J' K' f ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z} J' K' f :=
  (abelianLowerShriekDerived.totalAdjunction J' K' f).ofNatIsoRight
    (abelianInverseImageTotalDerivedIso J' K' f)

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
  abelianLowerShriekDerived (lisseEtaleTopology Z) Z.etaleTopology
    (lisseEtaleInclusion Z)

/-- Derived abelian lower shriek along the flat-fppf inclusion. -/
abbrev flatFppfAbelianLowerShriekDerived (Z : GroupoidsOver S) [AlgebraicStack Z] :
    DerivedCategory (Sheaf (flatFppfTopology Z) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (inheritedFppfTopology Z) AddCommGrpCat.{z}) :=
  abelianLowerShriekDerived (flatFppfTopology Z) (inheritedFppfTopology Z)
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
    (abelianLowerShriekDerived.adjunction (lisseEtaleTopology Y) Y.etaleTopology
      (lisseEtaleInclusion Y))
    (abelianLowerShriekDerived.adjunction (lisseEtaleTopology X) X.etaleTopology
      (lisseEtaleInclusion X))
    (lisseEtaleAbelianDerivedInverseImageSquare φ)

/-- The lisse-étale abelian comparison is the mate-transpose of the inverse-image
square. -/
theorem lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans_spec
    (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Smooth φ] :
    mateEquiv
      (abelianLowerShriekDerived.adjunction (lisseEtaleTopology Y) Y.etaleTopology
        (lisseEtaleInclusion Y))
      (abelianLowerShriekDerived.adjunction (lisseEtaleTopology X) X.etaleTopology
        (lisseEtaleInclusion X))
      (TwoSquare.mk (lisseEtaleAbelianDerivedInverseImage φ)
        (lisseEtaleAbelianLowerShriekDerived Y)
        (lisseEtaleAbelianLowerShriekDerived X)
        (etaleAbelianDerivedInverseImage φ)
        (lisseEtaleAbelianDerivedLowerShriekComparisonNatTrans φ)) =
      lisseEtaleAbelianDerivedInverseImageSquare φ := sorry

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
    (abelianLowerShriekDerived.adjunction (flatFppfTopology Y) (inheritedFppfTopology Y)
      (flatFppfInclusion Y))
    (abelianLowerShriekDerived.adjunction (flatFppfTopology X) (inheritedFppfTopology X)
      (flatFppfInclusion X))
    (flatFppfAbelianDerivedInverseImageSquare φ)

/-- The flat-fppf abelian comparison is the mate-transpose of the inverse-image
square. -/
theorem flatFppfAbelianDerivedLowerShriekComparisonNatTrans_spec
    (φ : X ⟶ Y) [AlgebraicGeometry.AlgebraicStack.Flat φ] :
    mateEquiv
      (abelianLowerShriekDerived.adjunction (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y))
      (abelianLowerShriekDerived.adjunction (flatFppfTopology X) (inheritedFppfTopology X)
        (flatFppfInclusion X))
      (TwoSquare.mk (flatFppfAbelianDerivedInverseImage φ)
        (flatFppfAbelianLowerShriekDerived Y)
        (flatFppfAbelianLowerShriekDerived X)
        (fppfAbelianDerivedInverseImage φ)
        (flatFppfAbelianDerivedLowerShriekComparisonNatTrans φ)) =
      flatFppfAbelianDerivedInverseImageSquare φ := sorry

end AlgebraicGeometry.AlgebraicStack
