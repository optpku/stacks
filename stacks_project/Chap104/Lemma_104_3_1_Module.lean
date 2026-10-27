/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedLowerShriek

/-!
# Derived module inverse-image compatibility

Inverse-image spellings for the lisse-étale and flat-fppf inclusions, together
with typed checks of their canonical derived lower-shriek adjunctions.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Coefficient-`z` module inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImageCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (etaleStructureSheaf X) ⥤
      SheafOfModules.{z} (lisseEtaleStructureSheaf X) :=
  moduleInverseImage (J := lisseEtaleTopology X) (K := X.etaleTopology)
    (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Bundled exact coefficient-`z` module inverse image along the lisse-étale
inclusion. -/
abbrev lisseEtaleModuleInverseImageExact (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.ModuleCat.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤ₑ
      RingedSite.ModuleCat.{z} (lisseEtaleRingedSite X) :=
  moduleInverseImage.exactFunctor (J := lisseEtaleTopology X)
    (K := X.etaleTopology) (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- Derived module inverse image along the lisse-étale inclusion. -/
abbrev lisseEtaleModuleInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (RingedSite.ofRingSheaf X.etaleTopology (etaleStructureSheaf X)) ⥤
      RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X) :=
  lisseEtaleInclusionDerivedInverseImage X

/-- Coefficient-`z` module inverse image along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImageCoeff (X : GroupoidsOver S)
    [AlgebraicStack X] :
    SheafOfModules.{z} (structureSheaf X) ⥤
      SheafOfModules.{z} (flatFppfStructureSheaf X) :=
  moduleInverseImage (J := flatFppfTopology X) (K := inheritedFppfTopology X)
    (flatFppfInclusion X) (structureSheaf X)

/-- Bundled exact coefficient-`z` module inverse image along the flat-fppf
inclusion. -/
abbrev flatFppfModuleInverseImageExact (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.ModuleCat.{z} (ringedSite X) ⥤ₑ
      RingedSite.ModuleCat.{z} (flatFppfRingedSite X) :=
  moduleInverseImage.exactFunctor (J := flatFppfTopology X)
    (K := inheritedFppfTopology X) (flatFppfInclusion X) (structureSheaf X)

/-- Derived module inverse image along the flat-fppf inclusion. -/
abbrev flatFppfModuleInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    RingedSite.Hom.ModuleDerived.{z} (ringedSite X) ⥤
      RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X) :=
  flatFppfInclusionDerivedInverseImage X

variable (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusionDerivedLowerShriek.adjunction X :
  lisseEtaleInclusionDerivedLowerShriek.{u, z} X ⊣ lisseEtaleInclusionDerivedInverseImage X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusionDerivedLowerShriek.adjunction X :
  flatFppfInclusionDerivedLowerShriek.{u, z} X ⊣ flatFppfInclusionDerivedInverseImage X)

end AlgebraicGeometry.AlgebraicStack
