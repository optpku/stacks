/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedComparison
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Ringed

/-!
# Derived lower shriek for algebraic-stack site inclusions

Derived lower shriek on abelian sheaves and modules is left adjoint to exact
inverse image for the lisse-étale and flat-fppf inclusions. The canonical units
are invertible, giving inverse-image-after-lower-shriek isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Derived lisse-étale lower shriek of abelian sheaves is left adjoint to
exact derived inverse image. -/
def lisseEtaleAbelianLowerShriekDerived.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleAbelianLowerShriekDerived X ⊣
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X) :=
  Functor.AbelianLowerShriek.derived.adjunction
    (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X)

/-- Morphisms out of derived lisse-étale abelian lower shriek correspond to
morphisms into derived inverse image. -/
def lisseEtaleAbelianLowerShriekDerived.homEquiv
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}))
    (G : DerivedCategory (Sheaf (X.etaleTopology) AddCommGrpCat.{z})) :
    ((lisseEtaleAbelianLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X)).obj G) :=
  (lisseEtaleAbelianLowerShriekDerived.adjunction X).homEquiv F G

/-- The derived lisse-étale abelian lower-shriek adjunction has invertible unit. -/
instance lisseEtaleAbelianLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z})) :
    IsIso ((lisseEtaleAbelianLowerShriekDerived.adjunction X).unit.app F) := sorry

/-- Derived inverse image after lisse-étale abelian lower shriek is naturally
isomorphic to the identity, by inversion of the adjunction unit. -/
def lisseEtaleAbelianLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleAbelianLowerShriekDerived X ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X) ≅ 𝟭 (DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z})) :=
  NatIso.ofComponents
    (fun F => (asIso ((lisseEtaleAbelianLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

/-- The derived lisse-étale module lower-shriek adjunction has invertible unit. -/
instance lisseEtaleModuleLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (SheafOfModules.{z} (lisseEtaleStructureSheaf X))) :
    IsIso ((lisseEtaleInclusionDerivedLowerShriek.adjunction X).unit.app F) := sorry

/-- Derived inverse image after lisse-étale module lower shriek is naturally
isomorphic to the identity, by inversion of the adjunction unit. -/
def lisseEtaleModuleLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    lisseEtaleInclusionDerivedLowerShriek X ⋙
      lisseEtaleInclusionDerivedInverseImage X ≅ 𝟭 (RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X)) :=
  NatIso.ofComponents
    (fun F => (asIso ((lisseEtaleInclusionDerivedLowerShriek.adjunction X).unit.app F)).symm)
    sorry

/-- Derived flat-fppf lower shriek of abelian sheaves is left adjoint to
exact derived inverse image. -/
def flatFppfAbelianLowerShriekDerived.adjunction
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfAbelianLowerShriekDerived X ⊣
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) :=
  Functor.AbelianLowerShriek.derived.adjunction
    (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)

/-- Morphisms out of derived flat-fppf abelian lower shriek correspond to
morphisms into derived inverse image. -/
def flatFppfAbelianLowerShriekDerived.homEquiv
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}))
    (G : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z})) :
    ((flatFppfAbelianLowerShriekDerived X).obj F ⟶ G) ≃
      (F ⟶ (siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)).obj G) :=
  (flatFppfAbelianLowerShriekDerived.adjunction X).homEquiv F G

/-- The derived flat-fppf abelian lower-shriek adjunction has invertible unit. -/
instance flatFppfAbelianLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z})) :
    IsIso ((flatFppfAbelianLowerShriekDerived.adjunction X).unit.app F) := sorry

/-- Derived inverse image after flat-fppf abelian lower shriek is naturally
isomorphic to the identity, by inversion of the adjunction unit. -/
def flatFppfAbelianLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfAbelianLowerShriekDerived X ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) ≅ 𝟭 (DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z})) :=
  NatIso.ofComponents
    (fun F => (asIso ((flatFppfAbelianLowerShriekDerived.adjunction X).unit.app F)).symm)
    sorry

/-- The derived flat-fppf module lower-shriek adjunction has invertible unit. -/
instance flatFppfModuleLowerShriekDerived_unit_app_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]
    (F : DerivedCategory (SheafOfModules.{z} (flatFppfStructureSheaf X))) :
    IsIso ((flatFppfInclusionDerivedLowerShriek.adjunction X).unit.app F) := sorry

/-- Derived inverse image after flat-fppf module lower shriek is naturally
isomorphic to the identity, by inversion of the adjunction unit. -/
def flatFppfModuleLowerShriekDerived_comp_inverseImage
    (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}] :
    flatFppfInclusionDerivedLowerShriek X ⋙
      flatFppfInclusionDerivedInverseImage X ≅ 𝟭 (RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X)) :=
  NatIso.ofComponents
    (fun F => (asIso ((flatFppfInclusionDerivedLowerShriek.adjunction X).unit.app F)).symm)
    sorry

end AlgebraicGeometry.AlgebraicStack
