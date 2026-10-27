/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedPushforward
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open RingedSite.Cocontinuous RingedSite.Hom
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- The canonical lisse-étale derived module pushforward/restriction comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def lisseEtaleDerivedPushforwardRestrictionComparison (φ : X ⟶ Y) [Smooth φ] :
    etaleDerivedPushforward φ ⋙ lisseEtaleInclusionDerivedInverseImage Y ⟶
      lisseEtaleInclusionDerivedInverseImage X ⋙ lisseEtaleDerivedPushforward φ :=
  (mateEquiv (etaleDerivedPushforward.adjunction φ)
      (lisseEtaleDerivedPushforward.adjunction φ)
      (lisseEtaleDerivedInverseImageSquare φ)).natTrans

/-- The canonical lisse-étale pushforward restriction comparison is invertible. -/
instance lisseEtaleDerivedPushforwardRestrictionComparison.instIsIso (φ : X ⟶ Y) [Smooth φ] :
    IsIso (lisseEtaleDerivedPushforwardRestrictionComparison φ) := sorry

/-- The canonical lisse-étale derived module pushforward/restriction comparison
as a natural isomorphism. -/
def lisseEtaleDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Smooth φ] :
    etaleDerivedPushforward φ ⋙ lisseEtaleInclusionDerivedInverseImage Y ≅
      lisseEtaleInclusionDerivedInverseImage X ⋙
        lisseEtaleDerivedPushforward φ :=
  CategoryTheory.asIso (lisseEtaleDerivedPushforwardRestrictionComparison φ)

/-- The canonical lisse-étale derived abelian-sheaf pushforward/restriction comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def lisseEtaleAbelianDerivedPushforwardRestrictionComparison (φ : X ⟶ Y)
    [Smooth φ] :
    etaleAbelianDerivedPushforward φ ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleInclusion Y) ⟶
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) ⋙
        lisseEtaleAbelianDerivedPushforward φ :=
  (mateEquiv (etaleAbelianDerivedPushforward.adjunction φ)
      (lisseEtaleAbelianDerivedPushforward.adjunction φ)
      (lisseEtaleAbelianDerivedInverseImageSquare φ)).natTrans

/-- The canonical lisse-étale pushforward restriction comparison is invertible. -/
@[stacks 0GR3]
instance lisseEtaleAbelianDerivedPushforwardRestrictionComparison.instIsIso (φ : X ⟶ Y) [Smooth φ] :
    IsIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ) := sorry

/-- The canonical lisse-étale derived abelian-sheaf pushforward/restriction comparison
as a natural isomorphism. -/
def lisseEtaleAbelianDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Smooth φ] :
    etaleAbelianDerivedPushforward φ ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleInclusion Y) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) ⋙
        lisseEtaleAbelianDerivedPushforward φ :=
  CategoryTheory.asIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ)

/-- The canonical flat-fppf derived module pushforward/restriction comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def flatFppfDerivedPushforwardRestrictionComparison (φ : X ⟶ Y) [Flat φ] :
    fppfDerivedPushforward φ ⋙ flatFppfInclusionDerivedInverseImage Y ⟶
      flatFppfInclusionDerivedInverseImage X ⋙ flatFppfDerivedPushforward φ :=
  (mateEquiv (fppfDerivedPushforward.adjunction φ)
      (flatFppfDerivedPushforward.adjunction φ)
      (flatFppfDerivedInverseImageSquare φ)).natTrans

/-- The canonical flat-fppf pushforward restriction comparison is invertible. -/
instance flatFppfDerivedPushforwardRestrictionComparison.instIsIso (φ : X ⟶ Y) [Flat φ] :
    IsIso (flatFppfDerivedPushforwardRestrictionComparison φ) := sorry

/-- The canonical flat-fppf derived module pushforward/restriction comparison
as a natural isomorphism. -/
def flatFppfDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Flat φ] :
    fppfDerivedPushforward φ ⋙ flatFppfInclusionDerivedInverseImage Y ≅
      flatFppfInclusionDerivedInverseImage X ⋙
        flatFppfDerivedPushforward φ :=
  CategoryTheory.asIso (flatFppfDerivedPushforwardRestrictionComparison φ)

/-- The canonical flat-fppf derived abelian-sheaf pushforward/restriction comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def flatFppfAbelianDerivedPushforwardRestrictionComparison (φ : X ⟶ Y)
    [Flat φ] :
    fppfAbelianDerivedPushforward φ ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y) ⟶
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (flatFppfTopology X) (inheritedFppfTopology X)
          (flatFppfInclusion X) ⋙
        flatFppfAbelianDerivedPushforward φ :=
  (mateEquiv (fppfAbelianDerivedPushforward.adjunction φ)
      (flatFppfAbelianDerivedPushforward.adjunction φ)
      (flatFppfAbelianDerivedInverseImageSquare φ)).natTrans

/-- The canonical flat-fppf pushforward restriction comparison is invertible. -/
@[stacks 0GR3]
instance flatFppfAbelianDerivedPushforwardRestrictionComparison.instIsIso (φ : X ⟶ Y) [Flat φ] :
    IsIso (flatFppfAbelianDerivedPushforwardRestrictionComparison φ) := sorry

/-- The canonical flat-fppf derived abelian-sheaf pushforward/restriction comparison
as a natural isomorphism. -/
def flatFppfAbelianDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Flat φ] :
    fppfAbelianDerivedPushforward φ ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (flatFppfTopology Y) (inheritedFppfTopology Y)
        (flatFppfInclusion Y) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (flatFppfTopology X) (inheritedFppfTopology X)
          (flatFppfInclusion X) ⋙
        flatFppfAbelianDerivedPushforward φ :=
  CategoryTheory.asIso (flatFppfAbelianDerivedPushforwardRestrictionComparison φ)

end AlgebraicGeometry.AlgebraicStack
