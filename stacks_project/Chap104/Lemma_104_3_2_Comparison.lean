module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Square
public import stacks_project.Chap104.Lemma_104_3_2_Pushforward

/-!
# Identity-1 restriction mates on the 103.15.1 square

The unbounded derived identities `g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹` are the
right mates of the inverse-image squares of `104.3.2.1` along
`f⁻¹ ⊣ Rf_*` and `(f')⁻¹ ⊣ Rf'_*`, for modules and abelian sheaves on
the lisse-étale and flat-fppf presentations.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]

/-- Modules on the lisse-étale inverse-image ring sheaf form an abelian
category. -/
instance lisseEtaleInverseImageModuleCat_abelian (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    Abelian (RingedSite.ModuleCat.{z}
      (moduleInverseImage.source (J := lisseEtaleTopology Z)
        (K := Z.etaleTopology) (lisseEtaleInclusion Z)
        (etaleStructureSheaf Z))) :=
  sorry

/-- Modules on the étale ringed site form an abelian category. -/
instance etaleModuleCat_abelian (Z : GroupoidsOver S) [AlgebraicStack Z] :
    Abelian (RingedSite.ModuleCat.{z}
      (RingedSite.ofRingSheaf Z.etaleTopology (etaleStructureSheaf Z))) :=
  sorry

/-- Modules on the flat-fppf inverse-image ring sheaf form an abelian
category. -/
instance flatFppfInverseImageModuleCat_abelian (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    Abelian (RingedSite.ModuleCat.{z}
      (moduleInverseImage.source (J := flatFppfTopology Z)
        (K := inheritedFppfTopology Z) (flatFppfInclusion Z)
        (structureSheaf Z))) :=
  sorry

/-- Modules on the inherited fppf ringed site form an abelian category. -/
instance inheritedFppfModuleCat_abelian (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    Abelian (RingedSite.ModuleCat.{z}
      (RingedSite.ofRingSheaf (inheritedFppfTopology Z) (structureSheaf Z))) :=
  sorry

/-- Derived categories of étale modules exist. -/
instance etaleModuleCat_hasDerivedCategory (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    HasDerivedCategory.{max (max (max (u + 1) u) u) (z + 1)}
      (RingedSite.ModuleCat.{z}
        (moduleInverseImage.target (K := Z.etaleTopology)
          (etaleStructureSheaf Z))) :=
  sorry

/-- Derived categories of lisse-étale inverse-image modules exist. -/
instance lisseEtaleInverseImageModuleCat_hasDerivedCategory
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasDerivedCategory.{max (max (max (u + 1) u) u) (z + 1)}
      (RingedSite.ModuleCat.{z}
        (moduleInverseImage.source (J := lisseEtaleTopology Z)
          (K := Z.etaleTopology) (lisseEtaleInclusion Z)
          (etaleStructureSheaf Z))) :=
  sorry

/-- Derived categories of inherited-fppf modules exist. -/
instance inheritedFppfModuleCat_hasDerivedCategory (Z : GroupoidsOver S)
    [AlgebraicStack Z] :
    HasDerivedCategory.{max (max (max (u + 1) u) u) (z + 1)}
      (RingedSite.ModuleCat.{z}
        (moduleInverseImage.target (K := inheritedFppfTopology Z)
          (structureSheaf Z))) :=
  sorry

/-- Derived categories of flat-fppf inverse-image modules exist. -/
instance flatFppfInverseImageModuleCat_hasDerivedCategory
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    HasDerivedCategory.{max (max (max (u + 1) u) u) (z + 1)}
      (RingedSite.ModuleCat.{z}
        (moduleInverseImage.source (J := flatFppfTopology Z)
          (K := inheritedFppfTopology Z) (flatFppfInclusion Z)
          (structureSheaf Z))) :=
  sorry

/-- The lisse-étale module identity-1 comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def lisseEtaleDerivedPushforwardRestrictionComparison (φ : X ⟶ Y) [Smooth φ] :
    etaleDerivedPushforward φ ⋙ lisseEtaleInclusionDerivedInverseImage Y ⟶
      lisseEtaleInclusionDerivedInverseImage X ⋙ lisseEtaleDerivedPushforward φ :=
  (mateEquiv (etaleDerivedPushforward.adjunction φ)
      (lisseEtaleDerivedPushforward.adjunction φ)
      (lisseEtaleDerivedInverseImageSquare φ)).natTrans

/-- The lisse-étale module identity-1 comparison is the right mate of the
derived inverse-image square. -/
theorem lisseEtaleDerivedPushforwardRestrictionComparison_spec (φ : X ⟶ Y)
    [Smooth φ] :
    lisseEtaleDerivedPushforwardRestrictionComparison φ =
      (mateEquiv (etaleDerivedPushforward.adjunction φ)
          (lisseEtaleDerivedPushforward.adjunction φ)
          (lisseEtaleDerivedInverseImageSquare φ)).natTrans :=
  sorry

/-- The lisse-étale module identity-1 comparison as a natural isomorphism. -/
def lisseEtaleDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Smooth φ] [IsIso (lisseEtaleDerivedPushforwardRestrictionComparison φ)] :
    etaleDerivedPushforward φ ⋙ lisseEtaleInclusionDerivedInverseImage Y ≅
      lisseEtaleInclusionDerivedInverseImage X ⋙
        lisseEtaleDerivedPushforward φ :=
  CategoryTheory.asIso (lisseEtaleDerivedPushforwardRestrictionComparison φ)

/-- The lisse-étale abelian identity-1 comparison
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

/-- The lisse-étale abelian identity-1 comparison is the right mate of the
derived inverse-image square. -/
theorem lisseEtaleAbelianDerivedPushforwardRestrictionComparison_spec
    (φ : X ⟶ Y) [Smooth φ] :
    lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ =
      (mateEquiv (etaleAbelianDerivedPushforward.adjunction φ)
          (lisseEtaleAbelianDerivedPushforward.adjunction φ)
          (lisseEtaleAbelianDerivedInverseImageSquare φ)).natTrans :=
  sorry

/-- The lisse-étale abelian identity-1 comparison as a natural isomorphism. -/
def lisseEtaleAbelianDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Smooth φ]
    [IsIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ)] :
    etaleAbelianDerivedPushforward φ ⋙
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
        (lisseEtaleTopology Y) Y.etaleTopology (lisseEtaleInclusion Y) ≅
      siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
          (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X) ⋙
        lisseEtaleAbelianDerivedPushforward φ :=
  CategoryTheory.asIso (lisseEtaleAbelianDerivedPushforwardRestrictionComparison φ)

/-- The flat-fppf module identity-1 comparison
`Rf_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ Rf'_*`. -/
def flatFppfDerivedPushforwardRestrictionComparison (φ : X ⟶ Y) [Flat φ] :
    fppfDerivedPushforward φ ⋙ flatFppfInclusionDerivedInverseImage Y ⟶
      flatFppfInclusionDerivedInverseImage X ⋙ flatFppfDerivedPushforward φ :=
  (mateEquiv (fppfDerivedPushforward.adjunction φ)
      (flatFppfDerivedPushforward.adjunction φ)
      (flatFppfDerivedInverseImageSquare φ)).natTrans

/-- The flat-fppf module identity-1 comparison is the right mate of the derived
inverse-image square. -/
theorem flatFppfDerivedPushforwardRestrictionComparison_spec (φ : X ⟶ Y)
    [Flat φ] :
    flatFppfDerivedPushforwardRestrictionComparison φ =
      (mateEquiv (fppfDerivedPushforward.adjunction φ)
          (flatFppfDerivedPushforward.adjunction φ)
          (flatFppfDerivedInverseImageSquare φ)).natTrans :=
  sorry

/-- The flat-fppf module identity-1 comparison as a natural isomorphism. -/
def flatFppfDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Flat φ] [IsIso (flatFppfDerivedPushforwardRestrictionComparison φ)] :
    fppfDerivedPushforward φ ⋙ flatFppfInclusionDerivedInverseImage Y ≅
      flatFppfInclusionDerivedInverseImage X ⋙
        flatFppfDerivedPushforward φ :=
  CategoryTheory.asIso (flatFppfDerivedPushforwardRestrictionComparison φ)

/-- The flat-fppf abelian identity-1 comparison
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

/-- The flat-fppf abelian identity-1 comparison is the right mate of the derived
inverse-image square. -/
theorem flatFppfAbelianDerivedPushforwardRestrictionComparison_spec
    (φ : X ⟶ Y) [Flat φ] :
    flatFppfAbelianDerivedPushforwardRestrictionComparison φ =
      (mateEquiv (fppfAbelianDerivedPushforward.adjunction φ)
          (flatFppfAbelianDerivedPushforward.adjunction φ)
          (flatFppfAbelianDerivedInverseImageSquare φ)).natTrans :=
  sorry

/-- The flat-fppf abelian identity-1 comparison as a natural isomorphism. -/
def flatFppfAbelianDerivedPushforwardRestrictionComparison.asIso (φ : X ⟶ Y)
    [Flat φ]
    [IsIso (flatFppfAbelianDerivedPushforwardRestrictionComparison φ)] :
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
