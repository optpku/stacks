module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.RingTheory.Unramified.Locality

/-!
# Locality of unramified scheme morphisms

This file relates unramifiedness and G-unramifiedness to local properties of
the induced ring homomorphisms and records affine, cover, and restriction
criteria, including locality on the source for the étale precoverage.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is unramified exactly when it is locally of type
`RingHom.Unramified`. -/
theorem unramified_iff_locallyOfType :
    Unramified f ↔ LocallyOfType RingHom.Unramified f := sorry

/-- A scheme morphism is G-unramified exactly when it is locally of type
`RingHom.GUnramified`. -/
theorem gUnramified_iff_locallyOfType :
    GUnramified f ↔ LocallyOfType RingHom.GUnramified f := sorry

/-- Unramifiedness is detected on every map of sections induced by compatible
affine opens. -/
theorem unramified_iff_affineOpen_appLE_unramified :
    Unramified f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Unramified (f.appLE V U e).hom := sorry

/-- A scheme morphism is unramified exactly when it is unramified on open
covers of the target and the corresponding pullbacks. -/
theorem unramified_iff_exists_openCover :
    Unramified f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Unramified (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- A scheme morphism is unramified exactly when the induced section maps on
affine covers of the target and the corresponding pullbacks are unramified. -/
theorem unramified_iff_exists_affineOpenCover :
    Unramified f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Unramified
              (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := sorry

/-- Restriction to compatible open subschemes preserves unramifiedness. -/
instance unramified_resLE
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) [Unramified f] :
    Unramified (f.resLE V U e) := sorry

/-- G-unramifiedness is detected on every map of sections induced by
compatible affine opens. -/
theorem gUnramified_iff_affineOpen_appLE_gUnramified :
    GUnramified f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.GUnramified (f.appLE V U e).hom := sorry

/-- A scheme morphism is G-unramified exactly when it is G-unramified on open
covers of the target and the corresponding pullbacks. -/
theorem gUnramified_iff_exists_openCover :
    GUnramified f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, GUnramified (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- A scheme morphism is G-unramified exactly when the induced section maps on
affine covers of the target and the corresponding pullbacks are G-unramified. -/
theorem gUnramified_iff_exists_affineOpenCover :
    GUnramified f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.GUnramified
              (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom) := sorry

/-- Restriction to compatible open subschemes preserves G-unramifiedness. -/
instance gUnramified_resLE
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) [GUnramified f] :
    GUnramified (f.resLE V U e) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Unramified

/-- Unramifiedness of scheme morphisms is local on the source for the étale precoverage. -/
instance isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Unramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Unramified

namespace AlgebraicGeometry.GUnramified

/-- G-unramifiedness of scheme morphisms is local on the source for the étale precoverage. -/
instance isLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.GUnramified :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.GUnramified
