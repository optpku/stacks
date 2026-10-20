module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Flat base change of scheme-theoretic images of algebraic stacks

Formation of a scheme-theoretic image factorization of a quasi-compact
morphism of algebraic stacks commutes with 2-fibre-product base change along
a flat morphism. The comparison of apices is induced by an explicit
factorization 2-isomorphism, without choosing an image carrier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- The cospan transformation induced by a factorization 2-isomorphism, with
left leg `toImage`, right leg `𝟙 Y'`, and base `𝟙 Y`. -/
def pullbackCospan {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    CospanTransform f g ι g :=
  CospanTransform.mk toImage (𝟙 Y') (𝟙 Y) (α ≪≫ (ρ_ f).symm)
    (λ_ g ≪≫ (ρ_ g).symm)

/-- The left vertex of the induced cospan transformation is `toImage`. -/
theorem pullbackCospan_left {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    (pullbackCospan f toImage ι g α).left = toImage :=
  sorry

/-- The right vertex of the induced cospan transformation is the identity of `Y'`. -/
theorem pullbackCospan_right {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    (pullbackCospan f toImage ι g α).right = 𝟙 Y' :=
  sorry

/-- The base vertex of the induced cospan transformation is the identity of `Y`. -/
theorem pullbackCospan_base {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    (pullbackCospan f toImage ι g α).base = 𝟙 Y :=
  sorry

/-- The comparison `X ×_Y Y' ⟶ Z ×_Y Y'` induced by a factorization
`toImage ≫ ι ≅ f`. -/
def pullbackToImage {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} ι g :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u} (pullbackCospan f toImage ι g α)

/-- The comparison of base changes is the two-fibre-product map of the
induced cospan transformation. -/
theorem pullbackToImage_eq {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    pullbackToImage f toImage ι g α =
      TwoFibreProduct.map.{u + 1, u, u + 1, u} (pullbackCospan f toImage ι g α) :=
  sorry

/-- The comparison of base changes commutes with the first projection up to
the canonical 2-isomorphism, recovering `toImage` on the first factor. -/
def pullbackToImage_fstIso {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    pullbackToImage f toImage ι g α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} ι g ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≫ toImage :=
  TwoFibreProduct.map.fstIso (pullbackCospan f toImage ι g α)

/-- The comparison of base changes commutes with the second projection up to
the canonical 2-isomorphism. -/
def pullbackToImage_sndIso {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    (g : Y' ⟶ Y) (α : toImage ≫ ι ≅ f) :
    pullbackToImage f toImage ι g α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g ≫ 𝟙 Y' :=
  TwoFibreProduct.map.sndIso (pullbackCospan f toImage ι g α)

/-- Scheme-theoretic images of quasi-compact morphisms of algebraic stacks
commute with 2-fibre-product base change along a flat morphism. -/
instance of_twoFibreProduct_flat {S : Scheme.{u}}
    {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (α : toImage ≫ ι ≅ f) :
    IsSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      (pullbackToImage f toImage ι g α)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g) :=
  sorry

/-- Existence of a scheme-theoretic image is preserved by 2-fibre-product
base change along a flat morphism, for a quasi-compact source morphism. -/
theorem hasSchemeTheoreticImage_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (hf : HasSchemeTheoreticImage f) :
    HasSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The essential image of a scheme-theoretic image inclusion after flat
base change equals the essential image of the base-changed inclusion. -/
theorem objectProperty_twoFibreProduct_eq {S : Scheme.{u}}
    {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι]
    {Z' : GroupoidsOver S} [AlgebraicStack Z']
    {toImage' : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g ⟶ Z'}
    {ι' : Z' ⟶ Y'}
    [IsSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      toImage' ι'] :
    (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor ι').essImage =
      (CategoryTheory.FiberedCategoryOver.Groupoids.toFunctor
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g)).essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
