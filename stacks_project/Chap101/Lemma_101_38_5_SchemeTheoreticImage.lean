/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import stacks_project.Chap100.Lemma_100_9_2
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_38_2_SchemeTheoreticImage

/-!
# Flat base change of scheme-theoretic images of algebraic stacks

Formation of a scheme-theoretic image factorization of a quasi-compact
morphism of algebraic stacks commutes with 2-fibre-product base change along
a flat morphism. There is no chosen image carrier: the comparison is the
explicit 1-morphism of apices induced by `toImage`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage

/-- The cospan transformation `(f, g) ⟶ (ι, g)` with left leg `toImage`,
right leg `𝟙 Y'`, and base `𝟙 Y`. -/
def pullbackCospan {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    CospanTransform f g ι g :=
  CospanTransform.mk toImage (𝟙 Y') (𝟙 Y) (eqToIso fac ≪≫ (ρ_ f).symm)
    (λ_ g ≪≫ (ρ_ g).symm)

/-- The left vertex of `pullbackCospan f toImage ι g` is `toImage`. -/
theorem pullbackCospan_left {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    (pullbackCospan f toImage ι g).left = toImage :=
  sorry

/-- The right vertex of `pullbackCospan f toImage ι g` is the identity of `Y'`. -/
theorem pullbackCospan_right {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    (pullbackCospan f toImage ι g).right = 𝟙 Y' :=
  sorry

/-- The base vertex of `pullbackCospan f toImage ι g` is the identity of `Y`. -/
theorem pullbackCospan_base {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    (pullbackCospan f toImage ι g).base = 𝟙 Y :=
  sorry

/-- The comparison 1-morphism `X ×_Y Y' ⟶ Z ×_Y Y'` induced by a
scheme-theoretic image factorization of `f`. -/
def pullbackToImage {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} ι g :=
  TwoFibreProduct.map.{u + 1, u, u + 1, u} (pullbackCospan f toImage ι g)

/-- `pullbackToImage f toImage ι g` is the two-fibre-product map of
`pullbackCospan f toImage ι g`. -/
theorem pullbackToImage_eq {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    pullbackToImage f toImage ι g =
      TwoFibreProduct.map.{u + 1, u, u + 1, u} (pullbackCospan f toImage ι g) :=
  sorry

/-- The induced map commutes with the first projection up to the canonical
2-isomorphism, recovering `toImage` on the image factor. -/
def pullbackToImage_fstIso {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    pullbackToImage f toImage ι g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} ι g ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g ≫ toImage :=
  TwoFibreProduct.map.fstIso (pullbackCospan f toImage ι g)

/-- The induced map commutes with the second projection up to the canonical
2-isomorphism. -/
def pullbackToImage_sndIso {S : Scheme.{u}} {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (g : Y' ⟶ Y) :
    pullbackToImage f toImage ι g ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g ≫ 𝟙 Y' :=
  TwoFibreProduct.map.sndIso (pullbackCospan f toImage ι g)

/-- Scheme-theoretic images of quasi-compact morphisms of algebraic stacks
commute with 2-fibre-product base change along a flat morphism. -/
instance of_twoFibreProduct_flat {S : Scheme.{u}}
    {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ι g)] :
    IsSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      (pullbackToImage f toImage ι g)
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g) :=
  sorry

/-- Existence of a scheme-theoretic image is preserved by 2-fibre-product
base change along a flat morphism, for a quasi-compact source morphism. -/
theorem hasSchemeTheoreticImage_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Y' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y']
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (hf : HasSchemeTheoreticImage f)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    HasSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- As closed substacks of `Y'`, a scheme-theoretic image of the base change
`X ×_Y Y' ⟶ Y'` agrees with `Z ×_Y Y'`. -/
theorem objectProperty_twoFibreProduct_eq {S : Scheme.{u}}
    {X Y Y' Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Y'] [AlgebraicStack Z]
    (f : X ⟶ Y) [QuasiCompact f] (g : Y' ⟶ Y) [Flat g]
    (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ι g)]
    {Z' : ClosedSubstack Y'}
    {toImage' : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g ⟶ Z'.Y}
    [IsSchemeTheoreticImage (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
      toImage' Z'.ι] :
    Z'.objectProperty =
      (toClosedSubstack (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)
        (pullbackToImage f toImage ι g)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} ι g)).objectProperty :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsSchemeTheoreticImage
