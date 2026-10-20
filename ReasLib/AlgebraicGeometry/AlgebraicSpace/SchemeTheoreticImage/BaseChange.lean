module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage

/-!
# Base-change comparison maps for scheme-theoretic images

A scheme-theoretic image factorization induces concrete comparison maps from
the pullback of its source to the pullback of its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- The comparison `X ×_Y V ⟶ Z ×_Y V` induced by a scheme-theoretic image
factorization of `f`, as a morphism of chosen pullbacks. -/
def pullbackToImage {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] : pullback f φ ⟶ pullback ι φ :=
  pullback.lift (pullback.fst f φ ≫ toImage) (pullback.snd f φ) (by
    rw [Category.assoc,
      IsSchemeTheoreticImage.fac (f := f) (toImage := toImage) (ι := ι)]
    exact pullback.condition)

/-- `pullbackToImage f toImage ι φ` projects to `toImage` on the first factor. -/
theorem pullbackToImage_fst {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] :
    pullbackToImage f toImage ι φ ≫ pullback.fst ι φ =
      pullback.fst f φ ≫ toImage :=
  sorry

/-- `pullbackToImage f toImage ι φ` projects to `pullback.snd f φ` on the second
factor. -/
theorem pullbackToImage_snd {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] :
    pullbackToImage f toImage ι φ ≫ pullback.snd ι φ = pullback.snd f φ :=
  sorry

/-- The comparison `X ×_Y V ⟶ Z ×_Y V` into the closed inverse image of `ι`
along a morphism `φ : V ⟶ Y`. -/
def pullbackToInverseImage {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] : pullback f φ ⟶ inverseImage φ ι :=
  (inverseImage_isPullback φ ι).lift (pullback.snd f φ)
    (pullback.fst f φ ≫ toImage) (by
      symm
      rw [Category.assoc,
        IsSchemeTheoreticImage.fac (f := f) (toImage := toImage) (ι := ι)]
      exact pullback.condition)

/-- `pullbackToInverseImage f toImage ι φ` composes to `pullback.snd f φ` along
the closed inclusion of `inverseImage φ ι`. -/
theorem pullbackToInverseImage_ι {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] :
    pullbackToInverseImage f toImage ι φ ≫ inverseImageι φ ι =
      pullback.snd f φ :=
  sorry

/-- `pullbackToInverseImage f toImage ι φ` composes to
`pullback.fst f φ ≫ toImage` along the comparison into `Z`. -/
theorem pullbackToInverseImage_to {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] :
    pullbackToInverseImage f toImage ι φ ≫ inverseImageTo φ ι =
      pullback.fst f φ ≫ toImage :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
