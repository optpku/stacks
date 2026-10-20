module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeEmbedding
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Pushouts along thickenings and affine morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme pushout along a thickening and an affine morphism remains a pushout after embedding
schemes over the base into algebraic spaces. -/
theorem isPushout_ofOver_thickening_affine {S : Scheme.{u}} {X X' Y Y' : Over S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [AlgebraicGeometry.IsThickening i.left] [IsAffineHom f.left]
    (h : IsPushout i.left f.left i'.left g.left) :
    IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map f)
      ((schemeFunctor S).map i') ((schemeFunctor S).map g) := sorry

namespace PushoutAlongThickening

/-- A thickening and an affine morphism of algebraic spaces over `S` have a pushout in
the category of algebraic spaces over `S`. -/
instance instHasPushout {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] : HasPushout i f :=
  sorry

/-- The canonical morphism from the target of an affine morphism to the pushout along a
thickening is a thickening. -/
instance instInrIsThickening {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    IsThickening (pushout.inr i f) :=
  sorry

/-- In any pushout square of a thickening along an affine morphism, the morphism
`Y ⟶ Y'` is a thickening. -/
theorem isThickening_inr {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    [IsThickening i] [Affine f] (h : IsPushout i f i' g) : IsThickening g :=
  sorry

/-- In a pushout square of a thickening along an affine morphism, the morphism
`X' ⟶ Y'` is representable by schemes. -/
theorem relativelyRepresentable_inl {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    [IsThickening i] [Affine f] (h : IsPushout i f i' g) :
    yoneda.relativelyRepresentable i' :=
  sorry

end PushoutAlongThickening

end AlgebraicGeometry.AlgebraicSpace
