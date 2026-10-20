module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RepresentablePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `f : X ⟶ Y` is an integral, universally injective, and surjective morphism
of algebraic spaces, base change along `f` induces an equivalence from the
spaces-étale site of `Y` to the spaces-étale site of `X`. -/
instance spacesEtalePullback.isEquivalence
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (spacesEtalePullback f).IsEquivalence := sorry

/-- An integral morphism of algebraic spaces is relatively representable. -/
theorem IsIntegralHom.relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] : yoneda.relativelyRepresentable f :=
  sorry

/-- An object of the spaces-étale site is a scheme if and only if its base change
along an integral, universally injective, surjective morphism is a scheme. -/
theorem spacesEtalePullback.obj_isScheme_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (V : spacesEtaleSite Y) :
    IsScheme V.left ↔ IsScheme ((spacesEtalePullback f).obj V).left :=
  sorry

/-- An object of the spaces-étale site is affine if and only if its base change
along an integral, universally injective, surjective morphism is affine. -/
theorem spacesEtalePullback.obj_isAffine_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (V : spacesEtaleSite Y) :
    IsAffine V.left ↔ IsAffine ((spacesEtalePullback f).obj V).left :=
  sorry

/-- Base change along an integral, universally injective, surjective morphism
of algebraic spaces induces an equivalence of small étale sites. -/
instance smallEtalePullback.isEquivalence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (smallEtalePullback f (IsIntegralHom.relativelyRepresentable f)).IsEquivalence :=
  sorry

/-- Base change along an integral morphism sends affine objects of the small
étale site to affine objects of the small étale site. -/
theorem affineEtaleObjects.map_smallEtalePullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]
    (hf : yoneda.relativelyRepresentable f) (U : affineEtaleSite Y) :
    affineEtaleObjects X ((affineEtaleInclusion Y ⋙ smallEtalePullback f hf).obj U) :=
  sorry

/-- Base change along an integral morphism as a functor of affine étale sites. -/
def affineEtalePullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIntegralHom f] (hf : yoneda.relativelyRepresentable f) :
    affineEtaleSite Y ⥤ affineEtaleSite X :=
  (affineEtaleObjects X).lift (affineEtaleInclusion Y ⋙ smallEtalePullback f hf)
    (affineEtaleObjects.map_smallEtalePullback f hf)

/-- Affine étale pullback commutes with the inclusions into the small étale sites
up to the canonical natural isomorphism. -/
def affineEtalePullback.comp_inclusion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] (hf : yoneda.relativelyRepresentable f) :
    affineEtalePullback f hf ⋙ affineEtaleInclusion X ≅
      affineEtaleInclusion Y ⋙ smallEtalePullback f hf :=
  (affineEtaleObjects X).liftCompιIso (affineEtaleInclusion Y ⋙ smallEtalePullback f hf)
    (affineEtaleObjects.map_smallEtalePullback f hf)

/-- Base change along an integral, universally injective, surjective morphism
of algebraic spaces induces an equivalence of affine étale sites. -/
instance affineEtalePullback.isEquivalence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    (affineEtalePullback f (IsIntegralHom.relativelyRepresentable f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
