module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.CategoryTheory.Adjunction.LeftExact
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback

/-!
# Morphisms of étale topoi of algebraic spaces

The morphism of sites `spacesEtalePullback f` induces a morphism of topoi of étale
sheaves of algebraic spaces. Transport along the restriction-extension equivalence yields the
associated morphism of small étale topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Sheaves of types in universe `u + 1` on the étale site of algebraic spaces over `X` admit
weak sheafification. -/
instance hasWeakSheafify_spacesEtaleTopology (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) (Type (u + 1)) :=
  (plusPlusAdjunction (spacesEtaleTopology X) (Type (u + 1))).isRightAdjoint

/-- Sheaves of types in universe `u + 1` on the small étale site of `X` admit weak
sheafification. -/
instance hasWeakSheafify_smallEtaleTopology (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) (Type (u + 1)) :=
  (plusPlusAdjunction (smallEtaleTopology X) (Type (u + 1))).isRightAdjoint

/-- The opposite of `spacesEtalePullback f` has left Kan extensions on presheaves of types. -/
instance spacesEtalePullback_op_hasLeftKanExtension {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P : (spacesEtaleSite Y)ᵒᵖ ⥤ Type (u + 1)) :
    (spacesEtalePullback f).op.HasLeftKanExtension P :=
  inferInstance

/-- Sheaf pullback along `spacesEtalePullback f` preserves finite limits. -/
instance spacesEtalePullback_sheafPullback_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    PreservesFiniteLimits
      ((spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X)) :=
  sorry

/-- The morphism of topoi `Sh(X_spaces,étale) ⟶ Sh(Y_spaces,étale)` induced by
`spacesEtalePullback f`. -/
noncomputable def spacesEtaleMorphismOfTopoi {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  IsMorphismOfSites.toMorphismOfTopoiIn (spacesEtalePullback f)

/-- `spacesEtaleMorphismOfTopoi f` is the topos morphism of the site morphism
`spacesEtalePullback f`. -/
theorem spacesEtaleMorphismOfTopoi_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    spacesEtaleMorphismOfTopoi f =
      IsMorphismOfSites.toMorphismOfTopoiIn (spacesEtalePullback f) :=
  rfl

/-- The inverse image of `spacesEtaleMorphismOfTopoi f` is sheaf pullback along
`spacesEtalePullback f`. -/
theorem spacesEtaleMorphismOfTopoi_inverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (spacesEtaleMorphismOfTopoi f).inverseImage =
      (spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- The direct image of `spacesEtaleMorphismOfTopoi f` is continuous sheaf pushforward along
`spacesEtalePullback f`. -/
theorem spacesEtaleMorphismOfTopoi_pushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (spacesEtaleMorphismOfTopoi f).pushforward =
      (spacesEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X) :=
  rfl

/-- Cocontinuous direct image along `smallEtaleToSpaces X` on sheaves of types. -/
noncomputable abbrev smallEtaleInclusionDirectImage (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- `smallEtaleInclusionDirectImage X` is cocontinuous sheaf pushforward of
`smallEtaleToSpaces X`. -/
theorem smallEtaleInclusionDirectImage_eq (X : AlgebraicSpace S) :
    smallEtaleInclusionDirectImage X =
      (smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- The morphism of topoi `Sh(X_étale) ⟶ Sh(X_spaces,étale)` presented by the comparison
equivalence between extension and restriction. -/
noncomputable def smallEtaleInclusionMorphismOfTopoi (X : AlgebraicSpace S) :
    MorphismOfTopoiIn (spacesEtaleTopology X) (smallEtaleTopology X) where
  inverseImageFunctor := LeftExactFunctor.of (smallEtalePresentationRestriction X)
  pushforward := smallEtaleInclusionDirectImage X
  adjunction := (smallEtalePresentationEquivalence X).symm.toAdjunction

/-- The inverse image of `smallEtaleInclusionMorphismOfTopoi X` is the inverse of the
cocontinuous direct image. -/
theorem smallEtaleInclusionMorphismOfTopoi_inverseImage (X : AlgebraicSpace S) :
    (smallEtaleInclusionMorphismOfTopoi X).inverseImage =
      (smallEtalePresentationRestriction X) :=
  rfl

/-- The morphism of topoi `Sh(X_spaces,étale) ⟶ Sh(X_étale)` inverse to
`smallEtaleInclusionMorphismOfTopoi X`. -/
noncomputable def smallEtaleInclusionInverseMorphismOfTopoi (X : AlgebraicSpace S) :
    MorphismOfTopoiIn (smallEtaleTopology X) (spacesEtaleTopology X) where
  inverseImageFunctor := LeftExactFunctor.of (smallEtaleInclusionDirectImage X)
  pushforward := (smallEtalePresentationRestriction X)
  adjunction := (smallEtalePresentationEquivalence X).toAdjunction

/-- The inverse image of `smallEtaleInclusionInverseMorphismOfTopoi X` is the cocontinuous
direct image. -/
theorem smallEtaleInclusionInverseMorphismOfTopoi_inverseImage (X : AlgebraicSpace S) :
    (smallEtaleInclusionInverseMorphismOfTopoi X).inverseImage =
      smallEtaleInclusionDirectImage X :=
  rfl

/-- The morphism of small étale topoi `f_small : Sh(X_étale) ⟶ Sh(Y_étale)` obtained by
transporting `spacesEtaleMorphismOfTopoi f` along the restriction-extension equivalences. -/
noncomputable def smallEtaleMorphismOfTopoi {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) :=
  (smallEtaleInclusionInverseMorphismOfTopoi Y).comp
    ((spacesEtaleMorphismOfTopoi f).comp (smallEtaleInclusionMorphismOfTopoi X))

/-- `smallEtaleMorphismOfTopoi f` is the conjugate of `spacesEtaleMorphismOfTopoi f` by the
restriction-extension equivalences. -/
theorem smallEtaleMorphismOfTopoi_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    smallEtaleMorphismOfTopoi f =
      (smallEtaleInclusionInverseMorphismOfTopoi Y).comp
        ((spacesEtaleMorphismOfTopoi f).comp (smallEtaleInclusionMorphismOfTopoi X)) :=
  rfl

/-- The inverse image of `smallEtaleMorphismOfTopoi f` is the composite of the inverse images
of the comparison and spaces-site morphisms of topoi. -/
theorem smallEtaleMorphismOfTopoi_inverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (smallEtaleMorphismOfTopoi f).inverseImage =
      (smallEtaleInclusionInverseMorphismOfTopoi Y).inverseImage ⋙
        ((spacesEtaleMorphismOfTopoi f).comp
          (smallEtaleInclusionMorphismOfTopoi X)).inverseImage :=
  rfl

/-- The direct image of `smallEtaleMorphismOfTopoi f` is the composite of the direct images
of the comparison and spaces-site morphisms of topoi. -/
theorem smallEtaleMorphismOfTopoi_pushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (smallEtaleMorphismOfTopoi f).pushforward =
      ((spacesEtaleMorphismOfTopoi f).comp
          (smallEtaleInclusionMorphismOfTopoi X)).pushforward ⋙
        (smallEtaleInclusionInverseMorphismOfTopoi Y).pushforward :=
  rfl

/-- The opposite of a composite spaces étale pullback has left Kan extensions on presheaves of
types. -/
instance spacesEtalePullback_comp_op_hasLeftKanExtension {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (P : (spacesEtaleSite Z)ᵒᵖ ⥤ Type (u + 1)) :
    (spacesEtalePullback g ⋙ spacesEtalePullback f).op.HasLeftKanExtension P :=
  inferInstance

/-- Inverse images of spaces étale topos morphisms compose up to the canonical isomorphism of
chosen fibre products. -/
noncomputable def spacesEtaleMorphismOfTopoiComp {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
      ((spacesEtaleMorphismOfTopoi g).comp (spacesEtaleMorphismOfTopoi f)).inverseImage :=
  (Functor.sheafPullbackComp' (spacesEtaleTopology Z) (spacesEtaleTopology Y)
      (spacesEtaleTopology X) (spacesEtalePullback g) (spacesEtalePullback f)
      (spacesEtalePullbackComp f g).symm).symm

/-- `spacesEtaleMorphismOfTopoiComp` is the inverse-image comparison of
`Functor.sheafPullbackComp'`. -/
theorem spacesEtaleMorphismOfTopoiComp_eq {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    spacesEtaleMorphismOfTopoiComp f g =
      (Functor.sheafPullbackComp' (spacesEtaleTopology Z) (spacesEtaleTopology Y)
        (spacesEtaleTopology X) (spacesEtalePullback g) (spacesEtalePullback f)
        (spacesEtalePullbackComp f g).symm).symm :=
  rfl

/-- Inverse images of small étale topos morphisms compose up to conjugation of
`spacesEtaleMorphismOfTopoiComp` by the restriction-extension equivalences. -/
noncomputable def smallEtaleMorphismOfTopoiComp {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
      ((smallEtaleMorphismOfTopoi g).comp (smallEtaleMorphismOfTopoi f)).inverseImage :=
  let iY := smallEtaleInclusionDirectImage Y
  let sF := (spacesEtaleMorphismOfTopoi f).inverseImage
  let sG := (spacesEtaleMorphismOfTopoi g).inverseImage
  let mid : sG ⋙ sF ≅ sG ⋙ (smallEtalePresentationRestriction Y) ⋙ iY ⋙ sF :=
    Functor.isoWhiskerLeft sG
      ((Functor.leftUnitor sF).symm ≪≫
        Functor.isoWhiskerRight (smallEtalePresentationEquivalence Y).counitIso.symm sF ≪≫
        Functor.associator (smallEtalePresentationRestriction Y) iY sF)
  Functor.isoWhiskerLeft (smallEtaleInclusionDirectImage Z)
    (Functor.isoWhiskerRight (spacesEtaleMorphismOfTopoiComp f g ≪≫ mid)
      (smallEtalePresentationRestriction X))

/-- `smallEtaleMorphismOfTopoiComp` conjugates `spacesEtaleMorphismOfTopoiComp` by the
restriction-extension equivalences. -/
theorem smallEtaleMorphismOfTopoiComp_eq {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleMorphismOfTopoiComp f g =
      let iY := smallEtaleInclusionDirectImage Y
      let sF := (spacesEtaleMorphismOfTopoi f).inverseImage
      let sG := (spacesEtaleMorphismOfTopoi g).inverseImage
      let mid : sG ⋙ sF ≅ sG ⋙ (smallEtalePresentationRestriction Y) ⋙ iY ⋙ sF :=
        Functor.isoWhiskerLeft sG
          ((Functor.leftUnitor sF).symm ≪≫
            Functor.isoWhiskerRight (smallEtalePresentationEquivalence Y).counitIso.symm sF ≪≫
            Functor.associator (smallEtalePresentationRestriction Y) iY sF)
      Functor.isoWhiskerLeft (smallEtaleInclusionDirectImage Z)
        (Functor.isoWhiskerRight (spacesEtaleMorphismOfTopoiComp f g ≪≫ mid)
          (smallEtalePresentationRestriction X)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
