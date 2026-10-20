module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Basic
public import ReasLib.CategoryTheory.Adjunction.LeftExact.Localization
public import ReasLib.CategoryTheory.Limits.OverPost
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of morphisms between site-presented ringed topoi

This module specializes slice localization of a left-exact adjunction to the underlying sheaves of
the structure sheaves of a ringed-site morphism.  The underlying categorical base change remains
owned by `LeftExactAdjunction.Localization`; only the ringed specialization lives here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]

section DirectImage

variable (f : Hom X Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]

/-- Lemma 18.22.1 (04IF), ringed layer: the underlying direct-image-form structure map of the
morphism localized at `G`. -/
@[stacks 04IF "(structure map)"]
noncomputable def localizedUnderlyingDirectImageMap
    (G : Sheaf Y.siteTopology (Type w)) :
    (Over.star G).obj (underlyingStructureSheaf Y) ⟶
      (f.toMorphismOfTopoi.localization G).pushforward.obj
        ((Over.star (f.toMorphismOfTopoi.inverseImage.obj G)).obj
          (underlyingStructureSheaf X)) :=
  (Over.star G).map f.underlyingDirectImageMap ≫
    ((f.toMorphismOfTopoi.localization_pushforwardStarIso G).app
      (underlyingStructureSheaf X)).inv

end DirectImage

section InverseImage

variable (f : Hom X Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]

/-- The canonical inverse-image comparison in the ambient square for localization along
`s : F ⟶ f⁻¹G`.  It compares localization followed by pullback along `s` with applying
the ambient inverse image and then forming the slice-product object over `F`.

The isomorphism is assembled from explicit product and pullback comparisons; it does not choose
an inverse from a deferred `IsIso` proof. -/
@[stacks 04J8 "ambient inverse-image comparison"]
noncomputable def localizedAmbientIso
    {G : Sheaf Y.siteTopology (Type w)}
    {F : Sheaf X.siteTopology (Type w)}
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) :
    Over.star G ⋙ (f.toMorphismOfTopoi.localization G).inverseImage ⋙
        Over.pullback s ≅
      f.toMorphismOfTopoi.inverseImage ⋙ Over.star F :=
  Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso
        f.toMorphismOfTopoi.inverseImage G)
      (Over.pullback s) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft f.toMorphismOfTopoi.inverseImage
      (Over.starPullbackIsoStar s)

/-- The source transport comparing localized inverse image with pullback of the slice-product
structure sheaf. -/
noncomputable def localizedInverseImageSourceIso
    {G : Sheaf Y.siteTopology (Type w)}
    {F : Sheaf X.siteTopology (Type w)}
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) :
    ((f.toMorphismOfTopoi.localization G).inverseImage ⋙ Over.pullback s).obj
        ((Over.star G).obj (underlyingStructureSheaf Y)) ≅
      (Over.star (f.toMorphismOfTopoi.inverseImage.obj G) ⋙ Over.pullback s).obj
        (f.toMorphismOfTopoi.inverseImage.obj (underlyingStructureSheaf Y)) :=
  (Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso f.toMorphismOfTopoi.inverseImage G)
      (Over.pullback s)).app (underlyingStructureSheaf Y)

/-- Lemma 18.22.3 (04J8), ringed layer: the inverse-image-form map on underlying structure
sheaves for localization along `s : F ⟶ f⁻¹G`. -/
@[stacks 04J8 "(structure map)"]
noncomputable def localizedUnderlyingInverseImageMap
    {G : Sheaf Y.siteTopology (Type w)}
    {F : Sheaf X.siteTopology (Type w)}
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) :
    ((f.toMorphismOfTopoi.localization G).inverseImage ⋙ Over.pullback s).obj
        ((Over.star G).obj (underlyingStructureSheaf Y)) ⟶
      (Over.star F).obj (underlyingStructureSheaf X) :=
  (localizedInverseImageSourceIso f s).hom ≫
    ((Over.starPullbackIsoStar s).app
      (f.toMorphismOfTopoi.inverseImage.obj (underlyingStructureSheaf Y))).hom ≫
    (Over.star F).map f.underlyingInverseImageMap

/-- The ambient inverse-image comparison carries the ambient structure map to the localized
underlying structure map.  This is the structure-sheaf compatibility missing from a merely
functor-level localization square. -/
@[stacks 04J8 "ambient structure compatibility"]
theorem localizedAmbientIso_structure
    {G : Sheaf Y.siteTopology (Type w)}
    {F : Sheaf X.siteTopology (Type w)}
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) :
    (localizedAmbientIso f s).hom.app (underlyingStructureSheaf Y) ≫
        (Over.star F).map f.underlyingInverseImageMap =
      localizedUnderlyingInverseImageMap f s := sorry

/-- Lemma 18.22.3 (04J8), functoriality: the base-change isomorphism associated to a commuting
square is compatible with the localized underlying structure maps. -/
@[stacks 04J8 "(base change)"]
theorem localizedUnderlyingInverseImageMap_commSq
    {G G' : Sheaf Y.siteTopology (Type w)}
    {F F' : Sheaf X.siteTopology (Type w)}
    (b : G' ⟶ G) (a : F' ⟶ F)
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G)
    (s' : F' ⟶ f.toMorphismOfTopoi.inverseImage.obj G')
    (h : s' ≫ f.toMorphismOfTopoi.inverseImage.map b = a ≫ s) :
    CommSq
      ((LeftExactAdjunction.Localization.inverseImageBaseChangeIso
          f.toMorphismOfTopoi b a s s' h).hom.app
        ((Over.star G).obj (underlyingStructureSheaf Y)))
      (((f.toMorphismOfTopoi.localization G').inverseImage ⋙ Over.pullback s').map
          (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
        localizedUnderlyingInverseImageMap f s')
      ((Over.pullback a).map (localizedUnderlyingInverseImageMap f s) ≫
        ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom)
      (𝟙 ((Over.star F').obj (underlyingStructureSheaf X))) := sorry

end InverseImage

end RingedSite.Hom
