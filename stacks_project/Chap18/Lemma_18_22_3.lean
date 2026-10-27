/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square
import StacksCheckRecall

/-!
# Lemma 18.22.3

Compatibility facade for a localized morphism defined by a map `F ⟶ f⁻¹G` and for its
functorial base-change square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY w uA vA uB vB uC vC uD vD

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]
variable (f : Hom X Y)
variable [PreservesFiniteLimits
  (f.sheafPullback (A := Type w))]
variable {G G' : Sheaf Y.siteTopology (Type w)}
variable {F F' : Sheaf X.siteTopology (Type w)}

/- Lemma 18.22.3 (2) (04J8): commutativity at the ringed-topos level is represented by a
chosen invertible `2`-cell, rather than only by a proposition that one exists. -/
@[stacks 04J8 "(2), ringed square"]
#check (RingedSite.ToposHom.CommSquare :
  ∀ (A : RingedSite.{uA, vA, w}) (B : RingedSite.{uB, vB, w})
    (C : RingedSite.{uC, vC, w}) (D : RingedSite.{uD, vD, w})
    [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
    [D.siteTopology.HasSheafCompose (forget RingCat.{w})],
    Type (max uA vA uB vB uC vC uD vD (w + 1)))

variable (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G)

/- Lemma 18.22.3 (1) (04J8): the inverse image of the morphism defined by
`s : F ⟶ f⁻¹G` is localized inverse image followed by pullback along `s`. -/
@[stacks 04J8 "(1), inverse image"]
#check (CategoryTheory.Functor.comp (f.toMorphismOfTopoi.localization G).inverseImage
    (Over.pullback s) : Over G ⥤ Over F)

/- Lemma 18.22.3 (1) (04J8): the corresponding inverse-image-form map on forgotten structure
sheaves. -/
@[stacks 04J8 "(1), structure map"]
#check (RingedSite.Hom.localizedUnderlyingInverseImageMap f s :
  ((f.toMorphismOfTopoi.localization G).inverseImage ⋙ Over.pullback s).obj
      ((Over.star G).obj (underlyingStructureSheaf Y)) ⟶
    (Over.star F).obj (underlyingStructureSheaf X))

variable (b : G' ⟶ G) (a : F' ⟶ F)
variable (s' : F' ⟶ f.toMorphismOfTopoi.inverseImage.obj G')
variable (h : s' ≫ f.toMorphismOfTopoi.inverseImage.map b = a ≫ s)

/- Lemma 18.22.3 (2) (04J8): a commuting square of localization parameters induces the
canonical base-change isomorphism of inverse-image functors. -/
@[stacks 04J8 "(2), inverse image"]
#check (CategoryTheory.LeftExactAdjunction.Localization.inverseImageBaseChangeIso
    f.toMorphismOfTopoi b a s s' h :
  Over.pullback b ⋙ (f.toMorphismOfTopoi.localization G').inverseImage ⋙ Over.pullback s' ≅
    (f.toMorphismOfTopoi.localization G).inverseImage ⋙ Over.pullback s ⋙ Over.pullback a)

/- Lemma 18.22.3 (2) (04J8): the base-change comparison respects the localized structure maps. -/
@[stacks 04J8 "(2), structure map"]
#check (RingedSite.Hom.localizedUnderlyingInverseImageMap_commSq f b a s s' h :
  CommSq
    ((LeftExactAdjunction.Localization.inverseImageBaseChangeIso
        f.toMorphismOfTopoi b a s s' h).hom.app
      ((Over.star G).obj (underlyingStructureSheaf Y)))
    (((f.toMorphismOfTopoi.localization G').inverseImage ⋙ Over.pullback s').map
        (((Over.starPullbackIsoStar b).app (underlyingStructureSheaf Y)).hom) ≫
      f.localizedUnderlyingInverseImageMap s')
    ((Over.pullback a).map (f.localizedUnderlyingInverseImageMap s) ≫
      ((Over.starPullbackIsoStar a).app (underlyingStructureSheaf X)).hom)
    (𝟙 ((Over.star F').obj (underlyingStructureSheaf X))))

end RingedSite.Hom
