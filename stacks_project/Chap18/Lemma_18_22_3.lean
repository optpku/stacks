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

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]
variable (f : Hom X Y)
variable [PreservesFiniteLimits
  (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]
variable {G G' : Sheaf Y.siteTopology (Type w)}
variable {F F' : Sheaf X.siteTopology (Type w)}

/- Lemma 18.22.3 (2) (04J8): commutativity at the ringed-topos level is represented by a
chosen invertible `2`-cell, rather than only by a proposition that one exists. -/
@[stacks 04J8 "(2), ringed square"]
#check @RingedSite.ToposHom.CommSquare

/- Lemma 18.22.3 (1) (04J8): the inverse image of the morphism defined by
`s : F ⟶ f⁻¹G` is localized inverse image followed by pullback along `s`. -/
@[stacks 04J8 "(1), inverse image"]
#check (fun (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) ↦
  (f.toMorphismOfTopoi.localization G).inverseImage ⋙ Over.pullback s)

/- Lemma 18.22.3 (1) (04J8): the corresponding inverse-image-form map on forgotten structure
sheaves. -/
@[stacks 04J8 "(1), structure map"]
#check (fun (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G) ↦
  f.localizedUnderlyingInverseImageMap s)

/- Lemma 18.22.3 (2) (04J8): a commuting square of localization parameters induces the
canonical base-change isomorphism of inverse-image functors. -/
@[stacks 04J8 "(2), inverse image"]
#check (fun (b : G' ⟶ G) (a : F' ⟶ F)
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G)
    (s' : F' ⟶ f.toMorphismOfTopoi.inverseImage.obj G')
    (h : s' ≫ f.toMorphismOfTopoi.inverseImage.map b = a ≫ s) ↦
  LeftExactAdjunction.Localization.inverseImageBaseChangeIso
    f.toMorphismOfTopoi b a s s' h)

/- Lemma 18.22.3 (2) (04J8): the base-change comparison respects the localized structure maps. -/
@[stacks 04J8 "(2), structure map"]
#check (fun (b : G' ⟶ G) (a : F' ⟶ F)
    (s : F ⟶ f.toMorphismOfTopoi.inverseImage.obj G)
    (s' : F' ⟶ f.toMorphismOfTopoi.inverseImage.obj G')
    (h : s' ≫ f.toMorphismOfTopoi.inverseImage.map b = a ≫ s) ↦
  f.localizedUnderlyingInverseImageMap_commSq b a s s' h)

end RingedSite.Hom
