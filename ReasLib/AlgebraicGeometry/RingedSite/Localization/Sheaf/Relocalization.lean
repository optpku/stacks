module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements.Relocalization
public import ReasLib.CategoryTheory.Sites.Localization.Representable.Relocalization
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relocalization at a map of sheaves

A map `s : G ⟶ F` induces a functor between the two category-of-elements
sites.  This module packages its ring-valued direct image and structure map as
a morphism of ringed topoi.  It also owns the canonical invertible triangle
with the two localization morphisms to the ambient ringed topos.

The slice-topos pullback comparison remains as a low-level view; it is not the
owner of the relocalization morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.Localization

noncomputable section

universe u v

namespace RingedSite.Localization.AtSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section CategoryOfElements

variable (O : Sheaf J RingCat.{max u v})
variable {G F : Sheaf J (Type v)} (s : G ⟶ F)

/-- Lemma 18.21.4 (04J4): inverse image along category-of-elements
relocalization carries the localized structure ring at `F` to that at `G`. -/
@[stacks 04J4 "inverse-image structure comparison"]
noncomputable def relocalizationInverseImageStructureIso :
    ((relocalizationFunctor s).sheafPushforwardContinuous
      RingCat.{max u v} (localizationTopology G) (localizationTopology F)).obj
        (site O F).structureSheaf ≅
      (site O G).structureSheaf :=
  (Functor.sheafPushforwardContinuousComp'
    (relocalizationProjectionIso s) RingCat.{max u v}
      (localizationTopology G) (localizationTopology F) J).app O

section DirectImage

variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (relocalizationFunctor s).op.HasPointwiseRightKanExtension P]

/-- The direct-image structure map of category-of-elements relocalization,
adjoint to `relocalizationInverseImageStructureIso`. -/
@[stacks 04J4 "structure map"]
noncomputable def relocalizationStructureMap :
    (site O F).structureSheaf ⟶
      ((relocalizationFunctor s).sheafPushforwardCocontinuous
        RingCat.{max u v} (localizationTopology G) (localizationTopology F)).obj
          (site O G).structureSheaf :=
  ((relocalizationFunctor s).sheafAdjunctionCocontinuous
    RingCat.{max u v} (localizationTopology G) (localizationTopology F)).homEquiv
      (site O F).structureSheaf (site O G).structureSheaf
        (relocalizationInverseImageStructureIso O s).hom

/-- The adjoint transpose of the relocalization structure map is the
canonical inverse-image comparison of localized structure rings. -/
@[stacks 04J4 "structure-map adjunct"]
theorem relocalizationStructureMap_adjunct :
    (((relocalizationFunctor s).sheafAdjunctionCocontinuous
      RingCat.{max u v} (localizationTopology G) (localizationTopology F)).homEquiv
        (site O F).structureSheaf (site O G).structureSheaf).symm
          (relocalizationStructureMap O s) =
      (relocalizationInverseImageStructureIso O s).hom := sorry

section ToposMorphism

variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (relocalizationFunctor s).op.HasPointwiseRightKanExtension P]

/-- Forgetting ring structure commutes with category-of-elements
relocalization direct image. -/
noncomputable def relocalizationForgetIso :
    (relocalizationFunctor s).sheafPushforwardCocontinuous
          RingCat.{max u v} (localizationTopology G) (localizationTopology F) ⋙
        sheafCompose (localizationTopology F) (forget RingCat.{max u v}) ≅
      sheafCompose (localizationTopology G) (forget RingCat.{max u v}) ⋙
        (relocalizationMorphismOfTopoiIn s).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (relocalizationFunctor s) (forget RingCat.{max u v})
      (localizationTopology G) (localizationTopology F)

/-- The direct-image presentation of category-of-elements relocalization preserves the canonical
internal-ring operations. -/
theorem relocalization_isRingCompatible :
    ToposHom.Direct.IsRingCompatible
      (X := site O G) (Y := site O F)
      (relocalizationMorphismOfTopoiIn s)
      ((relocalizationFunctor s).sheafPushforwardCocontinuous
        RingCat.{max u v} (localizationTopology G) (localizationTopology F))
      (relocalizationForgetIso s) (relocalizationStructureMap O s) := sorry

/-- Lemma 18.21.4 (04J4): the morphism of ringed topoi induced by
`s : G ⟶ F` between the category-of-elements localizations. -/
@[stacks 04J4 "ringed-topos relocalization"]
noncomputable def relocalization : ToposHom (site O G) (site O F) :=
  ToposHom.ofDirectImage
    (X := site O G) (Y := site O F)
    (relocalizationMorphismOfTopoiIn s)
    ((relocalizationFunctor s).sheafPushforwardCocontinuous
      RingCat.{max u v} (localizationTopology G) (localizationTopology F))
    (relocalizationForgetIso s) (relocalizationStructureMap O s)
    (relocalization_isRingCompatible O s)

section Triangle

variable [∀ P : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (localizationProjection F).op.HasPointwiseRightKanExtension P]
variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
  (localizationProjection G).op.HasPointwiseRightKanExtension P]
variable [∀ P : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (localizationProjection F).op.HasPointwiseRightKanExtension P]
variable [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
  (localizationProjection G).op.HasPointwiseRightKanExtension P]

/-- The composite from localization at `G`, through localization at `F`,
to the ambient ringed topos. -/
@[stacks 04J4 "triangle composite"]
noncomputable abbrev relocalizationToAmbient (s : G ⟶ F) :
    ToposHom (site O G) (ofRingSheaf J O) :=
  ToposHom.comp (X := site O G) (Y := site O F)
    (Z := ofRingSheaf J O) (relocalization O s) (toAmbient O F)

/-- The explicit direct-image isomorphism in the category-of-elements
relocalization triangle. -/
@[stacks 04J4 "direct-image triangle comparison"]
noncomputable def relocalizationTrianglePushforwardIso :
    (relocalizationToAmbient O s).toTopos.pushforward ≅
      (toAmbient O G).toTopos.pushforward :=
  Functor.sheafPushforwardCocontinuousComp'
    (localizationTopology G) (localizationTopology F) J
      (relocalizationFunctor s) (localizationProjection F)
        (relocalizationProjectionIso s)

/-- Compatibility of the relocalization triangle comparison with the
ring-valued direct-image structure maps. -/
@[stacks 04J4 "triangle compatibility"]
theorem relocalizationTriangle_comm :
    (relocalizationToAmbient O s).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (relocalizationTrianglePushforwardIso O s).hom).app
            (site O G).structureSheaf =
      (toAmbient O G).directStructureMap := sorry

/-- Lemma 18.21.4 (04J4): relocalization followed by localization to the
ambient ringed topos is canonically `2`-isomorphic to localization at `G`. -/
@[stacks 04J4 "ringed-topos triangle"]
noncomputable def relocalizationTriangle :
    ToposHom.TwoIso (X := site O G) (Y := ofRingSheaf J O)
      (relocalizationToAmbient O s)
      (toAmbient O G) where
  homIso := relocalizationTrianglePushforwardIso O s
  comm := relocalizationTriangle_comm O s

end Triangle

end ToposMorphism

end DirectImage

end CategoryOfElements

section SliceTopos

variable [J.HasSheafCompose (forget RingCat.{max u v})]

/-- Lemma 18.21.4 (04J4): pullback along `s : G ⟶ F` carries the
localized underlying structure object at `F` to the one at `G`. -/
@[stacks 04J4]
noncomputable abbrev underlyingStructurePullbackIso
    (O : Sheaf J RingCat.{max u v})
    {G F : Sheaf J (Type (max u v))} (s : G ⟶ F) :
    (Over.pullback s).obj (underlyingStructure O F) ≅
      underlyingStructure O G :=
  (Over.starPullbackIsoStar s).app
    ((sheafCompose J (forget RingCat.{max u v})).obj O)

end SliceTopos

end RingedSite.Localization.AtSheaf

namespace CategoryTheory.GrothendieckTopology.RepresentableLocalization

end CategoryTheory.GrothendieckTopology.RepresentableLocalization
