/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.CategoryOfElements
public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of a ringed site at a sheaf

This module owns the category-of-elements presentation of localization at an
arbitrary set-valued sheaf.  The localized structure ring is defined in
inverse-image form.  Its direct-image structure map is only the adjoint
transpose of that explicit identity map.  The resulting ringed-topos
morphism is bundled with the category-of-elements morphism of topoi and its
canonical coefficient-forgetful comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite.Localization.AtSheaf

section CategoryOfElements

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/-- Definition 18.21.2 (04J2): the category-of-elements presentation of the
localization of a ringed site at `F`. -/
@[stacks 04J2 "localized ringed site"]
abbrev site (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v)) :
    RingedSite.{max u v, v, max u v} :=
  RingedSite.ofRingSheaf (localizationTopology F)
    (SheafOfModules.Localization.AtSheaf.ring O F)

/-- Definition 18.21.2 (04J2): the inverse-image structure map of localization
at `F`; the localized structure ring was defined to be this inverse image. -/
@[stacks 04J2 "inverse-image structure map"]
abbrev inverseImageStructureMap
    (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v)) :
    ((localizationProjection F).sheafPushforwardContinuous
        RingCat.{max u v} (localizationTopology F) J).obj O ⟶
      (site O F).structureSheaf :=
  𝟙 _

section DirectImage

/-- Definition 18.21.2 (04J2): the direct-image structure map obtained by
transposing `inverseImageStructureMap` across the localization adjunction. -/
@[stacks 04J2 "direct-image structure map"]
abbrev structureMap
    (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    O ⟶
      ((localizationProjection F).sheafPushforwardCocontinuous
        RingCat.{max u v} (localizationTopology F) J).obj
          (site O F).structureSheaf :=
  ((localizationProjection F).sheafAdjunctionCocontinuous
    RingCat.{max u v} (localizationTopology F) J).homEquiv O
      (site O F).structureSheaf (inverseImageStructureMap O F)

/-- The adjoint transpose of `structureMap` is the identity inverse-image
structure map used to define the localized ring. -/
theorem structureMap_adjunct
    (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    (((localizationProjection F).sheafAdjunctionCocontinuous
      RingCat.{max u v} (localizationTopology F) J).homEquiv O
        (site O F).structureSheaf).symm (structureMap O F) =
      inverseImageStructureMap O F := sorry

/-- Forgetting ring structure commutes with category-of-elements direct image. -/
@[stacks 04J2 "forgetful comparison"]
noncomputable def toAmbientForgetIso
    (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
      (localizationProjection F).op.HasPointwiseRightKanExtension G]
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    (localizationProjection F).sheafPushforwardCocontinuous
          RingCat.{max u v} (localizationTopology F) J ⋙
        sheafCompose J (forget RingCat.{max u v}) ≅
      sheafCompose (localizationTopology F) (forget RingCat.{max u v}) ⋙
        (localizationMorphismOfTopoiIn F).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (localizationProjection F) (forget RingCat.{max u v})
      (localizationTopology F) J

/-- The direct-image presentation of category-of-elements localization preserves the canonical
internal-ring operations. -/
theorem toAmbient_isRingCompatible
    (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
      (localizationProjection F).op.HasPointwiseRightKanExtension G]
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    ToposHom.Direct.IsRingCompatible
      (X := site O F) (Y := RingedSite.ofRingSheaf J O)
      (localizationMorphismOfTopoiIn F)
      ((localizationProjection F).sheafPushforwardCocontinuous
        RingCat.{max u v} (localizationTopology F) J)
      (toAmbientForgetIso F) (structureMap O F) := sorry

/-- Lemma 18.21.1 (04IE) and Definition 18.21.2 (04J2): localization at `F`
as a morphism from the category-of-elements ringed topos to its ambient
ringed topos. -/
@[stacks 04IE "(1), canonical morphism",
  stacks 04J2 "ringed-topos localization"]
noncomputable def toAmbient
    (O : Sheaf J RingCat.{max u v}) (F : Sheaf J (Type v))
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ RingCat.{max u v},
      (localizationProjection F).op.HasPointwiseRightKanExtension G]
    [∀ G : F.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (localizationProjection F).op.HasPointwiseRightKanExtension G] :
    ToposHom (site O F) (RingedSite.ofRingSheaf J O) :=
  ToposHom.ofDirectImage
    (X := site O F) (Y := RingedSite.ofRingSheaf J O)
    (localizationMorphismOfTopoiIn F)
    ((localizationProjection F).sheafPushforwardCocontinuous
      RingCat.{max u v} (localizationTopology F) J)
    (toAmbientForgetIso F) (structureMap O F)
    (toAmbient_isRingCompatible O F)

end DirectImage

end CategoryOfElements

section SliceTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Lemma 18.21.1 (04IE): the underlying localized structure object in the
slice topos is `F ⨯ O ⟶ F`. -/
@[stacks 04IE "localized underlying structure"]
abbrev underlyingStructure (O : Sheaf J RingCat.{max u v})
    (F : Sheaf J (Type (max u v))) : Over F :=
  (Over.star F).obj
    ((sheafCompose J (forget RingCat.{max u v})).obj O)

end SliceTopos

section Representable

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}

/-- Lemma 18.21.3 (04J3): in a representable localization, the structure map
is the canonical map from a ring sheaf to the pushforward of its restriction
to the slice site. -/
@[stacks 04J3 "structure map"]
abbrev representableStructureMap
    (O : Sheaf J RingCat.{max u v}) (U : C) :
    O ⟶
      ((Over.star U).sheafPushforwardContinuous
        RingCat.{max u v} J (J.over U)).obj (O.over U) :=
  SheafOfModules.pushforwardOver U

end Representable

end RingedSite.Localization.AtSheaf
