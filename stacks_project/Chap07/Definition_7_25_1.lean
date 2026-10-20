module

public import ReasLib.CategoryTheory.Sites.Localization.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)

variable [HasSheafify (J.over U) (Type (max u v))]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.forget U).op.HasPointwiseRightKanExtension F]

/- Definition 7.25.1 (2): the morphism of topoi `J.localizationMorphism U` from `Sh(J.over U)`
to `Sh(J)` is the localization morphism. -/
@[stacks 00Y0] #check (CategoryTheory.GrothendieckTopology.localizationMorphism J U :
  MorphismOfTopoiIn J (J.over U))

/- Definition 7.25.1 (1): the site `J.over U` is the localization of the site `J` at the
object `U`. -/
@[stacks 00Y0] #check (CategoryTheory.GrothendieckTopology.over J U :
  GrothendieckTopology (Over U))

/- Definition 7.25.1 (3): the functor `(J.localizationMorphism U).pushforward` is the
direct image functor. -/
@[stacks 00Y0] #check (CategoryTheory.LeftExactAdjunction.pushforward
  (CategoryTheory.GrothendieckTopology.localizationMorphism J U) :
  Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf J (Type (max u v)))

/- Definition 7.25.1 (4): for a sheaf `F` on `J`, the sheaf
`(J.localizationMorphism U).inverseImage.obj F` is the restriction of `F` to `J.over U`. -/
@[stacks 00Y0] #check (CategoryTheory.LeftExactAdjunction.inverseImage
  (CategoryTheory.GrothendieckTopology.localizationMorphism J U) :
  Sheaf J (Type (max u v)) ⥤ Sheaf (J.over U) (Type (max u v)))

variable [∀ G : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension G]
variable [HasWeakSheafify J (Type (max u v))]

/- Definition 7.25.1 (5): for a sheaf `G` on `J.over U`, the sheaf obtained by
`(Over.forget U).sheafPullback (Type (max u v)) (J.over U) J` is the extension of `G` by the
empty set. -/
@[stacks 00Y0] #check (CategoryTheory.Functor.sheafPullback
  (Over.forget U) (Type (max u v)) (J.over U) J :
  Sheaf (J.over U) (Type (max u v)) ⥤ Sheaf J (Type (max u v)))
