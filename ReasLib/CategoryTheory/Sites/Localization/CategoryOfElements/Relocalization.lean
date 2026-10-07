module

public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relocalization between categories of elements

A morphism `s : G ⟶ F` of set-valued sheaves induces a functor from the
opposite category of elements of `G` to that of `F`.  This module owns that
functor, its strict compatibility with the two localization projections, and
the resulting morphism of topoi.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G F : Sheaf J (Type v)} (s : G ⟶ F)

/-- Lemma 18.21.4 (04J4): the functor between category-of-elements
localization sites induced by `s : G ⟶ F`. -/
@[stacks 04J4 "site functor"]
abbrev relocalizationFunctor : G.obj.Elementsᵒᵖ ⥤ F.obj.Elementsᵒᵖ :=
  (CategoryOfElements.map s.hom).op

/-- The category-of-elements relocalization functor commutes strictly with
the projections to the ambient site. -/
theorem relocalizationFunctor_comp_projection :
    relocalizationFunctor s ⋙ localizationProjection F =
      localizationProjection G := sorry

/-- The canonical isomorphism expressing compatibility of relocalization
with the two category-of-elements projections. -/
@[stacks 04J4 "projection comparison"]
noncomputable def relocalizationProjectionIso :
    relocalizationFunctor s ⋙ localizationProjection F ≅
      localizationProjection G :=
  Iso.refl _

/-- The category-of-elements relocalization functor is continuous. -/
instance relocalizationFunctor_isContinuous :
    Functor.IsContinuous (relocalizationFunctor s)
      (localizationTopology G) (localizationTopology F) := sorry

/-- The category-of-elements relocalization functor is cocontinuous. -/
instance relocalizationFunctor_isCocontinuous :
    Functor.IsCocontinuous (relocalizationFunctor s)
      (localizationTopology G) (localizationTopology F) := sorry

/-- Lemma 18.21.4 (04J4): the morphism of topoi presented by
category-of-elements relocalization. -/
@[stacks 04J4 "topos morphism"]
noncomputable def relocalizationMorphismOfTopoiIn
    [∀ P : G.obj.Elementsᵒᵖᵒᵖ ⥤ Type (max u v),
      (relocalizationFunctor s).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn (localizationTopology F) (localizationTopology G) :=
  (relocalizationFunctor s).morphismOfTopoiInOfCocontinuous
    (localizationTopology G) (localizationTopology F)

end CategoryTheory.Sheaf.Localization
