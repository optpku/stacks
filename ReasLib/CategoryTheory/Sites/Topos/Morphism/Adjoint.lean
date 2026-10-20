module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Embedding
public import ReasLib.CategoryTheory.Sites.EnoughObjects.Presentation

/-!
# Adjoint criteria for morphisms of topoi

The local corepresentability of inverse-image section functors can be promoted
along a covering family of generators to a global left adjoint of inverse image.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe uC uD vC vD

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasWeakSheafify J (Type (max uD vD))]
variable [HasWeakSheafify K (Type (max uD vD))]

/-- The inverse-image sections of `f` are corepresentable on each object selected by `E`. -/
def hasCorepresentableSectionsOn (f : MorphismOfTopoiIn J K) (E : ObjectProperty D) : Prop :=
  ∀ V : D, E V →
    (f.inverseImage ⋙ (sheafSections K (Type (max uD vD))).obj (op V)).IsCorepresentable

/-- Unfold the local corepresentability condition for inverse-image sections. -/
theorem hasCorepresentableSectionsOn_iff (f : MorphismOfTopoiIn J K) (E : ObjectProperty D) :
    f.hasCorepresentableSectionsOn E ↔
      ∀ V : D, E V →
        (f.inverseImage ⋙ (sheafSections K (Type (max uD vD))).obj (op V)).IsCorepresentable := sorry

/-- Local corepresentability of inverse-image sections on a covering family implies that the
inverse-image functor has a left adjoint. -/
theorem isRightAdjoint_of_corepresentableSections
    (f : MorphismOfTopoiIn J K) {E : ObjectProperty D}
    (hsections : f.hasCorepresentableSectionsOn E)
    (hcover : K.HasEnoughObjectsWithProperty E) :
    f.inverseImage.IsRightAdjoint := sorry

end CategoryTheory.MorphismOfTopoiIn
