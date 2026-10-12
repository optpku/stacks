/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.HomBifunctor.OfEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Representatives

/-!
# Functoriality of the right-fraction Hom-colimit

The source-denominator colimit formula is natural contravariantly in its source and covariantly
in its target.  This file packages both actions as a bifunctor and records compatibility with
every localization model.
-/

@[expose] public section

universe u v uD vD

namespace CategoryTheory.MorphismProperty.RightFraction.Localization

open Limits Opposite

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-- Postcompose a numerator in the source-denominator diagram.  The helper keeps the universe and
opposite-category transports out of the public coprojection formula. -/
def homDiagram.postcompose {X Y Y' : C} (g : Y ⟶ Y')
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (x : (homDiagram W X Y).obj s) :
    (homDiagram W X Y').obj s :=
  ULift.up (x.down ≫ g)

/-- The underlying numerator of `homDiagram.postcompose` is ordinary postcomposition. -/
@[simp]
theorem homDiagram.postcompose_down {X Y Y' : C} (g : Y ⟶ Y')
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (x : (homDiagram W X Y).obj s) :
    (homDiagram.postcompose W g s x).down = x.down ≫ g := sorry

/-- Postcomposition of a source-denominator numerator by an identity is the identity. -/
@[simp]
theorem homDiagram.postcompose_id {X Y : C} (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ)
    (x : (homDiagram W X Y).obj s) :
    homDiagram.postcompose W (𝟙 Y) s x = x := sorry

/-- Successive postcomposition of source-denominator numerators agrees with composition. -/
theorem homDiagram.postcompose_comp {X Y Y' Y'' : C} (g : Y ⟶ Y') (h : Y' ⟶ Y'')
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (x : (homDiagram W X Y).obj s) :
    homDiagram.postcompose W (g ≫ h) s x =
      homDiagram.postcompose W h s (homDiagram.postcompose W g s x) := sorry

variable [W.HasRightCalculusOfFractions]

/-- The source-denominator Hom-colimits as a bifunctor on `Cᵒᵖ × C`. -/
noncomputable def homColimit.bifunctor : Cᵒᵖ × C ⥤ Type (max u v) :=
  Functor.HomBifunctor.ofEquiv (Q W)
    (fun X Y ↦ (colimit (homDiagram W X Y) : Type (max u v)))
    (homColimit.equiv W)

/-- The Hom-colimit bifunctor is naturally isomorphic to the Hom bifunctor of the canonical
right-fraction localization. -/
noncomputable def homColimit.bifunctor.iso :
    homColimit.bifunctor W ≅
      Functor.prod (Q W).op (Q W) ⋙ Functor.hom (RightFraction.Localization W) :=
  Functor.HomBifunctor.ofEquivIso (Q W)
    (fun X Y ↦ (colimit (homDiagram W X Y) : Type (max u v)))
    (homColimit.equiv W)

/-- The value of the Hom-colimit bifunctor is the expected source-denominator colimit. -/
@[simp]
theorem homColimit.bifunctor.obj (p : Cᵒᵖ × C) :
    (homColimit.bifunctor W).obj p =
      (colimit (homDiagram W p.1.unop p.2) : Type (max u v)) := sorry

/-- A morphism in `Cᵒᵖ × C` acts by precomposition and postcomposition after applying the
canonical Hom-colimit equivalence. -/
@[simp]
theorem homColimit.bifunctor.map
    {p q : Cᵒᵖ × C} (f : p ⟶ q)
    (x : colimit (homDiagram W p.1.unop p.2)) :
    (homColimit.bifunctor W).map f x =
      (homColimit.equiv W q.1.unop q.2).symm
        ((Q W).map f.1.unop ≫ homColimit.equiv W p.1.unop p.2 x ≫
          (Q W).map f.2) := sorry

/-- The Hom-colimit bifunctor acts contravariantly in the source by precomposition. -/
@[simp]
theorem homColimit.bifunctor.map_left
    {X X' Y : C} (f : X' ⟶ X) (x : colimit (homDiagram W X Y)) :
    (homColimit.bifunctor W).map
        ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y)) x =
      (homColimit.equiv W X' Y).symm
        ((Q W).map f ≫ homColimit.equiv W X Y x) := sorry

/-- The Hom-colimit bifunctor acts covariantly in the target by postcomposition. -/
@[simp]
theorem homColimit.bifunctor.map_right
    {X Y Y' : C} (g : Y ⟶ Y') (x : colimit (homDiagram W X Y)) :
    (homColimit.bifunctor W).map
        ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y')) x =
      (homColimit.equiv W X Y').symm
        (homColimit.equiv W X Y x ≫ (Q W).map g) := sorry

/-- Covariant target action sends a source-denominator coprojection to the same denominator with
its numerator postcomposed. -/
@[simp]
theorem homColimit.bifunctor.map_right_ι
    {X Y Y' : C} (g : Y ⟶ Y') (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ)
    (x : (homDiagram W X Y).obj s) :
    (homColimit.bifunctor W).map
        ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y'))
        (colimit.ι (homDiagram W X Y) s x) =
      colimit.ι (homDiagram W X Y') s (homDiagram.postcompose W g s x) := sorry

/-- The canonical Hom-colimit equivalence is natural in both variables. -/
theorem homColimit.equiv.map
    {p q : Cᵒᵖ × C} (f : p ⟶ q)
    (x : colimit (homDiagram W p.1.unop p.2)) :
    homColimit.equiv W q.1.unop q.2 ((homColimit.bifunctor W).map f x) =
      (Q W).map f.1.unop ≫ homColimit.equiv W p.1.unop p.2 x ≫
        (Q W).map f.2 := sorry

/-- Source naturality of the canonical Hom-colimit equivalence. -/
theorem homColimit.equiv.map_left
    {X X' Y : C} (f : X' ⟶ X) (x : colimit (homDiagram W X Y)) :
    homColimit.equiv W X' Y
        ((homColimit.bifunctor W).map
          ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y)) x) =
      (Q W).map f ≫ homColimit.equiv W X Y x := sorry

/-- Target naturality of the canonical Hom-colimit equivalence. -/
theorem homColimit.equiv.map_right
    {X Y Y' : C} (g : Y ⟶ Y') (x : colimit (homDiagram W X Y)) :
    homColimit.equiv W X Y'
        ((homColimit.bifunctor W).map
          ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y')) x) =
      homColimit.equiv W X Y x ≫ (Q W).map g := sorry

/-- The forward component of the bifunctor comparison is the canonical Hom-colimit
equivalence. -/
@[simp]
theorem homColimit.bifunctor.iso.hom.app_apply
    (p : Cᵒᵖ × C) (x : colimit (homDiagram W p.1.unop p.2)) :
    (homColimit.bifunctor.iso W).hom.app p x =
      homColimit.equiv W p.1.unop p.2 x := sorry

/-- The inverse component of the bifunctor comparison is the inverse canonical Hom-colimit
equivalence. -/
@[simp]
theorem homColimit.bifunctor.iso.inv.app_apply
    (p : Cᵒᵖ × C) (f : (Q W).obj p.1.unop ⟶ (Q W).obj p.2) :
    (homColimit.bifunctor.iso W).inv.app p f =
      (homColimit.equiv W p.1.unop p.2).symm f := sorry

variable {D : Type uD} [Category.{vD} D]

/-- The Hom-colimit action is compatible with precomposition and postcomposition in every
localization model. -/
theorem homColimit.equivTo.map
    (L : C ⥤ D) [L.IsLocalization W]
    {p q : Cᵒᵖ × C} (f : p ⟶ q)
    (x : colimit (homDiagram W p.1.unop p.2)) :
    homColimit.equivTo L W q.1.unop q.2
        ((homColimit.bifunctor W).map f x) =
      L.map f.1.unop ≫ homColimit.equivTo L W p.1.unop p.2 x ≫ L.map f.2 := sorry

/-- Naturality of the Hom-colimit equivalence under precomposition. -/
theorem homColimit.equivTo.map_left
    (L : C ⥤ D) [L.IsLocalization W]
    {X X' Y : C} (f : X' ⟶ X) (x : colimit (homDiagram W X Y)) :
    homColimit.equivTo L W X' Y
        ((homColimit.bifunctor W).map
          ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y)) x) =
      L.map f ≫ homColimit.equivTo L W X Y x := sorry

/-- Naturality of the Hom-colimit equivalence under postcomposition. -/
theorem homColimit.equivTo.map_right
    (L : C ⥤ D) [L.IsLocalization W]
    {X Y Y' : C} (g : Y ⟶ Y') (x : colimit (homDiagram W X Y)) :
    homColimit.equivTo L W X Y'
        ((homColimit.bifunctor W).map
          ((𝟙 (Opposite.op X), g) : (Opposite.op X, Y) ⟶ (Opposite.op X, Y')) x) =
      homColimit.equivTo L W X Y x ≫ L.map g := sorry

end CategoryTheory.MorphismProperty.RightFraction.Localization
