/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.HomBifunctor.OfEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Representatives

/-!
# Functoriality of the left-fraction Hom-colimit

The target-denominator colimit formula is natural contravariantly in its source and covariantly
in its target.  This file packages the two actions as a mathlib-style bifunctor and records
compatibility with every localization model.
-/

@[expose] public section

universe u v uD vD

namespace CategoryTheory.MorphismProperty.LeftFraction.Localization

open Limits Opposite

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-- Precompose a numerator in the target-denominator diagram.  The helper keeps the universe and
opposite-category transports out of the public coprojection formula. -/
def homDiagram.precompose {X X' Y : C} (f : X' ⟶ X)
    (s : MorphismProperty.Under W ⊤ Y) (x : (homDiagram W X Y).obj s) :
    (homDiagram W X' Y).obj s :=
  ULift.up (f ≫ x.down)

/-- The underlying numerator of `homDiagram.precompose` is ordinary precomposition. -/
@[simp]
theorem homDiagram.precompose_down {X X' Y : C} (f : X' ⟶ X)
    (s : MorphismProperty.Under W ⊤ Y) (x : (homDiagram W X Y).obj s) :
    (homDiagram.precompose W f s x).down = f ≫ x.down := sorry

/-- Precomposition of a target-denominator numerator by an identity is the identity. -/
@[simp]
theorem homDiagram.precompose_id {X Y : C} (s : MorphismProperty.Under W ⊤ Y)
    (x : (homDiagram W X Y).obj s) :
    homDiagram.precompose W (𝟙 X) s x = x := sorry

/-- Successive precomposition of target-denominator numerators agrees with composition. -/
theorem homDiagram.precompose_comp {X X' X'' Y : C} (f : X' ⟶ X) (g : X'' ⟶ X')
    (s : MorphismProperty.Under W ⊤ Y) (x : (homDiagram W X Y).obj s) :
    homDiagram.precompose W (g ≫ f) s x =
      homDiagram.precompose W g s (homDiagram.precompose W f s x) := sorry

variable [W.HasLeftCalculusOfFractions]

/-- The target-denominator Hom-colimits as a bifunctor on `Cᵒᵖ × C`. -/
noncomputable def homColimit.bifunctor : Cᵒᵖ × C ⥤ Type (max u v) :=
  Functor.HomBifunctor.ofEquiv (Q W)
    (fun X Y ↦ (colimit (homDiagram W X Y) : Type (max u v)))
    (homColimit.equiv W)

/-- The Hom-colimit bifunctor is naturally isomorphic to the Hom bifunctor of the canonical
left-fraction localization. -/
noncomputable def homColimit.bifunctor.iso :
    homColimit.bifunctor W ≅
      Functor.prod (Q W).op (Q W) ⋙ Functor.hom (LeftFraction.Localization W) :=
  Functor.HomBifunctor.ofEquivIso (Q W)
    (fun X Y ↦ (colimit (homDiagram W X Y) : Type (max u v)))
    (homColimit.equiv W)

/-- The value of the Hom-colimit bifunctor is the expected target-denominator colimit. -/
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

/-- Contravariant source action sends a target-denominator coprojection to the same denominator
with its numerator precomposed. -/
@[simp]
theorem homColimit.bifunctor.map_left_ι
    {X X' Y : C} (f : X' ⟶ X) (s : MorphismProperty.Under W ⊤ Y)
    (x : (homDiagram W X Y).obj s) :
    (homColimit.bifunctor W).map
        ((f.op, 𝟙 Y) : (Opposite.op X, Y) ⟶ (Opposite.op X', Y))
        (colimit.ι (homDiagram W X Y) s x) =
      colimit.ι (homDiagram W X' Y) s (homDiagram.precompose W f s x) := sorry

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

end CategoryTheory.MorphismProperty.LeftFraction.Localization
