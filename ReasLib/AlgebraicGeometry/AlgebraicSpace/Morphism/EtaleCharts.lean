module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Scheme morphism properties on étale charts of algebraic spaces

A scheme morphism property lifts to algebraic-space morphisms by requiring it
on every commutative scheme square with representable étale vertical arrows.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces satisfies a scheme morphism property on
étale charts when the top arrow of every commutative scheme square with
representable étale vertical arrows satisfies that property. -/
def onEtaleCharts {S : Scheme.{u}} (P : MorphismProperty Scheme.{u}) :
    MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f ↦
    ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
          a ≫ f = yoneda.map h ≫ b → P h.left

/-- Satisfaction of a scheme morphism property on étale charts is equivalent
to satisfaction on the top arrow of every commutative scheme square with
representable étale vertical arrows. -/
theorem onEtaleCharts_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    onEtaleCharts P f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → P h.left := sorry

end AlgebraicGeometry.AlgebraicSpace
