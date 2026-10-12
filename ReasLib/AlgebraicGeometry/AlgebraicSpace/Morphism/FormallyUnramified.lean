/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyUnramified.Composition

/-!
# Formally unramified morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme is formally unramified when its
transformation of functors of points is formally unramified. This property is
stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is formally unramified if it is formally
unramified as a transformation of functors of points. -/
class FormallyUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is formally unramified as a transformation of functors. -/
  ofFunctor : Scheme.Over.FormallyUnramified f

/-- A morphism of algebraic spaces is formally unramified if and only if it is
formally unramified as a transformation of functors of points. -/
theorem formallyUnramified_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyUnramified f ↔ Scheme.Over.FormallyUnramified f := sorry

namespace FormallyUnramified

/-- A morphism of algebraic spaces that is formally unramified as a
transformation of functors of points is formally unramified. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.FormallyUnramified f) : FormallyUnramified f := sorry

/-- A formally unramified morphism of algebraic spaces is formally unramified as
a transformation of functors of points. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] : Scheme.Over.FormallyUnramified f := sorry

/-- The identity morphism of an algebraic space is formally unramified. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FormallyUnramified (𝟙 X) := sorry

/-- A formally unramified morphism of algebraic spaces yields a formally
unramified transformation of functors of points. -/
instance toSchemeOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] : Scheme.Over.FormallyUnramified f := sorry

/-- The composite of two formally unramified morphisms of algebraic spaces is
formally unramified. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyUnramified f] [FormallyUnramified g] :
    FormallyUnramified (f ≫ g) := sorry

/-- Formally unramified morphisms of algebraic spaces are stable under
composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)) := sorry

end FormallyUnramified

end AlgebraicGeometry.AlgebraicSpace
