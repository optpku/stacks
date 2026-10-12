/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Composition
import StacksCheckRecall

/-!
# Lemma 29.35.4

Unramified and G-unramified morphisms are stable under composition.

@stack 02G9
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.35.4 (1): unramified morphisms are stable under composition. -/
@[stacks 02G9] #check
  (AlgebraicGeometry.unramified_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      [AlgebraicGeometry.Unramified f] [AlgebraicGeometry.Unramified g],
      AlgebraicGeometry.Unramified (f ≫ g))

/- Lemma 29.35.4 (2): G-unramified morphisms are stable under composition. -/
@[stacks 02G9] #check
  (AlgebraicGeometry.gUnramified_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      [AlgebraicGeometry.GUnramified f] [AlgebraicGeometry.GUnramified g],
      AlgebraicGeometry.GUnramified (f ≫ g))
