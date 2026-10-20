/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Surjective
import StacksCheckRecall

/-!
# Points-map characterization of surjective representable morphisms

A morphism of algebraic stacks representable by algebraic spaces is surjective
in the sense of Section 100.3 if and only if the induced map of points is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

/- Lemma 100.4.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `Points.map f : Points X → Points Y` is
surjective if and only if `f` is surjective in the sense of Section 100.3. -/
@[stacks 04XI] #check (AlgebraicGeometry.Groupoids.Hom.Surjective.iff_map :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
      (Groupoids.Hom.Surjective f ↔ Function.Surjective (AlgebraicStack.Points.map f)))

/- If a morphism of algebraic stacks representable by algebraic spaces induces a
surjective map of points, then it is surjective in the sense of Section 100.3. -/
#check (AlgebraicGeometry.Groupoids.Hom.Surjective.of_map :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
      Function.Surjective (AlgebraicStack.Points.map f) → Groupoids.Hom.Surjective f)

/- A 1-morphism of algebraic stacks which is surjective in the sense of
Section 100.3 induces a surjective map of points. -/
#check (AlgebraicGeometry.Groupoids.Hom.Surjective.map_surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Surjective f],
    Function.Surjective (AlgebraicStack.Points.map f))

/- A morphism of algebraic stacks representable by algebraic spaces has the
algebraic-space surjectivity property on scheme-slice representing morphisms if
and only if the induced map of points is surjective. -/
#check (AlgebraicGeometry.Groupoids.Hom.Surjective.has_iff_map :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
    relativelyRepresentableByAlgebraicSpaces f →
      (Groupoids.Hom.has (@AlgebraicSpace.Surjective S) f ↔
        Function.Surjective (AlgebraicStack.Points.map f)))
