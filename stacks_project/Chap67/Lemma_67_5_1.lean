module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
import StacksCheckRecall

/-!
# Representable surjective morphisms of algebraic spaces

A representable morphism of algebraic spaces is surjective in the
sense of Section 67.3 if and only if the induced map of associated
point spaces is surjective.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.5.1: A representable morphism of algebraic spaces has surjective
represented scheme base changes if and only if its induced map on points is
surjective. -/
@[stacks 03MD] #check
  (@AlgebraicGeometry.AlgebraicSpace.surjective_presheaf_iff_map_surjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} {f : X ⟶ Y},
      CategoryTheory.yoneda.relativelyRepresentable f →
        ((CategoryTheory.MorphismProperty.over (@AlgebraicGeometry.Surjective :
          CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})).presheaf f ↔
          Function.Surjective (AlgebraicGeometry.AlgebraicSpace.Points.map f)))
