module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.UniversallyOpen
import StacksCheckRecall

/-!
# Flat morphisms locally of finite presentation are universally open

A flat morphism of algebraic spaces that is locally of finite presentation is
universally open.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.30.6: A flat morphism locally of finite presentation of algebraic
spaces is universally open. -/
@[stacks 042S] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.of_flat :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f],
      AlgebraicGeometry.AlgebraicSpace.UniversallyOpen f)
