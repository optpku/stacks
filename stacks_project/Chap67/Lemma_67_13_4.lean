module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ClosedImmersion
import StacksCheckRecall

/-!
# Closed immersions of algebraic spaces are separated

A closed immersion of algebraic spaces over a scheme `S` is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.13.4: A closed immersion of algebraic spaces is separated. -/
@[stacks 04CH] #check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.separated :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion f] →
      AlgebraicGeometry.AlgebraicSpace.Separated f)
