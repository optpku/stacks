module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Perfect.Flat
import StacksCheckRecall

/-!
# Flat perfect morphisms of algebraic spaces

A morphism of algebraic spaces is flat and perfect if and only if it is flat
and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 76.47.4: A morphism of algebraic spaces over a scheme is flat and
perfect if and only if it is flat and locally of finite presentation. -/
@[stacks 06C2] #check
  (AlgebraicGeometry.AlgebraicSpace.flat_and_perfect_iff_flat_and_locallyOfFinitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      (AlgebraicGeometry.AlgebraicSpace.onEtaleCharts (@AlgebraicGeometry.Flat) f ∧
          AlgebraicGeometry.AlgebraicSpace.onEtaleCharts
            (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) f) ↔
        (AlgebraicGeometry.AlgebraicSpace.onEtaleCharts (@AlgebraicGeometry.Flat) f ∧
          AlgebraicGeometry.AlgebraicSpace.onEtaleCharts
            (@AlgebraicGeometry.LocallyOfFinitePresentation) f))
