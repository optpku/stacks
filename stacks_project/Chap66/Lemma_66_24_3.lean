module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Noetherian
import StacksCheckRecall

/-!
# Points of Noetherian algebraic spaces

The space of points of a Noetherian algebraic space is a sober Noetherian topological space.
-/

universe u

/- Lemma 66.24.3: the point space of a Noetherian algebraic space is sober and Noetherian. -/
@[stacks 04ZG] #check
  (AlgebraicGeometry.AlgebraicSpace.IsNoetherian.sober_noetherian :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian X],
      T0Space (AlgebraicGeometry.AlgebraicSpace.Points X) ∧
        QuasiSober (AlgebraicGeometry.AlgebraicSpace.Points X) ∧
          TopologicalSpace.NoetherianSpace (AlgebraicGeometry.AlgebraicSpace.Points X))
