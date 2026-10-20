module

public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Local
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.10.7: a point of a locally Noetherian scheme has local topological Krull dimension
zero if and only if its singleton is open. -/
@[stacks 0H7C] #check
  (AlgebraicGeometry.Scheme.topologicalKrullDimAt_eq_zero_iff_isOpen_singleton :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] {x : X},
      topologicalKrullDimAt x = 0 ↔ IsOpen ({x} : Set X))
