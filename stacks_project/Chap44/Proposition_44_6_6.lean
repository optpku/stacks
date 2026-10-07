module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Curve.Representability
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.RelativePicard

/- Proposition 44.6.6: over a separably closed field, the relative Picard functor of a
smooth projective curve is representable. -/
@[stacks 0B9Z] #check
  (AlgebraicGeometry.RelativePicard.functor_isRepresentable_of_smoothProjectiveCurve :
    ∀ {k : Type u} [Field k] [IsSepClosed k] (X : SchemeOverField k) [Curve X]
      [Smooth X.hom] [Projective X.hom],
      (AlgebraicGeometry.RelativePicard.functor X).obj.IsRepresentable)

end AlgebraicGeometry.RelativePicard
