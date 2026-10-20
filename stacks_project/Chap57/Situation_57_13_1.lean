module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectEmbedding
import StacksCheckRecall

@[expose] public section

universe u

/- Situation 57.13.1 -/
@[stacks 0G08] #check
  (AlgebraicGeometry.SchemeOverField.ProperSmoothPerfectEmbedding :
    ∀ (k : Type u) [Field k], Type (u + 1))
