module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Filtration
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.57.2: Every quasi-compact quasi-separated algebraic space admits a
finite closed filtration of finite presentation, beginning with a thickening
and ending empty, with admissible resolution blowups of successive differences. -/
@[stacks 0GV6] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteClosedResolutionBlowupFiltration :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X], Nonempty (FiniteClosedResolutionBlowupFiltration X))
