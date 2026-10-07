module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCheckRecall

/-!
# Lemma 29.42.1: Valuative criterion for properness

For a finite type, quasi-separated morphism, properness is equivalent to the valuative criterion.

@stack 0BX5
-/

@[expose] public section

/- Lemma 29.42.1 (Valuative criterion for properness)

For a finite type, quasi-separated morphism, properness is equivalent to the
valuative criterion.
-/
@[stacks 0BX5] #check
  (AlgebraicGeometry.IsProper.eq_valuativeCriterion :
    @AlgebraicGeometry.IsProper =
      AlgebraicGeometry.ValuativeCriterion ⊓
        @AlgebraicGeometry.QuasiCompact ⊓
          @AlgebraicGeometry.QuasiSeparated ⊓
            @AlgebraicGeometry.LocallyOfFiniteType)
