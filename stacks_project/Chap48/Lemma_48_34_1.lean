module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cohomology.Dimension
import StacksCheckRecall

/-!
# Lemma 48.34.1
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 48.34.1: if cohomology of a coherent module on a variety is nonzero
in degree `d`, then `d` is at most the dimension, and equality forces properness. -/
@[stacks 0G5E]
#check (AlgebraicGeometry.SchemeOverField.cohomologyDegree_le_dimension :
    ∀ {k : Type u} [Field k] (U : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Variety U]
      (F : U.left.Modules) [F.IsCoherent] (d : ℕ),
      ¬ CategoryTheory.Limits.IsZero (AlgebraicGeometry.Scheme.Modules.cohomology F d) →
        d ≤ U.dimension)

#check (AlgebraicGeometry.SchemeOverField.isProper_of_dimension_eq_cohomologyDegree :
    ∀ {k : Type u} [Field k] (U : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Variety U]
      (F : U.left.Modules) [F.IsCoherent] (d : ℕ),
      ¬ CategoryTheory.Limits.IsZero (AlgebraicGeometry.Scheme.Modules.cohomology F d) →
        U.dimension = d → AlgebraicGeometry.IsProper U.hom)
