module

public import ReasLib.Topology.Counterexamples.DiscreteTwoPoint.Basic
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf counterexample for the discrete two-point collapse

The finite-colimit criterion used by this example is mathlib's
`preservesFiniteColimits_of_preservesInitial_and_pushouts`; this module only
owns the concrete pushforward and its two non-preservation statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace TopCat.Counterexample.DiscreteTwoPoint

/-- Direct image of type-valued sheaves along the discrete two-point collapse. -/
noncomputable def pushforward : space.Sheaf Type ⥤ point.Sheaf Type :=
  TopCat.Sheaf.pushforward Type collapse

/-- Example 7.41.3 (1) (04D8): direct image along the discrete two-point
collapse does not preserve coequalizers. -/
@[stacks 04D8 "(1)"]
theorem not_preservesCoequalizers :
    ¬ PreservesColimitsOfShape WalkingParallelPair pushforward := sorry

/-- Example 7.41.3 (2) (04D8): direct image along the discrete two-point
collapse does not preserve pushouts. -/
@[stacks 04D8 "(2)"]
theorem not_preservesPushouts :
    ¬ PreservesColimitsOfShape WalkingSpan pushforward := sorry

end TopCat.Counterexample.DiscreteTwoPoint
