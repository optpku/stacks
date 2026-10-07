module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_14_2_Approximation

/-!
# Approximation by perfect complexes on qcqs algebraic spaces

Every quasi-compact, quasi-separated algebraic space admits approximation by
perfect complexes.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasApproximationByPerfectComplexes

/-- Every quasi-compact, quasi-separated algebraic space admits approximation by
perfect complexes. -/
theorem of_qcqs {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    HasApproximationByPerfectComplexes X := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.AlgebraicSpace
