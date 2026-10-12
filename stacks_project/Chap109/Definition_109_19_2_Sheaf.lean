/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Relative dualizing sheaf of a Cohen–Macaulay family of curves

For a family of curves with Cohen–Macaulay fibres equidimensional of dimension
1, the relative dualizing sheaf is the degree `-1` cohomology sheaf of a
chosen relative dualizing complex.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- The relative dualizing sheaf of a Cohen–Macaulay family of curves of
relative dimension 1, as the degree `-1` cohomology sheaf of a chosen
relative dualizing complex. -/
noncomputable def sheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) : X.Modules :=
  cohomologySheaf C.complex (-1)

/-- The relative dualizing sheaf is the degree `-1` cohomology sheaf of the
chosen relative dualizing complex. -/
theorem sheaf_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    sheaf C = cohomologySheaf C.complex (-1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

