/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal.CohomologyDiagram
import StacksCheckRecall

/-!
# Lemma 15.94.6 (0H32)

The canonical objects and the reusable comparison-diagram structure are owned by
`ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Principal.CohomologyDiagram`.
This chapter entry directly recalls the shared comparison-diagram owner.

@stack 0H32
-/

@[expose] public section

/- Lemma 15.94.6 (0H32): ordinary principal-adic completion of cohomology and cohomology of
principal derived completion fit into the canonical comparison diagram. -/
@[stacks 0H32]
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.existsComparison

#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison.topRow
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison.middleRow
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison.leftColumn
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison.middleColumn
#check @CategoryTheory.DerivedCategory.PrincipalPower.CohomologyDiagram.Comparison.spec
