module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Projection formulas and base change on ringed sites

The ringed-site diagram is the specialization of the generic monoidal compatibility square in
`ReasLib`.
-/

/- Remark 21.50.2: the morphism of 21.50.0.1 is compatible with specified derived base-change
maps in a commutative square of ringed topoi. -/
@[stacks 0E48]
#check @CategoryTheory.leftProjectionFormulaMate_baseChange_commSq_of_isDerivedBaseChangeMap

/- Canonical form using the base-change mates determined by the adjunction square. -/
#check @CategoryTheory.leftProjectionFormulaMate_baseChange_commSq
