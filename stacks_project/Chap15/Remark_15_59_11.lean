/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Generation
import StacksCheckRecall

@[expose] public section

/-!
# Split filtered models of derived modules

Remark 15.59.11 is owned by the reusable generation API for derived modules.

@stack 09PB
-/

/- The regular module in degree zero is the generating object used below. -/
#check @CategoryTheory.ModuleCat.ringSingle

/- Remark 15.59.11 (1): every cochain complex has the specified exhaustive split filtered
model with graded pieces built from shifts of `R[0]`. -/
@[stacks 09PB "Remark 15.59.11 (1)"]
#check @CategoryTheory.ModuleCat.exists_splitFilteredModel

/- Remark 15.59.11 (2): the filtered model gives the displayed homotopy-colimit distinguished
triangle with coproducts of shifts of `R[0]`. -/
@[stacks 09PB "Remark 15.59.11 (2), homotopy-colimit distinguished triangle"]
#check @CategoryTheory.ModuleCat.ringSingleResolution_nonempty

/- Remark 15.59.11 (3): coproduct- and triangle-stable properties that hold on the shifts of
`R[0]` hold on every derived module. -/
@[stacks 09PB "Remark 15.59.11 (3)"]
#check @CategoryTheory.ModuleCat.allDerivedObjects_of_coproducts_triangles_ringShifts

/- Weak generation is a reusable corollary of the three source clauses. -/
#check @CategoryTheory.ModuleCat.ringSingle_isWeakGenerator
