/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/-!
# Naturality of the projection-formula morphism

The former chapter-local helper is the right-variable naturality of the generic
projection-formula mate.
-/

/- Naturality for an explicitly supplied tensor comparison. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMateOf_natural_right

/- Naturality for the canonical oplax-monoidal tensor comparison. -/
#check @CategoryTheory.Adjunction.leftProjectionFormulaMate_natural_right
